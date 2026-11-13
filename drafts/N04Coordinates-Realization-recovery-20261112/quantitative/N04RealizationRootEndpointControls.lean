import ContinuousFlexibility.Analysis.N04RealizationRootHeightEnvelopes

/-!
# Select material-controlled finite endpoint constants before transport

The finite prefix is chosen on one common neighborhood. The numerical
constants are uniform over states, roots, angles and actual host cells.
The resulting radius, coordinate and height bounds are explicit powers
of that host sample, before any positive transport is constructed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

def N04RealizationRootEndpointControls
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (n base : ℕ) (ε K₀ C0 B A : ℝ) : Prop :=
  ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
    (∀ x ∈ Ioo (C.left m) (C.right m),
      K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) * min (x - C.left m) (C.right m - x) ≤
        -deriv D.w x / (x * D.w x)) →
    ∀ side : Bool, ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      let M : ℝ := 1 + B * (C0 * T.E0 (T.sample j)) ^ A
      let i : ℕ := if side then (K.cutPair m).2 else (K.cutPair m).1
      RootEndpointJetBounds n (canonicalCurrentPoint C K z i)
        (n04CoordinatesCurrentHeightRatio C K z i)
        (n01ComponentRoot C m side) M⁻¹ M M

theorem n04Realization_exists_rootEndpoint_material_controls
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε K₀ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hK₀ : 0 < K₀) (n : ℕ) :
    ∃ C0 B A : ℝ, ∃ newBase : ℕ, ∃ η : ℝ,
      1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      0 < B ∧ 0 < A ∧ base ≤ newBase ∧ 0 < η ∧ η ≤ ε ∧
      N04RealizationRootEndpointControls D T S C K n newBase η K₀ C0 B A := by
  classical
  obtain ⟨C0, P, newBase, η, hC0, hfloor, hP, hb, hη, hηε, hraw⟩ :=
    n04Realization_rootMaterial_finite_prefix hS hT hN hfield hA hB hK₀ (n + 2)
  have hA' := n04PartA_restrict hA hb hηε
  have hB' := n04PartB_restrict hB hb hηε
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C newBase η :=
    reference_mem_stateNeighborhood S C newBase hη
  have hsref : stateSector S C.referenceState := n04b_referenceState_sector hN.1.1.2.2.1
  let V : Type := {v : (AnnularState S × ℝ) × (ℕ × ℕ × Bool) //
    v.1 ∈ stateNeighborhood S C newBase η ∧ stateSector S v.1.1 ∧
      Ioo (C.left v.2.1) (C.right v.2.1) ⊆ D.cells v.2.2.1 ∧
      ∀ r ∈ Ioo (C.left v.2.1) (C.right v.2.1),
        K₀⁻¹ * T.E0 (T.sample v.2.2.1) ^ (-K₀) *
          min (r - C.left v.2.1) (C.right v.2.1 - r) ≤ -deriv D.w r / (r * D.w r)}
  let X : Type := V × ℝ
  let z : X → AnnularState S × ℝ := fun x => x.1.val.1
  let m : X → ℕ := fun x => x.1.val.2.1
  let j : X → ℕ := fun x => x.1.val.2.2.1
  let side : X → Bool := fun x => x.1.val.2.2.2
  let θ : X → ℝ := fun x => x.2
  let i : X → ℕ := fun x =>
    if side x then (K.cutPair (m x)).2 else (K.cutPair (m x)).1
  let p : X → PolarPoint := fun x => (n01ComponentRoot C (m x) (side x), θ x)
  let W : X → ℝ := fun x => C0 * T.E0 (T.sample (j x))
  let F : Bool → X → PolarPoint → PolarPoint := fun b x =>
    if b then canonicalReferencePoint C K (z x) (i x)
    else canonicalCurrentPoint C K (z x) (i x)
  let H : Bool → X → PolarPoint → ℝ := fun b x q =>
    n04CoordinatesCurrentHeightRatio C K (z x) (i x) q ^
      (if b then (-1 : ℝ) else 1)
  have hz (x : X) : z x ∈ stateNeighborhood S C newBase η := x.1.property.1
  have hs (x : X) : stateSector S (z x).1 := x.1.property.2.1
  have hhost (x : X) : Ioo (C.left (m x)) (C.right (m x)) ⊆ D.cells (j x) :=
    x.1.property.2.2.1
  have hopt (x : X) : ∀ r ∈ Ioo (C.left (m x)) (C.right (m x)),
      K₀⁻¹ * T.E0 (T.sample (j x)) ^ (-K₀) *
        min (r - C.left (m x)) (C.right (m x) - r) ≤
          -deriv D.w r / (r * D.w r) := x.1.property.2.2.2
  have hW (x : X) : 1 ≤ W x := hfloor (j x)
  have hF (b : Bool) (k : ℕ) (hk : 0 < k) (hkn : k ≤ n + 2) :
      HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ k (F b x) (p x)‖) := by
    cases b
    · exact n04Realization_rootBetween_material_envelope hA' hB'.1 hP hfloor hraw
        (fun _ => (C.referenceState, 0)) z m j side θ
        (fun _ => href) (fun _ => hsref) hz hs hhost hopt hk hkn
    · exact n04Realization_rootBetween_material_envelope hA' hB'.1 hP hfloor hraw
        z (fun _ => (C.referenceState, 0)) m j side θ
        hz hs (fun _ => href) (fun _ => hsref) hhost hopt hk hkn
  have hH (b : Bool) (k : ℕ) (hkn : k ≤ n + 2) :
      HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ k (H b x) (p x)‖) :=
    n04Realization_rootHeight_material_envelope hA' hB'.1 hP hfloor hraw
      href hsref z m j side θ hz hs hhost hopt b hkn
  let J : Type := (Bool × Fin (n + 2)) ⊕ (Bool × Fin (n + 1))
  let Q : J → X → ℝ := fun t x => match t with
    | .inl a => ‖iteratedFDeriv ℝ (a.2.val + 1) (F a.1 x) (p x)‖
    | .inr a => ‖iteratedFDeriv ℝ a.2.val (H a.1 x) (p x)‖
  have hQ₀ (t : J) (x : X) : 0 ≤ Q t x := by cases t <;> exact norm_nonneg _
  have hQ (t : J) : HasPositiveEnvelope W (Q t) := by
    cases t with
    | inl a => exact hF a.1 (a.2.val + 1) (by omega) (by omega)
    | inr a => exact hH a.1 a.2.val (by omega)
  obtain ⟨B, A, hBpos, hApos, hbound⟩ :=
    n04Realization_envelope_finite_uniform hW Q hQ₀ hQ
  refine ⟨C0, B, A, newBase, η, hC0, hfloor, hBpos, hApos, hb, hη, hηε, ?_⟩
  intro m₀ j₀ hhost₀ hopt₀ side₀ z₀ hz₀ hs₀
  let a : V := ⟨(z₀, m₀, j₀, side₀), hz₀, hs₀, hhost₀, hopt₀⟩
  let M : ℝ := 1 + B * (C0 * T.E0 (T.sample j₀)) ^ A
  let k₀ : ℕ := if side₀ then (K.cutPair m₀).2 else (K.cutPair m₀).1
  let r₀ : ℝ := n01ComponentRoot C m₀ side₀
  have hM : 1 ≤ M := le_add_of_nonneg_right
    (mul_nonneg hBpos.le (Real.rpow_nonneg (zero_le_one.trans (hfloor j₀)) _))
  have hcoordinate (b : Bool) (t : ℝ) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 2) :
      ‖iteratedFDeriv ℝ k (F b (a, t)) (r₀, t)‖ ≤ M := by
    let f : Fin (n + 2) := ⟨k - 1, by omega⟩
    have h := hbound (a, t) (.inl (b, f))
    change ‖iteratedFDeriv ℝ ((k - 1) + 1) (F b (a, t)) (r₀, t)‖ ≤
      B * (C0 * T.E0 (T.sample j₀)) ^ A at h
    have h' : ‖iteratedFDeriv ℝ k (F b (a, t)) (r₀, t)‖ ≤
        B * (C0 * T.E0 (T.sample j₀)) ^ A := by
      simpa only [Nat.sub_add_cancel hk] using h
    exact h'.trans (le_add_of_nonneg_left zero_le_one)
  have hheight (b : Bool) (t : ℝ) (k : ℕ) (hkn : k ≤ n) :
      ‖iteratedFDeriv ℝ k (H b (a, t)) (r₀, t)‖ ≤ M := by
    let f : Fin (n + 1) := ⟨k, by omega⟩
    have h := hbound (a, t) (.inr (b, f))
    change ‖iteratedFDeriv ℝ k (H b (a, t)) (r₀, t)‖ ≤
      B * (C0 * T.E0 (T.sample j₀)) ^ A at h
    exact h.trans (le_add_of_nonneg_left zero_le_one)
  have hdiagonal (t : ℝ) :
      M⁻¹ ≤ radialPartial (fun q => (canonicalCurrentPoint C K z₀ k₀ q).1) (r₀, t) ∧
        M⁻¹ ≤ angularPartial (fun q => (canonicalCurrentPoint C K z₀ k₀ q).2) (r₀, t) := by
    have hy : canonicalCurrentPoint C K z₀ k₀ (r₀, t) =
        (r₀, (canonicalCurrentPoint C K z₀ k₀ (r₀, t)).2) :=
      Prod.ext (canonicalCurrentPoint_root_radial hA' hB'.1 href hsref
        hz₀ hs₀ m₀ side₀ t) rfl
    apply canonicalCurrentPoint_root_diagonal_lower hA' hB'.1 href hsref
      hz₀ hs₀ m₀ side₀ t (zero_lt_one.trans_le hM)
    rw [hy]
    have h := hcoordinate true (canonicalCurrentPoint C K z₀ k₀ (r₀, t)).2
      1 le_rfl (by omega)
    simpa only [F, ↓reduceIte, norm_iteratedFDeriv_one] using h
  refine {
    radial_lower := fun t => (hdiagonal t).1
    angular_lower := fun t => (hdiagonal t).2
    coordinate_jets := fun k hk hkn t => hcoordinate false t k hk hkn
    height_value := ?_
    height_inverse := ?_
    height_jets := ?_ }
  · intro t
    have h := hheight false t 0 (Nat.zero_le _)
    have habs : |n04CoordinatesCurrentHeightRatio C K z₀ k₀ (r₀, t)| ≤ M := by
      simpa only [H, Bool.false_eq_true, ↓reduceIte, Real.rpow_one,
        norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h
    exact (le_abs_self _).trans habs
  · intro t
    have h := hheight true t 0 (Nat.zero_le _)
    have habs : |(n04CoordinatesCurrentHeightRatio C K z₀ k₀ (r₀, t))⁻¹| ≤ M := by
      simpa only [H, ↓reduceIte, Real.rpow_neg_one,
        norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h
    exact (le_abs_self _).trans habs
  · intro k hk hkn t
    have h := hheight false t k hkn
    simpa only [H, Bool.false_eq_true, ↓reduceIte, Real.rpow_one] using h

end ContinuousFlexibility.Analysis
