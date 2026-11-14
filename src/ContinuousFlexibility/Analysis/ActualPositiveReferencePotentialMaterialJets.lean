module

public import ContinuousFlexibility.Analysis.ActualPositiveReferenceInverseMaterialJets
public import ContinuousFlexibility.Analysis.RadialReferencePotentialJetEnvelope
public import Mathlib.Topology.Order.Compact

/-!
# Material jets of the same displayed positive reference potential

The finite endpoint envelope is chosen once before every spatial order.
The coordinate, inverse and height below are exactly the displayed
reference interpolation produced with that envelope. A finite prefix of
the proved inverse jets is combined with the actual forward height jets.
The physical profile is estimated on the fixed closed annulus, and its
evaluation point belongs there by the actual inverse range certificate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped Topology ContDiff BigOperators

private theorem referencePotential_profile_compact_bound
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (l r : ℝ) (s : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ k, k ≤ s → ∀ x ∈ Icc l r,
      |iteratedDeriv k w x| ≤ P := by
  classical
  have hbound (k : Fin (s + 1)) : ∃ A : ℝ, ∀ x ∈ Icc l r,
      ‖iteratedDeriv k.val w x‖ ≤ A :=
    isCompact_Icc.exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedDeriv k.val hw (by simp)).continuousOn
  choose A hA using hbound
  refine ⟨∑ k : Fin (s + 1), |A k|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro k hk x hx
  let j : Fin (s + 1) := ⟨k, by omega⟩
  have hjet : |iteratedDeriv k w x| ≤ A j := by
    simpa only [Real.norm_eq_abs] using hA j x hx
  exact (hjet.trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun k => |A k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))

/-- The actual flux potential has polynomial sample bounds at every
order. The returned finite data, width and range geometry use precisely
the same low envelope selected before those orders. -/
theorem n04Coordinates_retained_positive_reference_potential_material_jets
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε K : ℝ}
    (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
    (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
    (hfield : N04bFieldRegularity Γ.reference S C L base ε)
    (e : ℕ ≃ N04PieceIndex Γ.reference) (hK : 0 < K)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m))
    (hoptical : ∀ m x, x ∈ Ioo (C.left m) (C.right m) →
      K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
        min (x - C.left m) (C.right m - x) ≤
          -deriv Γ.reference.w x / (x * Γ.reference.w x)) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ n : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      (∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
        ∀ src : (side : Bool) → N04PositiveEndpointSource C i side,
          let A := n04bActualTypedAtlas hT hS hN hfield e
          let U := B * (C0 * T.E0 (T.sample j)) ^ B
          1 ≤ U ∧ (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ U ∧
            n04PositiveRight i - n04PositiveLeft i ≤ U ∧
            ∀ side : Bool,
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
                (n04PositiveEndpoint i side) 1 0 ∧
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
                (n04PositiveEndpoint i side) 0 0 ∧
              (∀ k : ℕ, 1 ≤ k → k ≤ n + 1 →
                |radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) ∧
              ∀ k : ℕ, k ≤ n + 1 →
                |radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) ∧
      ∀ s : ℕ, ∃ M : ℝ, 1 ≤ M ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
      ∀ src : (side : Bool) → N04PositiveEndpointSource C i side,
        let A := n04bActualTypedAtlas hT hS hN hfield e
        let W := C0 * T.E0 (T.sample j)
        let U := B * W ^ B
        let δ := positiveReferenceTaylorWidth n
          (n04PositiveLeft i) (n04PositiveRight i) U⁻¹ U
        let ys := fun side : Bool => radialEndpointTaylorSlice (n + 1)
          (n04PositiveEndpoint i side) (n04PositiveReferenceSourceCoordinate (src side) A)
        let hs := fun side : Bool => radialEndpointTaylorSlice (n + 1)
          (n04PositiveEndpoint i side) (n04PositiveReferenceSourceHeight (src side) A)
        let Y := positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i) δ
          (deriv (ys false)) (deriv (ys true))
        let H := positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i) δ
          (hs false) (hs true)
        let χ := Function.invFun Y
        PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
          (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
          (n04PositiveLeft i) (n04PositiveRight i) 0 1 ∧
        ∀ x ∈ Ioo (0 : ℝ) 1,
          |iteratedDeriv s
            (fun t => -(H (χ t) * deriv ((fun r => Γ.reference.w r * deriv H r) ∘ χ) t)) x| ≤
              M * W ^ M := by
  classical
  obtain ⟨C0, hC0, hfloor, hfamily⟩ :=
    n04Coordinates_retained_positive_reference_inverse_material_jets
      P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e hK hhost hoptical
  refine ⟨C0, hC0, hfloor, ?_⟩
  intro n
  obtain ⟨B, hB, hfinite, hjets⟩ := hfamily n
  refine ⟨B, hB, hfinite, ?_⟩
  choose A₀ hA₀ hactual using hjets
  intro s
  have hDgeom : RadialProfileGeometry Γ.reference := n04b_profileGeometry_of_through03 hN
  obtain ⟨P₀, hP₀, hprofile⟩ := referencePotential_profile_compact_bound
    hDgeom.2.2.1.1 Γ.reference.a Γ.reference.b (s + 1)
  obtain ⟨C₁, hC₁, henvelope⟩ := exists_radialReferencePotential_jet_envelope s
  let D : ℝ := 1 + ∑ k : Fin (s + 3), A₀ k.val
  have hD : 1 ≤ D := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun k _ => zero_le_one.trans (hA₀ k.val)))
  have hAD (k : ℕ) (hk : k ≤ s + 2) : A₀ k ≤ D :=
    (Finset.single_le_sum (f := fun j : Fin (s + 3) => A₀ j.val)
      (fun j _ => zero_le_one.trans (hA₀ j.val))
      (Finset.mem_univ (⟨k, by omega⟩ : Fin (s + 3)))).trans
        (le_add_of_nonneg_left zero_le_one)
  let d : ℕ := 2 * s + 3
  let coefficient : ℝ := C₁ * P₀ * D ^ d
  let exponent : ℝ := D * (d : ℝ)
  let M : ℝ := 1 + D + coefficient + exponent
  have hcoefficient : 0 ≤ coefficient :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hC₁) hP₀)
      (pow_nonneg (zero_le_one.trans hD) _)
  have hexponent : 0 ≤ exponent :=
    mul_nonneg (zero_le_one.trans hD) (Nat.cast_nonneg _)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hD, hcoefficient, hexponent]
  have hcoefficientM : coefficient ≤ M := by dsimp only [M]; linarith only [hD, hexponent]
  have hexponentM : exponent ≤ M := by dsimp only [M]; linarith only [hD, hcoefficient]
  refine ⟨M, hM, ?_⟩
  intro i j hmid src
  let A := n04bActualTypedAtlas hT hS hN hfield e
  let W : ℝ := C0 * T.E0 (T.sample j)
  let U : ℝ := B * W ^ B
  let Z : ℝ := D * W ^ D
  let a : Bool → ℝ := fun side => n04PositiveSourceLeft (src side)
  let b : Bool → ℝ := fun side => n04PositiveSourceRight (src side)
  let y : Bool → PolarPoint → ℝ :=
    fun side => n04PositiveReferenceSourceCoordinate (src side) A
  let h : Bool → PolarPoint → ℝ :=
    fun side => n04PositiveReferenceSourceHeight (src side) A
  let δ := positiveReferenceTaylorWidth n (n04PositiveLeft i) (n04PositiveRight i) U⁻¹ U
  let ys : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (n04PositiveEndpoint i side) (y side)
  let hs : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (n04PositiveEndpoint i side) (h side)
  let Y := positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i) δ
    (deriv (ys false)) (deriv (ys true))
  let H := positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i) δ
    (hs false) (hs true)
  let χ : ℝ → ℝ := Function.invFun Y
  have hW : 1 ≤ W := hfloor j
  have hZ : 1 ≤ Z := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ D * W ^ D := mul_le_mul hD
        (Real.one_le_rpow hW (zero_le_one.trans hD)) zero_le_one (zero_le_one.trans hD)
  have hbound (k : ℕ) (hk : k ≤ s + 2) : A₀ k * W ^ A₀ k ≤ Z := by
    exact mul_le_mul (hAD k hk)
      (Real.rpow_le_rpow_of_exponent_le hW (hAD k hk))
      (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hD)
  have hcost : C₁ * P₀ * Z ^ d ≤ M * W ^ M := by
    calc
      _ = coefficient * W ^ exponent := by
        dsimp only [Z, coefficient, exponent]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hW) D d]
        ring
      _ ≤ coefficient * W ^ M := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hW hexponentM) hcoefficient
      _ ≤ M * W ^ M := mul_le_mul_of_nonneg_right hcoefficientM
        (Real.rpow_nonneg (zero_le_one.trans hW) _)
  have hinput := hfinite i j hmid src
  have hU : 1 ≤ U := hinput.1
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hf : Continuous (deriv Γ.reference.w) := hDgeom.2.2.1.1.continuous_deriv (by simp)
  have hlr : n04PositiveLeft i < n04PositiveRight i :=
    (n04PositiveComponent_bounds hf i).2.1
  have hd (side : Bool) :=
    n04Coordinates_actual_positive_reference_source_data hT hS hN hfield e (src side)
  have hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1 :=
    (positiveReferenceFiniteRadialJets_prescribed n
      (κ := U⁻¹) (M := U) (a := a) (b := b) (y := y) (h := h)
      hlr (inv_pos.mpr hUpos) hUpos.le
      (fun side => (hd side).1) (fun side => (hd side).2.1)
      (fun side => (hd side).2.2.1) (fun side => (hd side).2.2.2.1)
      (fun side => (hd side).2.2.2.2.1) (fun side => (hd side).2.2.2.2.2.1)
      (fun side x hx θ => (hd side).2.2.2.2.2.2.1 x hx θ)
      (fun side x hx θ => (hd side).2.2.2.2.2.2.2.1 x hx θ)
      (fun side => (hd side).2.2.2.2.2.2.2.2.1)
      (fun side => (hinput.2.2.2 side).1) (fun side => (hinput.2.2.2 side).2.1)
      (fun side => (hinput.2.2.2 side).2.2.1)
      (fun side => (hinput.2.2.2 side).2.2.2)).1
  have hline : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hH : ContDiff ℝ ∞ H := by
    simpa only [Function.comp_def] using hgeometry.height_smooth.comp hline
  have hχ : ContDiff ℝ ∞ χ := by
    simpa only [positiveReferenceCylinderInverse, Function.comp_def, χ] using
      hgeometry.inverse_smooth.fst.comp hline
  have hforward : ∀ k, k ≤ s + 2 → ∀ x : ℝ,
      |iteratedDeriv (k + 1) Y x| ≤ A₀ (s + 2) * W ^ A₀ (s + 2) ∧
      |iteratedDeriv k H x| ≤ A₀ (s + 2) * W ^ A₀ (s + 2) ∧
      |iteratedDeriv k (fun t => (H t)⁻¹) x| ≤ A₀ (s + 2) * W ^ A₀ (s + 2) :=
    (hactual (s + 2) i j hmid src).1
  have hHjets (k : ℕ) (hk : k ≤ s + 2) (x : ℝ) :
      |iteratedDeriv k H x| ≤ Z :=
    ((hforward k hk x).2.1).trans (hbound (s + 2) le_rfl)
  have hχjets (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s + 1) (x : ℝ) :
      |iteratedDeriv k χ x| ≤ Z := by
    have he : k - 1 + 1 = k := by omega
    have hi : |iteratedDeriv (k - 1 + 1) χ x| ≤ A₀ (k - 1) * W ^ A₀ (k - 1) :=
      (hactual (k - 1) i j hmid src).2 x
    rw [he] at hi
    exact hi.trans (hbound (k - 1) (by omega))
  change PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
    (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
    (n04PositiveLeft i) (n04PositiveRight i) 0 1 ∧
      ∀ x ∈ Ioo (0 : ℝ) 1,
        |iteratedDeriv s
          (fun t => -(H (χ t) * deriv ((fun r => Γ.reference.w r * deriv H r) ∘ χ) t)) x| ≤
            M * W ^ M
  refine ⟨hgeometry, ?_⟩
  intro x hx
  have hxcanonical : (x, (0 : ℝ)) ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) :=
    ⟨hx, mem_univ _⟩
  have hxphysical : χ x ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) :=
    (hgeometry.inverse_maps_open hxcanonical).1
  have hxcore : χ x ∈ Ioo Γ.reference.a Γ.reference.b :=
    n04PositiveComponent_interval_subset hf i hxphysical
  have hb := henvelope hP₀ hZ Γ.reference.w H χ x hDgeom.2.2.1.1 hH hχ
    (fun k hk => hprofile k hk (χ x) ⟨hxcore.1.le, hxcore.2.le⟩)
    (fun k hk => hHjets k hk (χ x))
    (fun k hk hks => hχjets k hk hks x)
  exact hb.trans hcost

end ContinuousFlexibility.Analysis
