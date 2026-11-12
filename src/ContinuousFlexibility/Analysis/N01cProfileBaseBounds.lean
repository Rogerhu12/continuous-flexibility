import ContinuousFlexibility.Analysis.N01cProfileMaterialBounds

/-!
# Base-state radial profile bounds on the original neighbourhood

Undifferentiated parameter factors in a spatial expansion need a uniform
reference-envelope estimate.  Every exponent jet is globally bounded by
the material axioms, so the actual finite exponential majorant has only a
reference-profile E0 power left.  The same N01b neighbourhood bounds the
actual exponential by two.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

/-- Each original exponent-jet majorant is uniformly bounded on the
whole core, from its proved material decay estimate. -/
theorem stateProfileExponentJetMajorant_uniform_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r (hr : r ∈ Ioo D.a D.b),
      stateProfileExponentJetMajorant D T C hA.2.2.1 n r hr ≤ B := by
  obtain ⟨C₀, A, hC₀, _, hpoint⟩ :=
    stateProfileExponentJetMajorant_material_bound hT hA hloc hχloc n
  obtain ⟨M, hM, hweight⟩ :=
    materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) A
  refine ⟨C₀ * M, mul_pos hC₀ hM, fun r hr => ?_⟩
  calc
    _ ≤ C₀ * T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ A := hpoint r hr
    _ = C₀ * (T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ A) := mul_assoc _ _ _
    _ ≤ C₀ * M := mul_le_mul_of_nonneg_left (hweight r hr) hC₀.le

/-- The actual radial profile majorant with no parameter directions has
a uniform E0 bound; no height factor is claimed for the base profile. -/
theorem scaledExponentialJetMajorant_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ Ioo D.a D.b), r ∈ D.cells m →
        scaledExponentialJetMajorant (fun j => |iteratedDeriv j D.w r|)
          (fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr) q n ≤
            B * T.E0 r ^ A := by
  classical
  have hpart : RadialPartition D := hA.1.1.choose_spec.2.1
  let X : Type := {p : ℕ × ℝ // p.2 ∈ D.cells p.1}
  have hcore (x : X) : x.1.2 ∈ Ioo D.a D.b := hpart.2.2.2.1 x.1.1 x.2
  let E : X → ℝ := fun x => T.E0 x.1.2
  let W : ℕ → X → ℝ := fun j x => |iteratedDeriv j D.w x.1.2|
  have hWprimitive (j : ℕ) :
      ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ x : X, W j x ≤ B * 1 * E x ^ A := by
    obtain ⟨B, A, hB, hA', hb⟩ := referenceProfile_iteratedDeriv_le_E0 hA.1.1 hE j
    exact ⟨B, A, hB, hA', fun x => by
      simpa only [W, E, mul_one] using hb x.1.1 x.1.2 x.2⟩
  obtain ⟨CW, A, hCW, hA', hWbound⟩ := finiteOrder_envelope_bound
    (fun _ : X => 1) E (fun _ => zero_le_one)
    (fun x => hE _ (hcore x)) W hWprimitive n
  choose R hR hRbound using
    (fun j => stateProfileExponentJetMajorant_uniform_bound hT hA hloc hχloc j)
  let M : ℝ := 1 + ∑ i : Fin (n + 1), R i.val
  have hM : 0 < M := by
    have hh : 0 ≤ ∑ i : Fin (n + 1), R i.val :=
      Finset.sum_nonneg (fun i _ => (hR i.val).le)
    dsimp only [M]
    linarith
  have hRle (j : ℕ) (hj : j ≤ n) : R j ≤ M := by
    let i : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have hh : R i.val ≤ ∑ l : Fin (n + 1), R l.val :=
      Finset.single_le_sum (fun l _ => (hR l.val).le) (Finset.mem_univ i)
    dsimp only [i] at hh
    dsimp only [M]
    linarith
  let F : ℝ := scaledExponentialJetMajorant (fun _ => 1) (fun _ => M) q n
  have hF : 0 ≤ F := scaledExponentialJetMajorant_nonneg _ _ q
    (fun _ => zero_le_one) (fun _ => hM.le) hq n
  have hcoef : 0 ≤ CW * F := mul_nonneg hCW.le hF
  refine ⟨1 + CW * F, A, by linarith, hA', fun m r hr hrm => ?_⟩
  let x : X := ⟨(m, r), hrm⟩
  have hEpos : 0 < T.E0 r := (hT.2.1 r hr).2.2.1
  have hb := scaledExponentialJetMajorant_le_const
    (fun j => |iteratedDeriv j D.w r|)
    (fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr)
    (fun _ => abs_nonneg _)
    (fun j => stateProfileExponentJetMajorant_nonneg hT hA.1.1 hA.2.2.1 j r hr)
    (mul_nonneg hCW.le (Real.rpow_nonneg hEpos.le A)) hq n
    (fun j hj => by simpa only [W, E, x, mul_one] using hWbound j hj x)
    (fun j hj => (hRbound j r hr).trans (hRle j hj))
  calc
    _ ≤ (CW * T.E0 r ^ A) * F := hb
    _ = (CW * F) * T.E0 r ^ A := by ring
    _ ≤ (1 + CW * F) * T.E0 r ^ A :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hEpos.le A)

private abbrev profileBaseStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] profileBaseStateTopology

private abbrev profileBaseStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] profileBaseStateGroup

private abbrev profileBaseStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] profileBaseStateModule

private abbrev profileBaseStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (profileBaseStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] profileBaseStateSMul

/-- A pointwise bound by the fixed genuine majorant on the original
neighbourhood, before any existential material constants are transported. -/
theorem abs_iteratedDeriv_stateProfile_le_majorant_on_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hB : N01PartB D S C base ε)
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    |iteratedDeriv n (stateProfile D S C z.1) r| ≤
      2 * scaledExponentialJetMajorant (fun j => |iteratedDeriv j D.w r|)
        (fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr)
        (stateGrading S 0 C.referenceState + ε) n := by
  let W : ℕ → ℝ := fun j => |iteratedDeriv j D.w r|
  let P : ℕ → ℝ := fun j =>
    stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr
  have hW (j : ℕ) : 0 ≤ W j := abs_nonneg _
  have hP (j : ℕ) : 0 ≤ P j :=
    stateProfileExponentJetMajorant_nonneg hT hA.1.1 hA.2.2.1 j r hr
  have hq₀ : 0 ≤ stateGrading S 0 z.1 := apply_nonneg _ _
  exact (abs_iteratedDeriv_stateProfile_le_rawMajorant
    hS hT hA.1.1 hD hA.2.2.1 hχ n r hr z.1).trans
      (mul_le_mul
        (n01PartB_stateProfileExponent_exp_le_two hD hS hA.2.1 hB hz r hr)
        (scaledExponentialJetMajorant_mono W P hW hP hq₀
          (stateGrading_zero_le_reference_add_radius hz) n)
        (scaledExponentialJetMajorant_nonneg W P _ hW hP hq₀ n)
        (by norm_num))

/-- Uniform ordinary radial jets of the actual base profile on the
original common neighbourhood, including zero spatial order. -/
theorem iteratedDeriv_stateProfile_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ Ioo D.a D.b), r ∈ D.cells m →
      ∀ z ∈ stateNeighborhood S C base ε,
        |iteratedDeriv n (stateProfile D S C z.1) r| ≤ B * T.E0 r ^ A :=
  exists_scalar_envelope_bound_of_majorant (X := AnnularState S × ℝ)
    (Ioo D.a D.b) D.cells T.E0 (stateNeighborhood S C base ε)
    (fun r hr => scaledExponentialJetMajorant (fun j => |iteratedDeriv j D.w r|)
      (fun j => stateProfileExponentJetMajorant D T C hA.2.2.1 j r hr)
      (stateGrading S 0 C.referenceState + ε) n)
    (fun r _ z => iteratedDeriv n (stateProfile D S C z.1) r)
    (scaledExponentialJetMajorant_material_bound hT hA hE hloc hχloc
      (add_nonneg (apply_nonneg (stateGrading S 0) C.referenceState) hε.le) n)
    (fun r hr z hz => abs_iteratedDeriv_stateProfile_le_majorant_on_neighborhood
      hS hT hA hD hχ hB n r hr hz)

end ContinuousFlexibility.Statements
