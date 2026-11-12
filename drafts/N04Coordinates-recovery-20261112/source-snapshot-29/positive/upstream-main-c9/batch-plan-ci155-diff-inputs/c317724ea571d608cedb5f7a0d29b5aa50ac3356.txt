import ContinuousFlexibility.Analysis.N05SeedOpticalLowerAssembly
import ContinuousFlexibility.Analysis.N01aOpticalProfile
import ContinuousFlexibility.Analysis.AffineMaterialSampling
import ContinuousFlexibility.Blueprint.Statements

/-!
# The retained seed's actual material primitive certificate

The affine envelope is at least one on the whole real line. The actual
seed optical lower bound is charged to each chosen whole-component host
and converted to that host's affine sample. The strict border support is
already part of the same radial-reference witness. This draft uses the
additive N01PrimitiveGeometry definition in the per-k companion patch.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real ContinuousFlexibility.Analysis

theorem n05Retained_affine_E0_one (D : ReferenceData) (sample : ℕ → ℝ) (r : ℝ) :
    1 ≤ (affineMaterialData D sample).E0 r := by
  have hlog (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Real.log (materialE0 x) := by
    rw [materialE0, Real.log_exp, materialE0Exponent]
    have hl : 0 ≤ materialLogFactor x :=
      Real.log_nonneg ((Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans
        (le_add_of_nonneg_right hx))
    exact add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg hx _) hl)
  let t := affineMaterialUnitCoordinate D r
  change 1 ≤ Real.exp (materialIntervalLogE0 t)
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr (materialIntervalTransition_le_one t))
      (hlog (materialIntervalXL t) (Real.sqrt_nonneg _)))
    (mul_nonneg (materialIntervalTransition_nonneg t)
      (hlog (materialIntervalXR t) (Real.sqrt_nonneg _)))

/-- A coefficient is charged to its own actual physical host sample. -/
theorem n05Retained_affine_coefficient_power {D : ReferenceData} {sample : ℕ → ℝ}
    (hD : IsAccumulatingProfile D) (hsample : ∀ m, sample m ∈ D.cells m)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
      B * radialE (D.cellIndex j) ^ B ≤
        C * (affineMaterialData D sample).E0 (sample j) ^ C := by
  obtain ⟨A, _, _, _, hlog⟩ := affineMaterialData_cell_log_bounds (sample := sample) hD
  obtain ⟨C, hC, hmajor⟩ := n01aOptical_absorb_power B (A * B) hB
  refine ⟨C, hC, fun j => ?_⟩
  have hE : 1 ≤ (affineMaterialData D sample).E0 (sample j) :=
    n05Retained_affine_E0_one D sample (sample j)
  have hEpos : 0 < (affineMaterialData D sample).E0 (sample j) :=
    zero_lt_one.trans_le hE
  have hp : radialE (D.cellIndex j) ^ B ≤
      (affineMaterialData D sample).E0 (sample j) ^ (A * B) := by
    rw [radialE, ← Real.exp_mul, Real.rpow_def_of_pos hEpos]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (hlog j (sample j) (hsample j)).2.1 hB
    nlinarith only [hh]
  exact (mul_le_mul_of_nonneg_left hp hB).trans (hmajor _ hE)

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Radial.SeedReferenceConstruction

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

variable {q : ℝ} (P : SeedReferenceConstruction q)

/-- The primitive lower bound is derived from the same actual seed and
the supplied actual host inclusion; it is not an additional estimate input. -/
theorem n05Retained_primitiveGeometry (hq : 0 < q)
    (hD : IsRadialReference P.reference) {sample : ℕ → ℝ}
    (hsample : ∀ j, sample j ∈ P.reference.cells j)
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (hC : controlGeometryConditions P.reference S C)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ P.reference.cells (C.cell m)) :
    N01PrimitiveGeometry P.reference (affineMaterialData P.reference sample) S C := by
  obtain ⟨B, hB, hseed⟩ := P.n05_actual_carrier_optical_lower hq
  let A : ℝ := max B 12
  have hA : 0 < A := hB.trans_le (le_max_left _ _)
  obtain ⟨K, hK, hweight⟩ :=
    n05Retained_affine_coefficient_power hD.1 hsample A hA.le
  refine ⟨hhost, fun r hr => (hD.2.2.2.1.2.2.1 hr).1, K, hK, ?_⟩
  intro m r hr
  let j := C.cell m
  let E := (affineMaterialData P.reference sample).E0 (sample j)
  have hE : 0 < E := zero_lt_one.trans_le
    (n05Retained_affine_E0_one P.reference sample (sample j))
  have hR : 0 < radialE (P.reference.cellIndex j) := Real.exp_pos _
  have hR1 : 1 ≤ radialE (P.reference.cellIndex j) :=
    Real.one_le_exp (radialQ_nonneg _)
  have hpower : B * radialE (P.reference.cellIndex j) ^ (12 : ℝ) ≤ K * E ^ K := by
    have hm := mul_le_mul (le_max_left B 12)
      (Real.rpow_le_rpow_of_exponent_le hR1 (le_max_right B 12))
      (Real.rpow_nonneg hR.le (12 : ℝ)) hA.le
    exact hm.trans (hweight j)
  have hinv : K⁻¹ * E ^ (-K) ≤
      (B * radialE (P.reference.cellIndex j) ^ (12 : ℝ))⁻¹ := by
    calc
      K⁻¹ * E ^ (-K) = (K * E ^ K)⁻¹ := by
        rw [Real.rpow_neg hE.le K, mul_inv_rev]
        exact mul_comm _ _
      _ ≤ _ := by
        simpa only [one_div] using one_div_le_one_div_of_le
          (mul_pos hB (Real.rpow_pos_of_pos hR (12 : ℝ))) hpower
  have hcomponent : NegativeRadialComponent P.reference (C.left m) (C.right m) :=
    ⟨(hC.1 m).1, (hC.1 m).2.1, (hC.1 m).2.2,
      (hC.2.1 m).1, (hC.2.1 m).2.1, hC.2.2.2.1 m⟩
  have hdist : 0 ≤ min (r - C.left m) (C.right m - r) :=
    le_min (sub_nonneg.mpr hr.1.le) (sub_nonneg.mpr hr.2.le)
  exact (mul_le_mul_of_nonneg_right hinv hdist).trans
    (hseed (C.left m) (C.right m) j hcomponent (hhost m) r (Ioo_subset_Icc_self hr))

end ContinuousFlexibility.Radial.SeedReferenceConstruction
