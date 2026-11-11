import ContinuousFlexibility.Analysis.N01aReferenceWeightedMode

/-!
# Actual radial multipliers controlled by the reference weights

A pointwise cell bound for a multiplier is converted into genuine physical
L² membership by the original partition. In particular, the cosine mode
then gives ordinary radial L² membership with no alternative norm.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false in
theorem n01a_reference_multiplier_memLp {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D)
    {F : PolarPoint → ℝ} (hF : Continuous F)
    (hcell : RadialCellIntegrable D F) {γ M : ℝ}
    (hsum : Summable (outputCellSquare D γ M F))
    {g : ℝ → ℝ} (hg : ContinuousOn g (radialCore D)) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ m r, r ∈ D.cells m → g r ^ 2 ≤ K *
      Real.exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m))) :
    MemLp (fun p => g p.1 * F p) 2 (radialPhysicalMeasure D) := by
  let V : PolarPoint → ℝ := fun p => g p.1 * F p
  let W : ℕ → ℝ := fun m =>
    Real.exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m))
  have hW (m : ℕ) : 0 ≤ W m := (Real.exp_pos _).le
  have hgpolar : ContinuousOn (fun p : PolarPoint => g p.1)
      (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) :=
    hg.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hVm : AEStronglyMeasurable V (radialPhysicalMeasure D) :=
    (hgpolar.mul hF.continuousOn).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioc)
  have hmajor (m : ℕ) : ∀ p : PolarPoint,
      (D.localizer m p.1 * V p) ^ 2 ≤
        (K * W m) * (D.localizer m p.1 * F p) ^ 2 := by
    intro p
    by_cases hz : D.localizer m p.1 = 0
    · simp only [hz, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    · have hp : p.1 ∈ D.cells m := hpart.2.2.1 m (Function.mem_support.mpr hz)
      calc
        _ = g p.1 ^ 2 * (D.localizer m p.1 * F p) ^ 2 := by dsimp only [V]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hbound m p.1 hp) (sq_nonneg _)
  have hVcell : RadialCellIntegrable D V := by
    intro m
    have hm := ((((hpart.1 m).continuous.comp continuous_fst).aestronglyMeasurable.mul hVm)
      .aemeasurable.pow_const (2 : ℕ)).aestronglyMeasurable
    exact ((hcell.integrable_square m).const_mul (K * W m)).mono_nonneg hm
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall (hmajor m))
  have hcells (m : ℕ) : referenceCellSquare D m V ≤ K * outputCellSquare D γ M F m := by
    have hi := integral_mono (hVcell.integrable_square m)
      ((hcell.integrable_square m).const_mul (K * W m)) (hmajor m)
    rw [integral_const_mul] at hi
    rw [referenceCellSquare_eq_integral hab hVcell m, outputCellSquare,
      referenceCellSquare_eq_integral hab hcell m]
    calc
      _ ≤ (2 * Real.pi)⁻¹ *
          ((K * W m) * ∫ p, (D.localizer m p.1 * F p) ^ 2 ∂radialPhysicalMeasure D) :=
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (by positivity))
      _ = _ := by dsimp only [W]; ring
  have hsV : Summable (fun m => referenceCellSquare D m V) :=
    Summable.of_nonneg_of_le (fun m => referenceCellSquare_nonneg hab m V) hcells
      (hsum.mul_left K)
  obtain ⟨C, hC, hb⟩ := exists_radialPartition_integral_square_bound hab hpart
  exact (memLp_two_iff_integrable_sq hVm).mpr (hb V hVcell hsV).1

set_option backward.isDefEq.respectTransparency false in
theorem n01a_weighted_radial_multiplier_memLp {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D)
    {f : ℝ → ℝ} (hf : Continuous f) {γ M : ℝ}
    (houtput : OutputRealization D γ M 0
      ((fun p => f p.1 * Radial.cosineMode 2 p.2), 0))
    {g : ℝ → ℝ} (hg : ContinuousOn g (radialCore D)) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ m r, r ∈ D.cells m → g r ^ 2 ≤ K *
      Real.exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m))) :
    MemLp (fun r => g r * f r) 2 (volume.restrict (radialCore D)) := by
  let F : PolarPoint → ℝ := fun p => f p.1 * Radial.cosineMode 2 p.2
  have hF : Continuous F := by
    dsimp only [F]
    unfold Radial.cosineMode
    fun_prop
  have hcell : RadialCellIntegrable D F := by
    simpa only [outputRemainder, zero_mul, sub_zero] using houtput.1
  have hsum : Summable (outputCellSquare D γ M F) := by
    simpa only [outputRemainder, zero_mul, sub_zero] using houtput.2.1
  have hV := n01a_reference_multiplier_memLp hab hpart hF hcell hsum hg hK hbound
  have hm := referenceMode_memLp_two hV 2
  have heq : referenceMode (fun p => g p.1 * F p) 2 = fun r => g r * f r := by
    funext r
    rw [referenceMode_mul_radial]
    dsimp only [F]
    rw [referenceMode_cosine_field f 2 2 (by decide) (by decide)]
    simp only [ite_true, mul_one]
  rw [heq] at hm
  exact hm

end ContinuousFlexibility.Statements
