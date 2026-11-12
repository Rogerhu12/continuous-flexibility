import ContinuousFlexibility.Radial.ReferenceCellAlgebra
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Interior L² control from the actual radial cells

Only finitely many actual cells meet a compact radial interval. Their
partition identity reconstructs the field there, so the frozen local
L² domain gives genuine ordinary L² on every interior cylinder.
Angular averages are consequently locally integrable, including for
outputs after their smooth left height is restored.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal

theorem RadialCellIntegrable.memLp_on_interval {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) {l h : ℝ}
    (hsub : Icc l h ⊆ radialCore D) :
    MemLp f 2 ((volume.restrict (Icc l h)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  classical
  obtain ⟨C, _, hP, _, _, _, hfinite, _⟩ := hD
  let hs := hfinite (Icc l h) isCompact_Icc hsub
  let s : Finset ℕ := hs.toFinset
  have hle : (volume.restrict (Icc l h)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) ≤ radialPhysicalMeasure D := by
    rw [radialPhysicalMeasure_eq_prod]
    exact Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
  have hsum : MemLp (fun x : PolarPoint => ∑ m ∈ s, D.localizer m x.1 * f x) 2
      ((volume.restrict (Icc l h)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :=
    memLp_finsetSum s (fun m _ => (hf m).mono_measure hle)
  have hmem : ∀ᵐ x : PolarPoint ∂(volume.restrict (Icc l h)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))), x.1 ∈ Icc l h :=
    (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Icc l h))
      (ν := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))).ae
      (ae_restrict_mem measurableSet_Icc)
  apply (memLp_congr_ae ?_).mp hsum
  filter_upwards [hmem] with x hx
  have hz (m : ℕ) (hm : m ∉ s) : D.localizer m x.1 = 0 := by
    by_contra hne
    apply hm
    exact hs.mem_toFinset.mpr ⟨x.1, hP.2.2.1 m hne, hx⟩
  calc
    (∑ m ∈ s, D.localizer m x.1 * f x) =
        ∑' m, D.localizer m x.1 * f x :=
      (tsum_eq_sum (s := s) (fun m hm => by rw [hz m hm, zero_mul])).symm
    _ = f x := hP.tsum_localizer_mul (hsub hx) (f x)

/-- A continuous field has ordinary L² on a finite radial-angular rectangle. -/
theorem continuous_memLp_reference_interval {f : PolarPoint → ℝ}
    (hf : Continuous f) (l h : ℝ) :
    MemLp f 2 ((volume.restrict (Icc l h)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (hf.continuousOn :
        ContinuousOn f (Icc l h ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
  apply MemLp.of_bound hf.aestronglyMeasurable B
  have hr : ∀ᵐ x : PolarPoint ∂(volume.restrict (Icc l h)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))), x.1 ∈ Icc l h :=
    (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Icc l h))
      (ν := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))).ae
      (ae_restrict_mem measurableSet_Icc)
  have ht : ∀ᵐ x : PolarPoint ∂(volume.restrict (Icc l h)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))),
      x.2 ∈ Ioc (0 : ℝ) (2 * Real.pi) :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc l h))
      (ν := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))).ae
      (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hr, ht] with x hx hθ
  exact hB x ⟨hx, hθ.1.le, hθ.2⟩

theorem angularMean_intervalIntegrable_of_memLp {l h : ℝ} (hlh : l ≤ h)
    {f : PolarPoint → ℝ}
    (hf : MemLp f 2 ((volume.restrict (Icc l h)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) :
    IntervalIntegrable (fun r => radialAngularMean (fun θ => f (r, θ))) volume l h := by
  have hi := (MemLp.integrable (show (1 : ℝ≥0∞) ≤ 2 by norm_num) hf).integral_prod_left
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hlh).mpr
  change Integrable (fun r => radialAngularMean (fun θ => f (r, θ)))
    (volume.restrict (Icc l h))
  simpa only [radialAngularMean,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] using
      hi.const_mul ((2 * Real.pi)⁻¹)

theorem RadialCellIntegrable.angularMean_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) {l h : ℝ}
    (hlh : l ≤ h) (hsub : Icc l h ⊆ radialCore D) :
    IntervalIntegrable (fun r => radialAngularMean (fun θ => f (r, θ))) volume l h :=
  angularMean_intervalIntegrable_of_memLp hlh (hf.memLp_on_interval hD hsub)

theorem OutputRealization.memLp_on_interval {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M aL : ℝ} {U : RadialUnknown} (hU : OutputRealization D γ M aL U)
    {l h : ℝ} (hsub : Icc l h ⊆ radialCore D) :
    MemLp U.1 2 ((volume.restrict (Icc l h)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  have hchi : Continuous (fun x : PolarPoint => aL * D.chiLeft x.1) :=
    continuous_const.mul (hB.2.2.2.2.1.continuous.comp continuous_fst)
  have hh := (hU.1.memLp_on_interval hD hsub).add
    (continuous_memLp_reference_interval hchi l h)
  apply (memLp_congr_ae ?_).mp hh
  filter_upwards with x
  change U.1 x - aL * D.chiLeft x.1 + aL * D.chiLeft x.1 = U.1 x
  ring

theorem OutputMember.angularMean_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M : ℝ} {U : RadialUnknown} (hU : OutputMember D γ M U)
    {l h : ℝ} (hlh : l ≤ h) (hsub : Icc l h ⊆ radialCore D) :
    IntervalIntegrable (fun r => radialAngularMean (fun θ => U.1 (r, θ))) volume l h := by
  obtain ⟨aL, hU⟩ := hU
  exact angularMean_intervalIntegrable_of_memLp hlh (hU.memLp_on_interval hD hB hsub)

end ContinuousFlexibility.Statements
