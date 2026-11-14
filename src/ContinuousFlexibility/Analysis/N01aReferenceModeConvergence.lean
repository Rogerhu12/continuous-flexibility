module

public import ContinuousFlexibility.Analysis.N01aReferenceModeAlgebra

/-!
# Convergence of the actual radial modes of the smooth graph core
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem n01a_abs_integral_mul_le_sqrt_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by simpa using hg
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hg'
  have hnorm := norm_integral_le_integral_norm (μ := μ) (fun x => f x * g x)
  have hnorm' : |∫ x, f x * g x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    simpa only [Real.norm_eq_abs, abs_mul] using hnorm
  apply hnorm'.trans
  simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hholder

theorem n01a_tendsto_integral_mul_of_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g κ : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ) (hκ : MemLp κ 2 μ)
    (hlim : Tendsto (fun n => ∫ x, (f n x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x * κ x ∂μ) atTop (𝓝 (∫ x, g x * κ x ∂μ)) := by
  have heq (n : ℕ) :
      (∫ x, f n x * κ x ∂μ) - (∫ x, g x * κ x ∂μ) =
        ∫ x, (f n x - g x) * κ x ∂μ := by
    simpa only [Pi.mul_apply, sub_mul] using
      (integral_sub ((hf n).integrable_mul hκ) (hg.integrable_mul hκ)).symm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs, heq]
  apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
    (Eventually.of_forall fun n => n01a_abs_integral_mul_le_sqrt_sq ((hf n).sub hg) hκ)
  simpa only [Pi.sub_apply, Real.sqrt_zero, zero_mul] using
    hlim.sqrt.mul_const (Real.sqrt (∫ x, κ x ^ 2 ∂μ))

theorem continuousOn_memLp_two_radialCore {D : ReferenceData} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc D.a D.b)) :
    MemLp f 2 (volume.restrict (radialCore D)) := by
  have hm : MemLp f 2 (volume.restrict (Icc D.a D.b)) :=
    (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable measurableSet_Icc)).mpr
      ((hf.pow 2).integrableOn_Icc)
  exact hm.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)

/-- The free left constants cancel in every positive mode.  Hence the
prescribed output convergence directly controls the mode difference. -/
theorem tendsto_referenceMode_core_square {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) (hchi : Continuous D.chiLeft)
    {γ M : ℝ} (hγ : 0 < γ) {U : RadialUnknown} {Un : ℕ → RadialUnknown}
    (an : ℕ → ℝ) (hU : MemLp U.1 2 (radialPhysicalMeasure D))
    (hUn : ∀ n, Continuous (Un n).1)
    (hreal : ∀ n, OutputRealization D γ M (an n) (Un n - U))
    (hlim : Tendsto (fun n => outputNormSquare D γ M (an n) (Un n - U)) atTop (𝓝 0))
    (j : ℕ) (hj : 0 < j) :
    Tendsto (fun n => ∫ r, (referenceMode (Un n).1 j r - referenceMode U.1 j r) ^ 2
      ∂volume.restrict (radialCore D)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_output_physical_square_bound hab hpart hγ M
  have hUn2 (n : ℕ) : MemLp (Un n).1 2 (radialPhysicalMeasure D) :=
    continuous_memLp_radialPhysicalMeasure (hUn n)
  have hrem2 (n : ℕ) : MemLp (outputRemainder D (an n) (Un n - U)) 2
      (radialPhysicalMeasure D) := by
    have hm : AEStronglyMeasurable (outputRemainder D (an n) (Un n - U))
        (radialPhysicalMeasure D) :=
      ((hUn2 n).sub hU).aestronglyMeasurable.sub
        (continuous_const.mul (hchi.comp continuous_fst)).aestronglyMeasurable
    exact (memLp_two_iff_integrable_sq hm).mpr (hb (Un n - U) (an n) (hreal n)).1
  have hmode (n : ℕ) :
      referenceMode (outputRemainder D (an n) (Un n - U)) j
        =ᵐ[volume.restrict (radialCore D)]
        fun r => referenceMode (Un n).1 j r - referenceMode U.1 j r :=
    (referenceMode_outputRemainder_ae hchi ((hUn2 n).sub hU) (an n) j hj).trans
      (referenceMode_sub_ae (hUn2 n) hU j)
  have hbound (n : ℕ) :
      (∫ r, (referenceMode (Un n).1 j r - referenceMode U.1 j r) ^ 2
        ∂volume.restrict (radialCore D)) ≤
      referenceModeL2Constant ^ 2 * C * outputNormSquare D γ M (an n) (Un n - U) := by
    have hm := hrem2 n
    rw [radialPhysicalMeasure_eq_prod] at hm
    have hproj := (referenceMode_memLp_two_and_integral_bound hm j).2
    rw [← radialPhysicalMeasure_eq_prod] at hproj
    have heq : (∫ r, referenceMode (outputRemainder D (an n) (Un n - U)) j r ^ 2
        ∂volume.restrict (radialCore D)) =
        ∫ r, (referenceMode (Un n).1 j r - referenceMode U.1 j r) ^ 2
          ∂volume.restrict (radialCore D) :=
      integral_congr_ae ((hmode n).mono fun r hr => by dsimp only; rw [hr])
    rw [heq] at hproj
    calc
      _ ≤ referenceModeL2Constant ^ 2 *
          ∫ p, outputRemainder D (an n) (Un n - U) p ^ 2 ∂radialPhysicalMeasure D := hproj
      _ ≤ referenceModeL2Constant ^ 2 *
          (C * outputNormSquare D γ M (an n) (Un n - U)) :=
        mul_le_mul_of_nonneg_left (hb (Un n - U) (an n) (hreal n)).2 (sq_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
    (Eventually.of_forall hbound)
  simpa only [mul_zero] using hlim.const_mul (referenceModeL2Constant ^ 2 * C)

end ContinuousFlexibility.Statements
