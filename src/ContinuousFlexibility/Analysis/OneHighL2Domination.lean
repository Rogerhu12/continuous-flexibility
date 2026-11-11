import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Finite pointwise majorants in the actual L² space

This lemma proves membership before passing to real norms. It therefore
applies on the noncompact cylinder without assuming that the output, or its
derivatives, already has finite energy.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal BigOperators

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X} {ι : Type*} [Fintype ι]

/-- A finite nonnegative linear combination of genuine L² functions controls
both the L² membership and norm of a measurable function. -/
theorem oneHigh_l2_finite_domination
    {g : X → E} (hg : AEStronglyMeasurable g μ)
    (u : ι → X → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hpoint : ∀ᵐ x ∂μ, ‖g x‖ ≤ ∑ i, C i * ‖u i x‖) :
    MemLp g 2 μ ∧
      (eLpNorm g 2 μ).toReal ≤ ∑ i, C i * (eLpNorm (u i) 2 μ).toReal := by
  classical
  let N (i : ι) : X → ℝ := C i • fun x => ‖u i x‖
  have hN (i : ι) : MemLp (N i) 2 μ := (hu i).norm.const_smul (C i)
  have hsum : MemLp (∑ i, N i) 2 μ :=
    memLp_finsetSum' Finset.univ (fun i _ => hN i)
  have hnonneg (x : X) : 0 ≤ (∑ i, N i) x := by
    simp only [Finset.sum_apply, N, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC i) (norm_nonneg _)
  have hdom : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖(∑ i, N i) x‖ := by
    filter_upwards [hpoint] with x hx
    rw [Real.norm_of_nonneg (hnonneg x)]
    simpa only [Finset.sum_apply, N, Pi.smul_apply, smul_eq_mul] using hx
  refine ⟨hsum.of_le hg hdom, ?_⟩
  have hnfin (i : ι) : eLpNorm (N i) 2 μ ≠ ∞ := (hN i).ne
  have htriangle :
      (eLpNorm (∑ i, N i) 2 μ).toReal ≤
        ∑ i, (eLpNorm (N i) 2 μ).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.sum_ne_top.mpr (fun i _ => hnfin i))
      (eLpNorm_sum_le (μ := μ) (f := N) (s := Finset.univ)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    rwa [ENNReal.toReal_sum (fun i _ => hnfin i)] at h
  have hscale (i : ι) :
      (eLpNorm (N i) 2 μ).toReal = C i * (eLpNorm (u i) 2 μ).toReal := by
    dsimp only [N]
    rw [eLpNorm_const_smul, Real.enorm_of_nonneg (hC i),
      eLpNorm_norm _ (hu i).aestronglyMeasurable,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (hC i)]
  calc
    _ ≤ (eLpNorm (∑ i, N i) 2 μ).toReal :=
      ENNReal.toReal_mono hsum.ne (eLpNorm_mono_ae hg hdom)
    _ ≤ ∑ i, (eLpNorm (N i) 2 μ).toReal := htriangle
    _ = _ := Finset.sum_congr rfl fun i _ => hscale i

end ContinuousFlexibility.Analysis
