import ContinuousFlexibility.Analysis.IntervalSobolevCutoff
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Ring

/-!
# Sobolev bounds for the interval cutoff

Leibniz's formula bounds the half-line derivative of order `n` by a finite
sum of the original interval derivatives of orders at most `n`. The estimate
is proved in the actual Lebesgue `Lᵖ` seminorm and applies in particular to
`p = 2` at every Sobolev level.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The cutoff jet vanishes beyond the original interval, so restricting
its half-line norm to the interval leaves the norm unchanged. -/
theorem eLpNorm_cutoffHalfLine_jet_eq_interval {L c : ℝ} (hc : c < L)
    {χ : ℝ → ℝ} (hzero : ∀ y, c ≤ y → χ y = 0) (f : ℝ → F)
    (n : ℕ) (p : ℝ≥0∞) :
    eLpNorm (iteratedDerivWithin n (cutoffHalfLine χ f) (Ici 0)) p
        (volume.restrict (Ici 0)) =
      eLpNorm (iteratedDerivWithin n (cutoffHalfLine χ f) (Ici 0)) p
        (volume.restrict (Icc 0 L)) := by
  let g : ℝ → F := iteratedDerivWithin n (cutoffHalfLine χ f) (Ici 0)
  have he : g =ᵐ[volume.restrict (Ici 0)] (Icc 0 L).indicator g := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    by_cases hxL : x ≤ L
    · exact (Set.indicator_of_mem ⟨hx, hxL⟩ g).symm
    · have hnot : x ∉ Icc 0 L := fun h => hxL h.2
      rw [Set.indicator_of_notMem hnot g]
      exact iteratedDerivWithin_cutoffHalfLine_zero f hzero
        (hc.trans (lt_of_not_ge hxL)) n (Ici 0)
  calc
    eLpNorm g p (volume.restrict (Ici 0)) =
        eLpNorm ((Icc 0 L).indicator g) p (volume.restrict (Ici 0)) := eLpNorm_congr_ae he
    _ = eLpNorm g p (volume.restrict (Icc 0 L)) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc,
        Measure.restrict_restrict_of_subset Icc_subset_Ici_self]

private theorem cutoff_leibniz_term_norm_le (n i : ℕ) (u : ℝ) (v : F)
    {M : ℝ} (hM : ‖u‖ ≤ M) :
    ‖n.choose i • u • v‖ ≤ ((n.choose i : ℝ) * M) * ‖v‖ := by
  calc
    ‖n.choose i • u • v‖ ≤ (n.choose i : ℝ) * ‖u • v‖ := norm_nsmul_le
    _ = ((n.choose i : ℝ) * ‖u‖) * ‖v‖ := by rw [norm_smul]; ring
    _ ≤ ((n.choose i : ℝ) * M) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg _)) (norm_nonneg _)

/-- The exact finite derivative bound, with constants depending only on
the fixed cutoff and on the derivative order. -/
theorem eLpNorm_cutoffHalfLine_jet_le {L c : ℝ} (hL : 0 < L) (hc : c < L)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ y, c ≤ y → χ y = 0)
    {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Icc 0 L))
    (M : ℕ → ℝ) (hM : ∀ i x, ‖iteratedDeriv i χ x‖ ≤ M i)
    (n : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (iteratedDerivWithin n (cutoffHalfLine χ f) (Ici 0)) p
        (volume.restrict (Ici 0)) ≤
      ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal ((n.choose i : ℝ) * M i) *
        eLpNorm (iteratedDerivWithin (n - i) f (Icc 0 L)) p
          (volume.restrict (Icc 0 L)) := by
  let T : ℕ → ℝ → F := fun i x => n.choose i •
    iteratedDeriv i χ x • iteratedDerivWithin (n - i) f (Icc 0 L) x
  have hT (i : ℕ) : AEStronglyMeasurable (T i) (volume.restrict (Icc 0 L)) := by
    have hi : ContinuousOn (T i) (Icc 0 L) :=
      (((hχ.continuous_iteratedDeriv i (by simp)).continuousOn).smul
        (hf.continuousOn_iteratedDerivWithin (by simp) (uniqueDiffOn_Icc hL)))
        .const_smul (n.choose i)
    exact hi.aestronglyMeasurable measurableSet_Icc
  have he : iteratedDerivWithin n (cutoffHalfLine χ f) (Ici 0)
      =ᵐ[volume.restrict (Icc 0 L)] ∑ i ∈ Finset.range (n + 1), T i := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simpa only [Finset.sum_apply, T] using
      iteratedDerivWithin_cutoffHalfLine hL hc hχ hzero hf n hx
  rw [eLpNorm_cutoffHalfLine_jet_eq_interval hc hzero f n p, eLpNorm_congr_ae he]
  refine (eLpNorm_sum_le hp).trans (Finset.sum_le_sum (fun i hi => ?_))
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hT i)
  filter_upwards [] with x
  exact cutoff_leibniz_term_norm_le n i _ _ (hM i x)

theorem memLp_cutoffHalfLine_jet {L c : ℝ} (hL : 0 < L) (hc : c < L)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ y, c ≤ y → χ y = 0)
    {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Icc 0 L))
    (M : ℕ → ℝ) (hM : ∀ i x, ‖iteratedDeriv i χ x‖ ≤ M i)
    (n : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hfp : ∀ k ≤ n, MemLp (iteratedDerivWithin k f (Icc 0 L)) p
      (volume.restrict (Icc 0 L))) :
    MemLp (iteratedDerivWithin n (cutoffHalfLine χ f) (Ici 0)) p
      (volume.restrict (Ici 0)) := by
  apply memLp_iff.mpr
  refine (eLpNorm_cutoffHalfLine_jet_le hL hc hχ hzero hf M hM n p hp).trans_lt ?_
  apply ENNReal.sum_lt_top.mpr
  intro i _
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (hfp (n - i) (Nat.sub_le n i)).eLpNorm_lt_top

/-- The same estimate in real-valued norms, suitable for normed Sobolev
cores and their completions. -/
theorem cutoffHalfLine_jet_norm_le {L c : ℝ} (hL : 0 < L) (hc : c < L)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ y, c ≤ y → χ y = 0)
    {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Icc 0 L))
    (M : ℕ → ℝ) (hM : ∀ i x, ‖iteratedDeriv i χ x‖ ≤ M i)
    (n : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hfp : ∀ k ≤ n, MemLp (iteratedDerivWithin k f (Icc 0 L)) p
      (volume.restrict (Icc 0 L))) :
    (eLpNorm (iteratedDerivWithin n (cutoffHalfLine χ f) (Ici 0)) p
        (volume.restrict (Ici 0))).toReal ≤
      ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * M i) *
        (eLpNorm (iteratedDerivWithin (n - i) f (Icc 0 L)) p
          (volume.restrict (Icc 0 L))).toReal := by
  have hfin (i : ℕ) : ENNReal.ofReal ((n.choose i : ℝ) * M i) *
      eLpNorm (iteratedDerivWithin (n - i) f (Icc 0 L)) p
        (volume.restrict (Icc 0 L)) ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (hfp (n - i) (Nat.sub_le n i)).eLpNorm_ne_top
  calc
    (eLpNorm (iteratedDerivWithin n (cutoffHalfLine χ f) (Ici 0)) p
        (volume.restrict (Ici 0))).toReal ≤
        (∑ i ∈ Finset.range (n + 1), ENNReal.ofReal ((n.choose i : ℝ) * M i) *
          eLpNorm (iteratedDerivWithin (n - i) f (Icc 0 L)) p
            (volume.restrict (Icc 0 L))).toReal :=
      ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hfin i))
        (eLpNorm_cutoffHalfLine_jet_le hL hc hχ hzero hf M hM n p hp)
    _ = _ := by
      rw [ENNReal.toReal_sum (fun i _ => hfin i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (hM i 0)))]

end ContinuousFlexibility.Analysis
