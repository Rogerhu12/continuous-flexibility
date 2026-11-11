import ContinuousFlexibility.Analysis.N07aCanonicalJetRealization
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Quantitative bounds for the actual canonical jet arrays

The exact canonical rectangle measure supplies its square-root factor.
Finite jet arrays and the outer square-summable sequence retain explicit
bounds, which are applied to the complete sampled source envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped BigOperators

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonicalMeasure_univ (hm : K.left m < K.right m) :
    canonicalMeasure S K m univ = ENNReal.ofReal (Real.pi * (K.right m - K.left m)) := by
  rw [canonicalMeasure, Measure.restrict_apply_univ, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioc, sub_zero,
    ← ENNReal.ofReal_mul (sub_pos.mpr hm).le]
  congr 1
  ring

theorem N07aCanonicalOpenCoefficient.toLp_norm_le
    (χ : N07aCanonicalOpenCoefficient S K m) (hm : K.left m < K.right m)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ p ∂canonicalMeasure S K m, |χ.value p| ≤ C) :
    ‖χ.toLp‖ ≤ Real.sqrt (Real.pi * (K.right m - K.left m)) * C := by
  have hn : ∀ᵐ p ∂canonicalMeasure S K m, ‖χ.value p‖ ≤ C := by
    simpa only [Real.norm_eq_abs] using hb
  have he := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞))
    (n07a_canonicalOpen_aestronglyMeasurable χ.smooth.continuousOn) hn
  rw [n07a_canonicalMeasure_univ hm] at he
  have htop : ENNReal.ofReal (Real.pi * (K.right m - K.left m)) ^
      (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal C ≠ ⊤ := by finiteness
  have h := ENNReal.toReal_mono htop he
  have hlen : 0 ≤ Real.pi * (K.right m - K.left m) :=
    mul_nonneg Real.pi_pos.le (sub_pos.mpr hm).le
  rw [toLp, Lp.norm_toLp]
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hlen, ENNReal.toReal_ofReal hC,
    ENNReal.toReal_ofNat, Real.sqrt_eq_rpow, one_div] using h

theorem n07a_piLp_two_norm_le_sum_norm
    {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (v : PiLp 2 E) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  apply (sq_le_sq₀ (norm_nonneg v) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

theorem n07a_lp_of_square_majorant
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (v : ∀ i, E i) (w : ι → ℝ) (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, ‖v i‖ ^ 2 ≤ w i * B ^ 2) :
    ∃ hu : Memℓp v 2,
      ‖(⟨v, hu⟩ : lp E 2)‖ ≤ Real.sqrt (∑' i, w i) * B := by
  have hs : Summable (fun i => ‖v i‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb (hw.mul_right (B ^ 2))
  have hm : Memℓp v 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs
  let u : lp E 2 := ⟨v, hm⟩
  refine ⟨hm, ?_⟩
  apply lp.norm_le_of_tsum_le (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    (mul_nonneg (Real.sqrt_nonneg _) hB)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc
    ∑' i, ‖u i‖ ^ 2 ≤ ∑' i, w i * B ^ 2 :=
      hs.tsum_le_tsum hb (hw.mul_right (B ^ 2))
    _ = (∑' i, w i) * B ^ 2 := tsum_mul_right
    _ = (Real.sqrt (∑' i, w i) * B) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (tsum_nonneg hw0)]

end ContinuousFlexibility.Analysis
