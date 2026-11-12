import ContinuousFlexibility.Analysis.N05OpticalPrimitive
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# A polynomial bound from the actual optical integral

A nonnegative Lipschitz function vanishing at the left endpoint has a
controlled plateau immediately before any point. Integrating its square
root on that plateau gives a lower bound for the actual optical travel.
After the Tricomi time normalization, only a first power of a Lipschitz
constant at least one is needed to bound the radicand divided by radius.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory

/-- A genuine interval integral controls the endpoint value. The proof
uses a plateau of length `f b / (2 * L)` and no fractional-power formula. -/
theorem n05_lipschitz_sqrt_integral_lower
    {f : ℝ → ℝ} {a b : ℝ} {L : NNReal} (hab : a ≤ b) (hL : 0 < (L : ℝ))
    (hf : LipschitzOnWith L f (Icc a b))
    (hzero : f a = 0) (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x) :
    f b * Real.sqrt (f b) ≤
      4 * (L : ℝ) * ∫ x in a..b, Real.sqrt (f x) := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hfb : 0 ≤ f b := hnonneg b hb
  have hbLip : f b ≤ (L : ℝ) * (b - a) := by
    have ht := hf.dist_le_mul b hb a ha
    simpa only [Real.dist_eq, hzero, sub_zero, abs_of_nonneg hfb,
      abs_of_nonneg (sub_nonneg.mpr hab)] using ht
  let δ := f b / (2 * (L : ℝ))
  let c := b - δ
  have hδ0 : 0 ≤ δ := div_nonneg hfb (by positivity)
  have hδmul : δ * (2 * (L : ℝ)) = f b :=
    div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hL.ne')
  have hδle : δ ≤ b - a := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (L : ℝ))).mpr
    have hw := mul_nonneg hL.le (sub_nonneg.mpr hab)
    nlinarith only [hbLip, hw]
  have hac : a ≤ c := by dsimp only [c]; linarith only [hδle]
  have hcb : c ≤ b := by dsimp only [c]; linarith only [hδ0]
  have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc hac le_rfl
  have hfloor (x : ℝ) (hx : x ∈ Icc c b) :
      Real.sqrt (f b) / 2 ≤ Real.sqrt (f x) := by
    have ht := hf.dist_le_mul b hb x (hsub hx)
    simp only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.2)] at ht
    have hd : f b - f x ≤ (L : ℝ) * (b - x) := (le_abs_self _).trans ht
    have hspan : b - x ≤ δ := by
      have hc := hx.1
      dsimp only [c] at hc
      linarith only [hc]
    have hm := mul_le_mul_of_nonneg_left hspan hL.le
    have hhalf : f b / 2 ≤ f x := by nlinarith only [hd, hm, hδmul]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [Real.sq_sqrt hfb, hhalf, hfb]
  have hg : ContinuousOn (fun x => Real.sqrt (f x)) (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn hf.continuousOn
  have hi : IntervalIntegrable (fun x => Real.sqrt (f x)) volume a b :=
    hg.intervalIntegrable_of_Icc hab
  have hplateau : (b - c) * (Real.sqrt (f b) / 2) ≤
      ∫ x in c..b, Real.sqrt (f x) := by
    have ht := intervalIntegral.integral_mono_on hcb
      ((show Continuous (fun _ : ℝ => Real.sqrt (f b) / 2) from continuous_const).intervalIntegrable c b)
      ((hg.mono hsub).intervalIntegrable_of_Icc hcb) hfloor
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using ht
  have hpiece : (∫ x in c..b, Real.sqrt (f x)) ≤
      ∫ x in a..b, Real.sqrt (f x) :=
    intervalIntegral.integral_mono_interval hac hcb le_rfl
      (Eventually.of_forall fun _ => Real.sqrt_nonneg _) hi
  have hlen : b - c = δ := by dsimp only [c]; ring
  have hmain : δ * (Real.sqrt (f b) / 2) ≤
      ∫ x in a..b, Real.sqrt (f x) := by
    simpa only [hlen] using hplateau.trans hpiece
  calc
    f b * Real.sqrt (f b) = (δ * (2 * (L : ℝ))) * Real.sqrt (f b) := by rw [hδmul]
    _ = (4 * (L : ℝ)) * (δ * (Real.sqrt (f b) / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain (by positivity)

/-- The exact Tricomi time identity turns the optical lower bound into a
coarse coefficient-power bound, without a lower bound for the root slope. -/
theorem n05_optical_radicand_le_radius
    {f : ℝ → ℝ} {a b ξ : ℝ} {L : NNReal} (hab : a ≤ b) (hL : 1 ≤ (L : ℝ))
    (hf : LipschitzOnWith L f (Icc a b))
    (hzero : f a = 0) (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x) (hξ : 0 ≤ ξ)
    (htime : (∫ x in a..b, Real.sqrt (f x)) = (2 / 3 : ℝ) * ξ * Real.sqrt ξ) :
    f b ≤ 4 * (L : ℝ) * ξ := by
  have hLp : 0 < (L : ℝ) := zero_lt_one.trans_le hL
  have hfb : 0 ≤ f b := hnonneg b (right_mem_Icc.mpr hab)
  have hbound := n05_lipschitz_sqrt_integral_lower hab hLp hf hzero hnonneg
  rw [htime] at hbound
  have htime_le : (2 / 3 : ℝ) * ξ * Real.sqrt ξ ≤ ξ * Real.sqrt ξ := by
    nlinarith only [mul_nonneg hξ (Real.sqrt_nonneg ξ)]
  have hrough : f b * Real.sqrt (f b) ≤
      (4 * (L : ℝ)) * (ξ * Real.sqrt ξ) :=
    hbound.trans (mul_le_mul_of_nonneg_left htime_le (by positivity))
  have hcube : f b ^ 3 ≤ 16 * (L : ℝ) ^ 2 * ξ ^ 3 := by
    calc
      f b ^ 3 = (f b * Real.sqrt (f b)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hfb]
        ring
      _ ≤ ((4 * (L : ℝ)) * (ξ * Real.sqrt ξ)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hfb (Real.sqrt_nonneg _)) hrough 2
      _ = 16 * (L : ℝ) ^ 2 * ξ ^ 3 := by
        simp only [mul_pow, Real.sq_sqrt hξ]
        ring
  have hLpow : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 3 := by
    calc
      (L : ℝ) ^ 2 = (L : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (L : ℝ) ^ 2 * L := mul_le_mul_of_nonneg_left hL (sq_nonneg _)
      _ = (L : ℝ) ^ 3 := by ring
  apply (pow_le_pow_iff_left₀ hfb (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp
  calc
    f b ^ 3 ≤ 16 * (L : ℝ) ^ 2 * ξ ^ 3 := hcube
    _ ≤ 16 * (L : ℝ) ^ 3 * ξ ^ 3 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLpow (by norm_num)) (pow_nonneg hξ 3)
    _ ≤ 64 * (L : ℝ) ^ 3 * ξ ^ 3 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (16 : ℝ) ≤ 64)
          (pow_nonneg hLp.le 3)) (pow_nonneg hξ 3)
    _ = (4 * (L : ℝ) * ξ) ^ 3 := by ring

/-- In the canonical interior the radicand-to-radius ratio has the same
polynomial bound. This is the ratio appearing in the exact negative symbol. -/
theorem n05_optical_radicand_div_radius_le
    {f : ℝ → ℝ} {a b ξ : ℝ} {L : NNReal} (hab : a ≤ b) (hL : 1 ≤ (L : ℝ))
    (hf : LipschitzOnWith L f (Icc a b))
    (hzero : f a = 0) (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x) (hξ : 0 < ξ)
    (htime : (∫ x in a..b, Real.sqrt (f x)) = (2 / 3 : ℝ) * ξ * Real.sqrt ξ) :
    f b / ξ ≤ 4 * (L : ℝ) :=
  (div_le_iff₀ hξ).mpr
    (n05_optical_radicand_le_radius hab hL hf hzero hnonneg hξ.le htime)

end ContinuousFlexibility.Statements
