import ContinuousFlexibility.Analysis.N06RootSpeedJets
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Actual finite jets of the fractional powers used in the root germ

Both the value and reciprocal of the positive input are bounded. This
controls the actual powers through exponents three, so the chain rule
gives a fixed polynomial estimate for all powers in `[-1,1]`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n06_rpow_le_pow_of_abs_le
    {u B a : ℝ} (hu : 0 < u) (hB : 1 ≤ B) (huB : u ≤ B) (hui : u⁻¹ ≤ B)
    (n : ℕ) (ha : |a| ≤ n) : u ^ a ≤ B ^ n := by
  have hpos {v p : ℝ} (hv : 0 ≤ v) (hvB : v ≤ B) (hp : 0 ≤ p) (hpn : p ≤ n) :
      v ^ p ≤ B ^ n := by
    calc
      v ^ p ≤ B ^ p := Real.rpow_le_rpow hv hvB hp
      _ ≤ B ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hB hpn
      _ = B ^ n := Real.rpow_natCast _ _
  by_cases hapos : 0 ≤ a
  · exact hpos hu.le huB hapos ((le_abs_self _).trans ha)
  · have he : u ^ a = (u⁻¹) ^ (-a) := by
      rw [Real.inv_rpow hu.le, Real.rpow_neg hu.le, inv_inv]
    rw [he]
    exact hpos (inv_nonneg.mpr hu.le) hui (neg_nonneg.mpr (lt_of_not_ge hapos).le)
      ((neg_le_abs a).trans ha)

/-- A local ordinary two-jet bound for every fixed fractional power used
by the actual Airy slope and height formulas. -/
theorem N06ScalarJetTwoBound.rpow_unit_at
    {f : ℝ → ℝ} {x B a : ℝ} (hf : ContDiffAt ℝ ∞ f x)
    (hpos : 0 < f x) (hB : 1 ≤ B) (hfb : N06ScalarJetTwoBound f x B)
    (hinv : (f x)⁻¹ ≤ B) (ha : |a| ≤ 1) :
    N06ScalarJetTwoBound (fun t => f t ^ a) x (3 * B ^ 5) ∧
      ((f x) ^ a)⁻¹ ≤ B := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hvalue : (f x) ^ a ≤ B := by
    simpa only [pow_one] using n06_rpow_le_pow_of_abs_le hpos hB
      ((le_abs_self _).trans hfb.value) hinv 1 (by simpa only [Nat.cast_one] using ha)
  have ha₁ : |a - 1| ≤ 2 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp ha
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have ha₂ : |a - 2| ≤ 3 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp ha
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hpow₁ : (f x) ^ (a - 1) ≤ B ^ 2 :=
    n06_rpow_le_pow_of_abs_le hpos hB ((le_abs_self _).trans hfb.value) hinv 2 ha₁
  have hpow₂ : (f x) ^ (a - 2) ≤ B ^ 3 :=
    n06_rpow_le_pow_of_abs_le hpos hB ((le_abs_self _).trans hfb.value) hinv 3 ha₂
  have hcoeff : |a * (a - 1)| ≤ 2 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul ha ha₁ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hder : deriv (fun t => f t ^ a) x = deriv f x * a * f x ^ (a - 1) :=
    ((hf.differentiableAt (by simp)).hasDerivAt.rpow_const (Or.inl hpos.ne')).deriv
  have houter : deriv (deriv (fun t : ℝ => t ^ a)) (f x) =
      a * (a - 1) * f x ^ (a - 2) := by
    rw [Real.deriv_rpow_const', deriv_const_mul_field, Real.deriv_rpow_const]
    rw [show a - 1 - 1 = a - 2 by ring]
    ring
  have hsecond : deriv (deriv (fun t => f t ^ a)) x =
      (a * (a - 1) * f x ^ (a - 2)) * deriv f x ^ 2 +
        (a * f x ^ (a - 1)) * deriv (deriv f) x := by
    have he := iteratedDeriv_comp_two
      (Real.contDiffAt_rpow_const_of_ne hpos.ne' :
        ContDiffAt ℝ 2 (fun t : ℝ => t ^ a) (f x)) (hf.of_le (by simp))
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_zero, Function.comp_def, houter, Real.deriv_rpow_const] using he
  have hfirst : |deriv (fun t => f t ^ a) x| ≤ B ^ 3 := by
    rw [hder, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    calc
      _ ≤ (B * 1) * B ^ 2 :=
        mul_le_mul (mul_le_mul hfb.first ha (abs_nonneg _) hB0) hpow₁
          (Real.rpow_nonneg hpos.le _) (by positivity)
      _ = B ^ 3 := by ring
  have hB15 : B ≤ B ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 5)
  have hB35 : B ^ 3 ≤ B ^ 5 := pow_le_pow_right₀ hB (by norm_num)
  have hB5 := pow_nonneg hB0 5
  have hi : ((f x) ^ a)⁻¹ ≤ B := by
    rw [← Real.rpow_neg hpos.le]
    simpa only [pow_one] using n06_rpow_le_pow_of_abs_le hpos hB
      ((le_abs_self _).trans hfb.value) hinv 1
        (by simpa only [Nat.cast_one, abs_neg] using ha)
  refine ⟨⟨?_, hfirst.trans (by nlinarith), ?_⟩, hi⟩
  · rw [abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    exact hvalue.trans (by nlinarith)
  · rw [hsecond]
    have h₁ : |(a * (a - 1) * f x ^ (a - 2)) * deriv f x ^ 2| ≤ 2 * B ^ 5 := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _), abs_pow]
      calc
        _ ≤ (2 * B ^ 3) * B ^ 2 := mul_le_mul
          (mul_le_mul hcoeff hpow₂ (Real.rpow_nonneg hpos.le _) (by norm_num))
          (pow_le_pow_left₀ (abs_nonneg _) hfb.first 2) (sq_nonneg _) (by positivity)
        _ = 2 * B ^ 5 := by ring
    have h₂ : |(a * f x ^ (a - 1)) * deriv (deriv f) x| ≤ B ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
      calc
        _ ≤ (1 * B ^ 2) * B := mul_le_mul
          (mul_le_mul ha hpow₁ (Real.rpow_nonneg hpos.le _) (by norm_num)) hfb.second
          (abs_nonneg _) (by positivity)
        _ = B ^ 3 := by ring
    exact ((abs_add_le _ _).trans (add_le_add h₁ h₂)).trans (by nlinarith)

end ContinuousFlexibility.Analysis
