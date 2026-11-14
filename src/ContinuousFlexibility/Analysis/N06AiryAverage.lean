module

public import ContinuousFlexibility.Analysis.SmoothScaledIntegral
public import ContinuousFlexibility.Analysis.N06RootSpeedJets
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The actual averaged coefficient of the two-sided reference Airy germ

The square-root weight is a convenient form of the quadratic root-flow
integral. Its finite jets follow from the existing scaled-integral formula.
An actual fundamental-theorem calculation gives the differential identity
that makes the radial coordinate nondegenerate on both sides of the root.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Real
open scoped ContDiff Topology Interval

set_option backward.isDefEq.respectTransparency false

def n06AiryAverage (c : ℝ → ℝ) (x : ℝ) : ℝ :=
  (3 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, Real.sqrt t * c (t * x)

theorem n06_contDiff_airyAverage {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (n06AiryAverage c) :=
  contDiff_const.mul (contDiff_scaled_intervalIntegral Real.continuous_sqrt hc)

theorem n06_iteratedDeriv_airyAverage {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (n06AiryAverage c) x =
      (3 / 2 : ℝ) * ∫ t in (0 : ℝ)..1,
        Real.sqrt t * t ^ n * iteratedDeriv n c (t * x) := by
  rw [show n06AiryAverage c =
      (fun y => (3 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, Real.sqrt t * c (t * y)) from rfl,
    iteratedDeriv_const_mul_field,
    iteratedDeriv_scaled_intervalIntegral Real.continuous_sqrt hc n]

theorem n06_deriv_airyAverage {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (x : ℝ) :
    deriv (n06AiryAverage c) x =
      (3 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, Real.sqrt t * t * deriv c (t * x) := by
  simpa only [iteratedDeriv_one, pow_one] using n06_iteratedDeriv_airyAverage hc 1 x

/-- The weight has exactly unit mass after the displayed normalization. -/
theorem n06_airy_weight_mass :
    (3 / 2 : ℝ) * (∫ t in (0 : ℝ)..1, Real.sqrt t) = 1 := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ (3 / 2 : ℝ))
      ((3 / 2 : ℝ) * Real.sqrt t) t := by
    simpa only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] using
      (Real.hasDerivAt_rpow_const (x := t) (p := (3 / 2 : ℝ))
        (Or.inr (by norm_num)))
  have hi : IntervalIntegrable (fun t : ℝ => (3 / 2 : ℝ) * Real.sqrt t) volume 0 1 :=
    (continuous_const.mul Real.continuous_sqrt).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa only [intervalIntegral.integral_const_mul, Real.one_rpow,
    Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), sub_zero] using he

/-- Pointwise lower bounds are preserved by the actual positive average. -/
theorem n06_airyAverage_lower {c : ℝ → ℝ} (hc : Continuous c)
    (m : ℝ) (hlower : ∀ x : ℝ, m ≤ c x) (x : ℝ) :
    m ≤ n06AiryAverage c x := by
  have h₁ : IntervalIntegrable (fun t : ℝ => Real.sqrt t * m) volume 0 1 :=
    (Real.continuous_sqrt.mul_const m).intervalIntegrable 0 1
  have h₂ : IntervalIntegrable (fun t : ℝ => Real.sqrt t * c (t * x)) volume 0 1 :=
    (Real.continuous_sqrt.mul (hc.comp (continuous_id.mul_const x))).intervalIntegrable 0 1
  have hi := intervalIntegral.integral_mono_on zero_le_one h₁ h₂
    (fun t _ => mul_le_mul_of_nonneg_left (hlower (t * x)) (Real.sqrt_nonneg t))
  have hm := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [intervalIntegral.integral_mul_const] at hm
  have he : (3 / 2 : ℝ) * ((∫ t in (0 : ℝ)..1, Real.sqrt t) * m) = m := by
    rw [← mul_assoc, n06_airy_weight_mass, one_mul]
  simpa only [he, n06AiryAverage] using hm

/-- The normalized average loses no ordinary derivative; a fixed factor
two bounds every finite-order jet from the corresponding actual input jet. -/
theorem n06_airyAverage_jet_bound {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x : ℝ, |iteratedDeriv n c x| ≤ M) (x : ℝ) :
    |iteratedDeriv n (n06AiryAverage c) x| ≤ 2 * M := by
  rw [n06_iteratedDeriv_airyAverage hc n x, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hb (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      ‖Real.sqrt t * t ^ n * iteratedDeriv n c (t * x)‖ ≤ M := by
    have hs0 := Real.sqrt_nonneg t
    have hs1 : Real.sqrt t ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht.2
    have hp0 := pow_nonneg ht.1.le n
    have hp1 := pow_le_one₀ ht.1.le ht.2 (n := n)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg hp0]
    have hw : Real.sqrt t * t ^ n ≤ 1 := by
      simpa only [one_mul] using mul_le_mul hs1 hp1 hp0 (by norm_num : (0 : ℝ) ≤ 1)
    calc
      _ ≤ (Real.sqrt t * t ^ n) * M :=
        mul_le_mul_of_nonneg_left (hbound (t * x)) (mul_nonneg hs0 hp0)
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right hw hM
      _ = M := one_mul _
  have hi := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall hb)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 1)
  have hi' : |∫ t in (0 : ℝ)..1,
      Real.sqrt t * t ^ n * iteratedDeriv n c (t * x)| ≤ M := by
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_const, sub_zero, one_smul] using hi
  exact (mul_le_mul_of_nonneg_left hi' (by norm_num : (0 : ℝ) ≤ 3 / 2)).trans
    (by nlinarith only [hM])

theorem n06_airyAverage_twoJet_bound {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    {B : ℝ} (hB : 1 ≤ B) (hjet : ∀ x, N06ScalarJetTwoBound c x B)
    (hpos : ∀ x, 0 < c x) (hinv : ∀ x, (c x)⁻¹ ≤ B) (x : ℝ) :
    0 < n06AiryAverage c x ∧
      N06ScalarJetTwoBound (n06AiryAverage c) x (2 * B) ∧
      (n06AiryAverage c x)⁻¹ ≤ B := by
  have hBp := zero_lt_one.trans_le hB
  have hlower : B⁻¹ ≤ n06AiryAverage c x := n06_airyAverage_lower hc.continuous B⁻¹
    (fun y => inv_le_of_inv_le₀ (hpos y) (hinv y)) x
  have hp := (inv_pos.mpr hBp).trans_le hlower
  have hi : (n06AiryAverage c x)⁻¹ ≤ B := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hBp) hlower
  refine ⟨hp, n06_scalarJetTwoBound_iff.mpr ?_, hi⟩
  intro n hn
  exact n06_airyAverage_jet_bound hc n (zero_le_one.trans hB)
    (fun y => n06_scalarJetTwoBound_iff.mp (hjet y) n hn) x

/-- The actual integral satisfies the Euler identity on the entire line.
It gives the positive slope of the new two-sided reference germ. -/
theorem n06_airyAverage_euler {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) (x : ℝ) :
    n06AiryAverage c x + (2 / 3 : ℝ) * x * deriv (n06AiryAverage c) x = c x := by
  have hcd : ContDiff ℝ ∞ (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
  let F : ℝ → ℝ := fun t => t ^ (3 / 2 : ℝ) * c (t * x)
  let F' : ℝ → ℝ := fun t =>
    (3 / 2 : ℝ) * (Real.sqrt t * c (t * x)) +
      x * (Real.sqrt t * t * deriv c (t * x))
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : HasDerivAt F (F' t) t := by
    have ht0 : 0 ≤ t := (uIcc_of_le (show (0 : ℝ) ≤ 1 from zero_le_one) ▸ ht).1
    have hp : t ^ (3 / 2 : ℝ) = Real.sqrt t * t := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
        Real.rpow_add' ht0 (by norm_num : (1 / 2 : ℝ) + 1 ≠ 0),
        ← Real.sqrt_eq_rpow, Real.rpow_one]
    have hp' := Real.hasDerivAt_rpow_const (x := t) (p := (3 / 2 : ℝ))
      (Or.inr (by norm_num))
    have hc' := (hc.differentiable (by simp) (t * x)).hasDerivAt.comp t
      (hasDerivAt_mul_const x)
    have hh := hp'.mul hc'
    apply hh.congr_deriv
    dsimp only [F', Function.comp_apply]
    rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, hp]
    ring
  have h₁ : IntervalIntegrable
      (fun t : ℝ => (3 / 2 : ℝ) * (Real.sqrt t * c (t * x))) volume 0 1 :=
    (continuous_const.mul
      (Real.continuous_sqrt.mul (hc.continuous.comp (continuous_id.mul_const x)))).intervalIntegrable 0 1
  have h₂ : IntervalIntegrable
      (fun t : ℝ => x * (Real.sqrt t * t * deriv c (t * x))) volume 0 1 :=
    (continuous_const.mul ((Real.continuous_sqrt.mul continuous_id).mul
      (hcd.continuous.comp (continuous_id.mul_const x)))).intervalIntegrable 0 1
  have hI : IntervalIntegrable F' volume 0 1 := h₁.add h₂
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hI
  change (∫ t in (0 : ℝ)..1,
    (3 / 2 : ℝ) * (Real.sqrt t * c (t * x)) +
      x * (Real.sqrt t * t * deriv c (t * x))) = F 1 - F 0 at he
  rw [intervalIntegral.integral_add h₁ h₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at he
  simp only [F, Real.one_rpow, one_mul, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0),
    zero_mul, sub_zero] at he
  rw [n06_deriv_airyAverage hc]
  change (3 / 2 : ℝ) * (∫ t in (0 : ℝ)..1, Real.sqrt t * c (t * x)) +
      (2 / 3 : ℝ) * x * ((3 / 2 : ℝ) *
        ∫ t in (0 : ℝ)..1, Real.sqrt t * t * deriv c (t * x)) = c x
  nlinarith only [he]

/-- The weighted average is precisely the original quadratic root-flow
integral, by the genuine substitution `s = t²`. -/
theorem n06_airyAverage_eq_quadratic {c : ℝ → ℝ} (hc : Continuous c) (x : ℝ) :
    n06AiryAverage c x = 3 * ∫ t in (0 : ℝ)..1, t ^ 2 * c (x * t ^ 2) := by
  let g : ℝ → ℝ := fun s => Real.sqrt s * c (s * x)
  have hg : Continuous g := Real.continuous_sqrt.mul
    (hc.comp (continuous_id.mul_const x))
  have hd (t : ℝ) (_ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa only [Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 from rfl, pow_one] using hasDerivAt_pow 2 t
  have hsub := intervalIntegral.integral_comp_mul_deriv hd
    ((continuous_const.mul continuous_id).continuousOn :
      ContinuousOn (fun t : ℝ => 2 * t) (uIcc 0 1)) hg
  have hEq : (∫ t in (0 : ℝ)..1, (g ∘ fun s : ℝ => s ^ 2) t * (2 * t)) =
      2 * ∫ t in (0 : ℝ)..1, t ^ 2 * c (x * t ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := (uIcc_of_le (show (0 : ℝ) ≤ 1 from zero_le_one) ▸ ht).1
    simp only [Function.comp_apply, g, Real.sqrt_sq ht0]
    rw [mul_comm (t ^ 2) x]
    ring
  have hvalue : (∫ s in (0 : ℝ)..1, Real.sqrt s * c (s * x)) =
      2 * ∫ t in (0 : ℝ)..1, t ^ 2 * c (x * t ^ 2) := by
    simpa only [g, zero_pow (by norm_num : (2 : ℕ) ≠ 0), one_pow] using hsub.symm.trans hEq
  rw [n06AiryAverage, hvalue]
  ring

end ContinuousFlexibility.Analysis
