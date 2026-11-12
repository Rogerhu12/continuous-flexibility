import ContinuousFlexibility.Analysis.N06RadialReferenceGeometry
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Finite scalar jet bounds for radial reference geometry

These elementary estimates control products, compositions, and reciprocals
of the primitive radial functions through order two. They use actual
derivatives and retain explicit polynomial constants.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

structure N06ScalarJetTwoBound (f : ℝ → ℝ) (x B : ℝ) : Prop where
  value : |f x| ≤ B
  first : |deriv f x| ≤ B
  second : |deriv (deriv f) x| ≤ B

theorem N06ScalarJetTwoBound.mono {f : ℝ → ℝ} {x B C : ℝ}
    (h : N06ScalarJetTwoBound f x B) (hBC : B ≤ C) :
    N06ScalarJetTwoBound f x C :=
  ⟨h.value.trans hBC, h.first.trans hBC, h.second.trans hBC⟩

theorem n06_deriv_two_mul {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : ℝ) :
    deriv (deriv (fun t => f t * g t)) x =
      deriv (deriv f) x * g x + deriv f x * deriv g x +
        (deriv f x * deriv g x + f x * deriv (deriv g) x) := by
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have hfirst : deriv (fun t => f t * g t) =
      fun t => deriv f t * g t + f t * deriv g t := by
    funext t
    exact deriv_fun_mul (hf.differentiable (by simp) t) (hg.differentiable (by simp) t)
  rw [hfirst]
  have hsum : HasDerivAt (fun t => deriv f t * g t + f t * deriv g t)
      (deriv (deriv f) x * g x + deriv f x * deriv g x +
        (deriv f x * deriv g x + f x * deriv (deriv g) x)) x :=
    (((hf'.differentiable (by simp) x).hasDerivAt.mul
      (hg.differentiable (by simp) x).hasDerivAt).add
      ((hf.differentiable (by simp) x).hasDerivAt.mul
        (hg'.differentiable (by simp) x).hasDerivAt))
  exact hsum.deriv

theorem N06ScalarJetTwoBound.mul
    {f g : ℝ → ℝ} {x B C : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfb : N06ScalarJetTwoBound f x B) (hgb : N06ScalarJetTwoBound g x C) :
    N06ScalarJetTwoBound (fun t => f t * g t) x (4 * B * C) := by
  have hmul {u v : ℝ} (hu : |u| ≤ B) (hv : |v| ≤ C) : |u * v| ≤ B * C := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg _) hB
  have hBC : 0 ≤ B * C := mul_nonneg hB hC
  constructor
  · exact (hmul hfb.value hgb.value).trans (by nlinarith)
  · rw [deriv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
    have hb := (abs_add_le _ _).trans
      (add_le_add (hmul hfb.first hgb.value) (hmul hfb.value hgb.first))
    nlinarith
  · rw [n06_deriv_two_mul hf hg]
    have hb := (abs_add_le _ _).trans
      (add_le_add
        ((abs_add_le _ _).trans
          (add_le_add (hmul hfb.second hgb.value) (hmul hfb.first hgb.first)))
        ((abs_add_le _ _).trans
          (add_le_add (hmul hfb.first hgb.first) (hmul hfb.value hgb.second))))
    nlinarith

theorem n06_deriv_two_comp {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : ℝ) :
    deriv (deriv (fun t => f (g t))) x =
      deriv (deriv f) (g x) * deriv g x ^ 2 +
        deriv f (g x) * deriv (deriv g) x := by
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have hfirst : deriv (fun t => f (g t)) =
      fun t => deriv f (g t) * deriv g t := by
    funext t
    exact deriv_comp t (hf.differentiable (by simp) (g t)) (hg.differentiable (by simp) t)
  rw [hfirst]
  have houter : HasDerivAt (fun t => deriv f (g t))
      (deriv (deriv f) (g x) * deriv g x) x :=
    (hf'.differentiable (by simp) (g x)).hasDerivAt.comp x
      (hg.differentiable (by simp) x).hasDerivAt
  have hproduct : HasDerivAt (fun t => deriv f (g t) * deriv g t)
      ((deriv (deriv f) (g x) * deriv g x) * deriv g x +
        deriv f (g x) * deriv (deriv g) x) x :=
    houter.mul (hg'.differentiable (by simp) x).hasDerivAt
  exact hproduct.deriv.trans (by ring)

theorem N06ScalarJetTwoBound.comp
    {f g : ℝ → ℝ} {x B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hB : 1 ≤ B)
    (hfb : N06ScalarJetTwoBound f (g x) B)
    (hgb : N06ScalarJetTwoBound g x B) :
    N06ScalarJetTwoBound (fun t => f (g t)) x (2 * B ^ 3) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hB13 : B ≤ B ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 3)
  have hB23 : B ^ 2 ≤ B ^ 3 := pow_le_pow_right₀ hB (by norm_num)
  have hB3 : 0 ≤ B ^ 3 := pow_nonneg hB0 _
  constructor
  · exact hfb.value.trans (by nlinarith)
  · rw [show deriv (fun t => f (g t)) x = deriv f (g x) * deriv g x from
      deriv_comp x (hf.differentiable (by simp) (g x)) (hg.differentiable (by simp) x),
      abs_mul]
    have hb := mul_le_mul hfb.first hgb.first (abs_nonneg _) hB0
    nlinarith
  · rw [n06_deriv_two_comp hf hg]
    have h1 : |deriv (deriv f) (g x) * deriv g x ^ 2| ≤ B * B ^ 2 := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul hfb.second
        (pow_le_pow_left₀ (abs_nonneg _) hgb.first 2) (pow_nonneg (abs_nonneg _) _) hB0
    have h2 : |deriv f (g x) * deriv (deriv g) x| ≤ B * B := by
      rw [abs_mul]
      exact mul_le_mul hfb.first hgb.second (abs_nonneg _) hB0
    have hb := (abs_add_le _ _).trans (add_le_add h1 h2)
    nlinarith

/-- Reciprocal jets are bounded using the genuine derivative of the
identity f * f⁻¹ = 1. The reciprocal value is a primitive lower-bound input. -/
theorem N06ScalarJetTwoBound.inv
    {f : ℝ → ℝ} {x B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hne : ∀ t, f t ≠ 0)
    (hB : 1 ≤ B) (hfb : N06ScalarJetTwoBound f x B)
    (hinv : |(f x)⁻¹| ≤ B) :
    N06ScalarJetTwoBound (fun t => (f t)⁻¹) x (3 * B ^ 5) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hB15 : B ≤ B ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 5)
  have hB35 : B ^ 3 ≤ B ^ 5 := pow_le_pow_right₀ hB (by norm_num)
  have hB5 : 0 ≤ B ^ 5 := pow_nonneg hB0 _
  have hg : ContDiff ℝ ∞ (fun t => (f t)⁻¹) := hf.inv hne
  have hfirst : |deriv (fun t => (f t)⁻¹) x| ≤ B ^ 3 := by
    calc
      _ = |deriv f x| * |(f x)⁻¹| ^ 2 := by
        rw [deriv_fun_inv'' (hf.differentiable (by simp) x) (hne x),
          abs_div, abs_neg, abs_pow, div_eq_mul_inv, abs_inv, inv_pow]
      _ ≤ B * B ^ 2 := mul_le_mul hfb.first
        (pow_le_pow_left₀ (abs_nonneg _) hinv 2) (pow_nonneg (abs_nonneg _) _) hB0
      _ = B ^ 3 := by ring
  have hprod : (fun t => f t * (f t)⁻¹) = fun _ => (1 : ℝ) :=
    funext fun t => mul_inv_cancel₀ (hne t)
  have hsecond := n06_deriv_two_mul hf hg x
  rw [hprod] at hsecond
  simp only [deriv_const', deriv_const] at hsecond
  have hsolve : deriv (deriv (fun t => (f t)⁻¹)) x =
      -(deriv (deriv f) x * (f x)⁻¹ +
        2 * deriv f x * deriv (fun t => (f t)⁻¹) x) / f x := by
    apply (eq_div_iff (hne x)).2
    nlinarith only [hsecond]
  constructor
  · exact hinv.trans (by nlinarith)
  · exact hfirst.trans (by nlinarith)
  · have h1 : |deriv (deriv f) x * (f x)⁻¹| ≤ B * B := by
      rw [abs_mul]
      exact mul_le_mul hfb.second hinv (abs_nonneg _) hB0
    have h2 : |2 * deriv f x * deriv (fun t => (f t)⁻¹) x| ≤ 2 * B * B ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfb.first (by norm_num))
        hfirst (abs_nonneg _) (by positivity)
    calc
      _ = |deriv (deriv f) x * (f x)⁻¹ +
          2 * deriv f x * deriv (fun t => (f t)⁻¹) x| * |(f x)⁻¹| := by
        rw [hsolve, abs_div, abs_neg, div_eq_mul_inv, abs_inv]
      _ ≤ (B * B + 2 * B * B ^ 3) * B :=
        mul_le_mul ((abs_add_le _ _).trans (add_le_add h1 h2)) hinv
          (abs_nonneg _) (by positivity)
      _ ≤ 3 * B ^ 5 := by nlinarith

end ContinuousFlexibility.Analysis
