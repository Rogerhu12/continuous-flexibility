import ContinuousFlexibility.Analysis.DegenerateEnergy
import ContinuousFlexibility.Radial.TailKernelTestExtension
import ContinuousFlexibility.Radial.InnerBufferSource

/-!
# Actual interval cubic weights absorb the interior cutoff derivatives

The cutoff is the existing `intervalTestCutoff a b n` on the actual interval. Its first and
second derivatives have their genuine scaled transition formulas. Away
from the two endpoint layers the cutoff has constant germ one. Thus
`d^2 * chi'` and `d^3 * chi''` are uniformly of order `1 / (n + 1)`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

variable (a b : ℝ)

private theorem cutoff_left_argument (k x : ℝ) :
    HasDerivAt (fun y : ℝ => k * (y - a) - 1) k x := by
  simpa only [id_eq, mul_one] using (((hasDerivAt_id x).sub_const a).const_mul k).sub_const (1 : ℝ)

private theorem cutoff_right_argument (k x : ℝ) :
    HasDerivAt (fun y : ℝ => k * (b - y) - 1) (-k) x := by
  simpa only [id_eq, mul_neg_one] using
    (((hasDerivAt_id x).const_sub b).const_mul k).sub_const (1 : ℝ)

private theorem cutoff_first (k x : ℝ) :
    deriv (innerDirichletCutoff a b k) x = k *
      (deriv Real.smoothTransition (k * (x - a) - 1) * Real.smoothTransition (k * (b - x) - 1) -
        Real.smoothTransition (k * (x - a) - 1) * deriv Real.smoothTransition (k * (b - x) - 1)) := by
  have hSmooth : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hL := ((hSmooth.differentiable (by simp)
    (k * (x - a) - 1)).hasDerivAt).comp x (cutoff_left_argument a k x)
  have hR := ((hSmooth.differentiable (by simp)
    (k * (b - x) - 1)).hasDerivAt).comp x (cutoff_right_argument b k x)
  have hfun : innerDirichletCutoff a b k = fun y : ℝ =>
      Real.smoothTransition (k * (y - a) - 1) * Real.smoothTransition (k * (b - y) - 1) := by
    funext y
    simp only [innerDirichletCutoff, sub_zero]
  rw [hfun]
  exact (hL.mul hR).deriv.trans (by simp only [Function.comp_apply]; ring)

private theorem cutoff_second (k x : ℝ) :
    deriv (deriv (innerDirichletCutoff a b k)) x = k ^ 2 *
      (deriv (deriv Real.smoothTransition) (k * (x - a) - 1) *
          Real.smoothTransition (k * (b - x) - 1) -
        2 * deriv Real.smoothTransition (k * (x - a) - 1) *
          deriv Real.smoothTransition (k * (b - x) - 1) +
        Real.smoothTransition (k * (x - a) - 1) *
          deriv (deriv Real.smoothTransition) (k * (b - x) - 1)) := by
  have heq : deriv (innerDirichletCutoff a b k) = fun y => k *
      (deriv Real.smoothTransition (k * (y - a) - 1) * Real.smoothTransition (k * (b - y) - 1) -
        Real.smoothTransition (k * (y - a) - 1) * deriv Real.smoothTransition (k * (b - y) - 1)) :=
    funext (cutoff_first a b k)
  have hS : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  have hSmooth : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hL := ((hSmooth.differentiable (by simp)
    (k * (x - a) - 1)).hasDerivAt).comp x (cutoff_left_argument a k x)
  have hR := ((hSmooth.differentiable (by simp)
    (k * (b - x) - 1)).hasDerivAt).comp x (cutoff_right_argument b k x)
  have hL₁ := ((hS.differentiable (by simp) (k * (x - a) - 1)).hasDerivAt).comp x
    (cutoff_left_argument a k x)
  have hR₁ := ((hS.differentiable (by simp) (k * (b - x) - 1)).hasDerivAt).comp x
    (cutoff_right_argument b k x)
  rw [heq]
  exact (((hL₁.mul hR).sub (hL.mul hR₁)).const_mul k).deriv.trans
    (by simp only [Function.comp_apply]; ring)

private theorem transition_mul_bound {v C : ℝ} (hC : 0 ≤ C) (hv : |v| ≤ C) (x : ℝ) :
    |v * Real.smoothTransition x| ≤ C := by
  rw [abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg x)]
  exact (mul_le_mul hv (Real.smoothTransition.le_one x)
    (Real.smoothTransition.nonneg x) hC).trans_eq (mul_one C)

private theorem cutoff_first_bound {C k : ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k)
    (hderiv : ∀ x, |deriv Real.smoothTransition x| ≤ C) (x : ℝ) :
    |deriv (innerDirichletCutoff a b k) x| ≤ (2 * C) * k := by
  have hL := transition_mul_bound hC (hderiv (k * (x - a) - 1)) (k * (b - x) - 1)
  have hR : |Real.smoothTransition (k * (x - a) - 1) *
      deriv Real.smoothTransition (k * (b - x) - 1)| ≤ C := by
    simpa only [mul_comm] using
      transition_mul_bound hC (hderiv (k * (b - x) - 1)) (k * (x - a) - 1)
  rw [cutoff_first a b, abs_mul, abs_of_nonneg hk]
  calc
    _ ≤ k * (|deriv Real.smoothTransition (k * (x - a) - 1) *
          Real.smoothTransition (k * (b - x) - 1)| +
        |Real.smoothTransition (k * (x - a) - 1) *
          deriv Real.smoothTransition (k * (b - x) - 1)|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) hk
    _ ≤ k * (C + C) := mul_le_mul_of_nonneg_left (add_le_add hL hR) hk
    _ = _ := by ring

private theorem cutoff_second_bound {C₁ C₂ k : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hfirst : ∀ x, |deriv Real.smoothTransition x| ≤ C₁)
    (hsecond : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C₂) (x : ℝ) :
    |deriv (deriv (innerDirichletCutoff a b k)) x| ≤
      (2 * C₂ + 2 * C₁ ^ 2) * k ^ 2 := by
  have hL := transition_mul_bound hC₂ (hsecond (k * (x - a) - 1)) (k * (b - x) - 1)
  have hR : |Real.smoothTransition (k * (x - a) - 1) *
      deriv (deriv Real.smoothTransition) (k * (b - x) - 1)| ≤ C₂ := by
    simpa only [mul_comm] using
      transition_mul_bound hC₂ (hsecond (k * (b - x) - 1)) (k * (x - a) - 1)
  have hM : |2 * deriv Real.smoothTransition (k * (x - a) - 1) *
      deriv Real.smoothTransition (k * (b - x) - 1)| ≤ 2 * C₁ ^ 2 := by
    have hprod : |deriv Real.smoothTransition (k * (x - a) - 1)| *
        |deriv Real.smoothTransition (k * (b - x) - 1)| ≤ C₁ * C₁ :=
      mul_le_mul (hfirst _) (hfirst _) (abs_nonneg _) hC₁
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith only [hprod]
  rw [cutoff_second a b, abs_mul, abs_of_nonneg (sq_nonneg k)]
  calc
    _ ≤ k ^ 2 * ((|deriv (deriv Real.smoothTransition) (k * (x - a) - 1) *
          Real.smoothTransition (k * (b - x) - 1)| +
        |2 * deriv Real.smoothTransition (k * (x - a) - 1) *
          deriv Real.smoothTransition (k * (b - x) - 1)|) +
        |Real.smoothTransition (k * (x - a) - 1) *
          deriv (deriv Real.smoothTransition) (k * (b - x) - 1)|) :=
      mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
        (add_le_add (abs_sub _ _) le_rfl)) (sq_nonneg k)
    _ ≤ k ^ 2 * ((C₂ + 2 * C₁ ^ 2) + C₂) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hL hM) hR) (sq_nonneg k)
    _ = _ := by ring

/-- One fixed constant controls both scaled derivatives of the already
defined compact interior cutoff. -/
theorem n06_intervalCutoff_derivative_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ∀ x : ℝ,
      |deriv (intervalTestCutoff a b n) x| ≤ C * ((n : ℝ) + 1) ∧
      |deriv (deriv (intervalTestCutoff a b n)) x| ≤ C * ((n : ℝ) + 1) ^ 2 := by
  obtain ⟨C₁, hC₁, hfirst⟩ := innerTransition_deriv_bounded
  obtain ⟨C₂, hC₂, hsecond⟩ := innerTransition_second_deriv_bounded
  let C := 1 + 2 * C₁ + 2 * C₂ + 2 * C₁ ^ 2
  have hC : 1 ≤ C := by dsimp only [C]; nlinarith only [hC₁, hC₂, sq_nonneg C₁]
  refine ⟨C, hC, ?_⟩
  intro n x
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  constructor
  · exact (cutoff_first_bound a b hC₁ hn hfirst x).trans
      (mul_le_mul_of_nonneg_right
        (by dsimp only [C]; nlinarith only [hC₂, sq_nonneg C₁]) hn)
  · exact (cutoff_second_bound a b hC₁ hC₂ hfirst hsecond x).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [hC₁]) (sq_nonneg _))

/-- Both actual derivatives vanish wherever the cutoff has its interior
constant germ. This does not impose any value or trace on the weak field. -/
theorem n06_intervalCutoff_derivatives_zero (n : ℕ) {x : ℝ}
    (hL : 2 < ((n : ℝ) + 1) * (x - a))
    (hR : 2 < ((n : ℝ) + 1) * (b - x)) :
    deriv (intervalTestCutoff a b n) x = 0 ∧
      deriv (deriv (intervalTestCutoff a b n)) x = 0 := by
  have hg : intervalTestCutoff a b n =ᶠ[𝓝 x] (fun _ => 1) := by
    change innerDirichletCutoff a b ((n : ℝ) + 1) =ᶠ[𝓝 x] (fun _ => 1)
    exact innerDirichletCutoff_eventually_one
      hL hR
  exact ⟨by simpa only [deriv_const] using hg.deriv_eq,
    by simpa only [deriv_const', deriv_const] using hg.deriv.deriv_eq⟩

/-- The actual two-endpoint cubic weights absorb both cutoff derivatives.
The constant may depend on the fixed interval, and is chosen before n or x. -/
theorem n06_intervalCutoff_cubic_weighted_bounds (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ x ∈ Icc a b,
      |((x - a) * (b - x)) ^ 2 * deriv (intervalTestCutoff a b n) x| ≤
          C / ((n : ℝ) + 1) ∧
      |((x - a) * (b - x)) ^ 3 * deriv (deriv (intervalTestCutoff a b n)) x| ≤
          C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, hbound⟩ := n06_intervalCutoff_derivative_bounds a b
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hℓ : 0 ≤ b - a := sub_nonneg.mpr hab
  let Q : ℝ := 4 * C * (b - a) ^ 2 + 8 * C * (b - a) ^ 3
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  refine ⟨Q, hQ, ?_⟩
  intro n x hx
  let k : ℝ := (n : ℝ) + 1
  let d : ℝ := (x - a) * (b - x)
  have hk : 0 < k := by dsimp only [k]; positivity
  have h0 : 0 ≤ x - a := sub_nonneg.mpr hx.1
  have h1 : 0 ≤ b - x := sub_nonneg.mpr hx.2
  have hd : 0 ≤ d := mul_nonneg h0 h1
  by_cases hinner : 2 < k * (x - a) ∧ 2 < k * (b - x)
  · obtain ⟨hzero₁, hzero₂⟩ := n06_intervalCutoff_derivatives_zero a b n hinner.1 hinner.2
    simp only [hzero₁, hzero₂, mul_zero, abs_zero]
    exact ⟨div_nonneg hQ hk.le, div_nonneg hQ hk.le⟩
  · have hdx : d ≤ (x - a) * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith only [hx.1]) h0
    have hdr : d ≤ (b - x) * (b - a) := by
      dsimp only [d]
      calc
        _ ≤ (b - a) * (b - x) :=
          mul_le_mul_of_nonneg_right (by linarith only [hx.2]) h1
        _ = _ := mul_comm _ _
    have hkd : d * k ≤ 2 * (b - a) := by
      by_cases hL : 2 < k * (x - a)
      · have hR : k * (b - x) ≤ 2 := le_of_not_gt (fun hR => hinner ⟨hL, hR⟩)
        calc
          _ ≤ ((b - x) * (b - a)) * k := mul_le_mul_of_nonneg_right hdr hk.le
          _ = (k * (b - x)) * (b - a) := by ring
          _ ≤ 2 * (b - a) := mul_le_mul_of_nonneg_right hR hℓ
      · calc
          _ ≤ ((x - a) * (b - a)) * k := mul_le_mul_of_nonneg_right hdx hk.le
          _ = (k * (x - a)) * (b - a) := by ring
          _ ≤ 2 * (b - a) := mul_le_mul_of_nonneg_right (le_of_not_gt hL) hℓ
    have hsquare : (d * k) ^ 2 ≤ 4 * (b - a) ^ 2 := by
      exact (pow_le_pow_left₀ (mul_nonneg hd hk.le) hkd 2).trans_eq (by ring)
    have hcube : (d * k) ^ 3 ≤ 8 * (b - a) ^ 3 := by
      exact (pow_le_pow_left₀ (mul_nonneg hd hk.le) hkd 3).trans_eq (by ring)
    obtain ⟨hfirst, hsecond⟩ := hbound n x
    change |deriv (intervalTestCutoff a b n) x| ≤ C * k at hfirst
    change |deriv (deriv (intervalTestCutoff a b n)) x| ≤ C * k ^ 2 at hsecond
    constructor
    · apply (le_div_iff₀ hk).mpr
      change |d ^ 2 * deriv (intervalTestCutoff a b n) x| * k ≤ Q
      rw [abs_mul, abs_of_nonneg (sq_nonneg d)]
      calc
        _ ≤ (d ^ 2 * (C * k)) * k :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfirst (sq_nonneg _)) hk.le
        _ = C * (d * k) ^ 2 := by ring
        _ ≤ C * (4 * (b - a) ^ 2) := mul_le_mul_of_nonneg_left hsquare hC₀
        _ ≤ Q := by dsimp only [Q]; nlinarith only [mul_nonneg hC₀ (pow_nonneg hℓ 3)]
    · apply (le_div_iff₀ hk).mpr
      change |d ^ 3 * deriv (deriv (intervalTestCutoff a b n)) x| * k ≤ Q
      rw [abs_mul, abs_of_nonneg (pow_nonneg hd 3)]
      calc
        _ ≤ (d ^ 3 * (C * k ^ 2)) * k :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsecond (pow_nonneg hd 3)) hk.le
        _ = C * (d * k) ^ 3 := by ring
        _ ≤ C * (8 * (b - a) ^ 3) := mul_le_mul_of_nonneg_left hcube hC₀
        _ ≤ Q := by dsimp only [Q]; nlinarith only [mul_nonneg hC₀ (sq_nonneg (b - a))]

end ContinuousFlexibility.Analysis
