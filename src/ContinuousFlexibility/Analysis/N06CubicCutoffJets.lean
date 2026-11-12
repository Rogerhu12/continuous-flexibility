import ContinuousFlexibility.Analysis.DegenerateEnergy
import ContinuousFlexibility.Radial.TailKernelTestExtension
import ContinuousFlexibility.Radial.InnerBufferSource

/-!
# The cubic weights absorb both derivatives of the actual interior cutoff

The cutoff is the existing `intervalTestCutoff 0 1 n`. Its first and
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

private theorem cutoff_left_argument (k x : ℝ) :
    HasDerivAt (fun y : ℝ => k * y - 1) k x := by
  simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul k).sub_const (1 : ℝ)

private theorem cutoff_right_argument (k x : ℝ) :
    HasDerivAt (fun y : ℝ => k * (1 - y) - 1) (-k) x := by
  simpa only [id_eq, mul_neg_one] using
    (((hasDerivAt_id x).const_sub (1 : ℝ)).const_mul k).sub_const (1 : ℝ)

private theorem cutoff_first (k x : ℝ) :
    deriv (innerDirichletCutoff 0 1 k) x = k *
      (deriv Real.smoothTransition (k * x - 1) * Real.smoothTransition (k * (1 - x) - 1) -
        Real.smoothTransition (k * x - 1) * deriv Real.smoothTransition (k * (1 - x) - 1)) := by
  have hSmooth : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hL := ((hSmooth.differentiable (by simp)
    (k * x - 1)).hasDerivAt).comp x (cutoff_left_argument k x)
  have hR := ((hSmooth.differentiable (by simp)
    (k * (1 - x) - 1)).hasDerivAt).comp x (cutoff_right_argument k x)
  have hfun : innerDirichletCutoff 0 1 k = fun y : ℝ =>
      Real.smoothTransition (k * y - 1) * Real.smoothTransition (k * (1 - y) - 1) := by
    funext y
    simp only [innerDirichletCutoff, sub_zero]
  rw [hfun]
  exact (hL.mul hR).deriv.trans (by simp only [Function.comp_apply]; ring)

private theorem cutoff_second (k x : ℝ) :
    deriv (deriv (innerDirichletCutoff 0 1 k)) x = k ^ 2 *
      (deriv (deriv Real.smoothTransition) (k * x - 1) *
          Real.smoothTransition (k * (1 - x) - 1) -
        2 * deriv Real.smoothTransition (k * x - 1) *
          deriv Real.smoothTransition (k * (1 - x) - 1) +
        Real.smoothTransition (k * x - 1) *
          deriv (deriv Real.smoothTransition) (k * (1 - x) - 1)) := by
  have heq : deriv (innerDirichletCutoff 0 1 k) = fun y => k *
      (deriv Real.smoothTransition (k * y - 1) * Real.smoothTransition (k * (1 - y) - 1) -
        Real.smoothTransition (k * y - 1) * deriv Real.smoothTransition (k * (1 - y) - 1)) :=
    funext (cutoff_first k)
  have hS : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  have hSmooth : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hL := ((hSmooth.differentiable (by simp)
    (k * x - 1)).hasDerivAt).comp x (cutoff_left_argument k x)
  have hR := ((hSmooth.differentiable (by simp)
    (k * (1 - x) - 1)).hasDerivAt).comp x (cutoff_right_argument k x)
  have hL₁ := ((hS.differentiable (by simp) (k * x - 1)).hasDerivAt).comp x
    (cutoff_left_argument k x)
  have hR₁ := ((hS.differentiable (by simp) (k * (1 - x) - 1)).hasDerivAt).comp x
    (cutoff_right_argument k x)
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
    |deriv (innerDirichletCutoff 0 1 k) x| ≤ (2 * C) * k := by
  have hL := transition_mul_bound hC (hderiv (k * x - 1)) (k * (1 - x) - 1)
  have hR : |Real.smoothTransition (k * x - 1) *
      deriv Real.smoothTransition (k * (1 - x) - 1)| ≤ C := by
    simpa only [mul_comm] using
      transition_mul_bound hC (hderiv (k * (1 - x) - 1)) (k * x - 1)
  rw [cutoff_first, abs_mul, abs_of_nonneg hk]
  calc
    _ ≤ k * (|deriv Real.smoothTransition (k * x - 1) *
          Real.smoothTransition (k * (1 - x) - 1)| +
        |Real.smoothTransition (k * x - 1) *
          deriv Real.smoothTransition (k * (1 - x) - 1)|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) hk
    _ ≤ k * (C + C) := mul_le_mul_of_nonneg_left (add_le_add hL hR) hk
    _ = _ := by ring

private theorem cutoff_second_bound {C₁ C₂ k : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hfirst : ∀ x, |deriv Real.smoothTransition x| ≤ C₁)
    (hsecond : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C₂) (x : ℝ) :
    |deriv (deriv (innerDirichletCutoff 0 1 k)) x| ≤
      (2 * C₂ + 2 * C₁ ^ 2) * k ^ 2 := by
  have hL := transition_mul_bound hC₂ (hsecond (k * x - 1)) (k * (1 - x) - 1)
  have hR : |Real.smoothTransition (k * x - 1) *
      deriv (deriv Real.smoothTransition) (k * (1 - x) - 1)| ≤ C₂ := by
    simpa only [mul_comm] using
      transition_mul_bound hC₂ (hsecond (k * (1 - x) - 1)) (k * x - 1)
  have hM : |2 * deriv Real.smoothTransition (k * x - 1) *
      deriv Real.smoothTransition (k * (1 - x) - 1)| ≤ 2 * C₁ ^ 2 := by
    have hprod : |deriv Real.smoothTransition (k * x - 1)| *
        |deriv Real.smoothTransition (k * (1 - x) - 1)| ≤ C₁ * C₁ :=
      mul_le_mul (hfirst _) (hfirst _) (abs_nonneg _) hC₁
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith only [hprod]
  rw [cutoff_second, abs_mul, abs_of_nonneg (sq_nonneg k)]
  calc
    _ ≤ k ^ 2 * ((|deriv (deriv Real.smoothTransition) (k * x - 1) *
          Real.smoothTransition (k * (1 - x) - 1)| +
        |2 * deriv Real.smoothTransition (k * x - 1) *
          deriv Real.smoothTransition (k * (1 - x) - 1)|) +
        |Real.smoothTransition (k * x - 1) *
          deriv (deriv Real.smoothTransition) (k * (1 - x) - 1)|) :=
      mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
        (add_le_add (abs_sub _ _) le_rfl)) (sq_nonneg k)
    _ ≤ k ^ 2 * ((C₂ + 2 * C₁ ^ 2) + C₂) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hL hM) hR) (sq_nonneg k)
    _ = _ := by ring

/-- One fixed constant controls both scaled derivatives of the already
defined compact interior cutoff. -/
theorem n06_intervalTestCutoff_derivative_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ∀ x : ℝ,
      |deriv (intervalTestCutoff 0 1 n) x| ≤ C * ((n : ℝ) + 1) ∧
      |deriv (deriv (intervalTestCutoff 0 1 n)) x| ≤ C * ((n : ℝ) + 1) ^ 2 := by
  obtain ⟨C₁, hC₁, hfirst⟩ := innerTransition_deriv_bounded
  obtain ⟨C₂, hC₂, hsecond⟩ := innerTransition_second_deriv_bounded
  let C := 1 + 2 * C₁ + 2 * C₂ + 2 * C₁ ^ 2
  have hC : 1 ≤ C := by dsimp only [C]; nlinarith only [hC₁, hC₂, sq_nonneg C₁]
  refine ⟨C, hC, ?_⟩
  intro n x
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  constructor
  · exact (cutoff_first_bound hC₁ hn hfirst x).trans
      (mul_le_mul_of_nonneg_right
        (by dsimp only [C]; nlinarith only [hC₂, sq_nonneg C₁]) hn)
  · exact (cutoff_second_bound hC₁ hC₂ hfirst hsecond x).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [hC₁]) (sq_nonneg _))

/-- Both actual derivatives vanish wherever the cutoff has its interior
constant germ. This does not impose any value or trace on the weak field. -/
theorem n06_intervalTestCutoff_derivatives_zero (n : ℕ) {x : ℝ}
    (hL : 2 < ((n : ℝ) + 1) * x)
    (hR : 2 < ((n : ℝ) + 1) * (1 - x)) :
    deriv (intervalTestCutoff 0 1 n) x = 0 ∧
      deriv (deriv (intervalTestCutoff 0 1 n)) x = 0 := by
  have hg : intervalTestCutoff 0 1 n =ᶠ[𝓝 x] (fun _ => 1) := by
    change innerDirichletCutoff 0 1 ((n : ℝ) + 1) =ᶠ[𝓝 x] (fun _ => 1)
    exact innerDirichletCutoff_eventually_one
      (by simpa only [sub_zero] using hL) hR
  exact ⟨by simpa only [deriv_const] using hg.deriv_eq,
    by simpa only [deriv_const', deriv_const] using hg.deriv.deriv_eq⟩

/-- The powers occurring in the genuine cubic commutator absorb both
cutoff derivatives, uniformly up to both endpoints. -/
theorem n06_intervalTestCutoff_cubic_weighted_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) 1,
      |cylinderWeight x ^ 2 * deriv (intervalTestCutoff 0 1 n) x| ≤ C / ((n : ℝ) + 1) ∧
      |cylinderWeight x ^ 3 * deriv (deriv (intervalTestCutoff 0 1 n)) x| ≤
        C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, hbound⟩ := n06_intervalTestCutoff_derivative_bounds
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  refine ⟨8 * C, mul_nonneg (by norm_num) hC₀, ?_⟩
  intro n x hx
  let k : ℝ := (n : ℝ) + 1
  have hk : 0 < k := by dsimp only [k]; positivity
  have hd : 0 ≤ cylinderWeight x := cylinderWeight_nonneg hx
  by_cases hinner : 2 < k * x ∧ 2 < k * (1 - x)
  · obtain ⟨hzero₁, hzero₂⟩ := n06_intervalTestCutoff_derivatives_zero n hinner.1 hinner.2
    simp only [hzero₁, hzero₂, mul_zero, abs_zero]
    exact ⟨div_nonneg (mul_nonneg (by norm_num) hC₀) hk.le,
      div_nonneg (mul_nonneg (by norm_num) hC₀) hk.le⟩
  · have hdx : cylinderWeight x ≤ x := by
      dsimp only [cylinderWeight]
      nlinarith only [hx.1, sq_nonneg x]
    have hdr : cylinderWeight x ≤ 1 - x := by
      dsimp only [cylinderWeight]
      nlinarith only [sq_nonneg (1 - x)]
    have hkd : cylinderWeight x * k ≤ 2 := by
      by_cases hL : 2 < k * x
      · have hR : k * (1 - x) ≤ 2 := le_of_not_gt (fun hR => hinner ⟨hL, hR⟩)
        exact (mul_le_mul_of_nonneg_right hdr hk.le).trans (by simpa only [mul_comm] using hR)
      · exact (mul_le_mul_of_nonneg_right hdx hk.le).trans
          (by simpa only [mul_comm] using (le_of_not_gt hL))
    have hsquare : (cylinderWeight x * k) ^ 2 ≤ 4 := by
      calc
        _ ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ (mul_nonneg hd hk.le) hkd 2
        _ = 4 := by norm_num
    have hcube : (cylinderWeight x * k) ^ 3 ≤ 8 := by
      calc
        _ ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ (mul_nonneg hd hk.le) hkd 3
        _ = 8 := by norm_num
    obtain ⟨hfirst, hsecond⟩ := hbound n x
    change |deriv (intervalTestCutoff 0 1 n) x| ≤ C * k at hfirst
    change |deriv (deriv (intervalTestCutoff 0 1 n)) x| ≤ C * k ^ 2 at hsecond
    constructor
    · apply (le_div_iff₀ hk).mpr
      rw [abs_mul, abs_of_nonneg (sq_nonneg (cylinderWeight x))]
      calc
        _ ≤ (cylinderWeight x ^ 2 * (C * k)) * k :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfirst (sq_nonneg _)) hk.le
        _ = C * (cylinderWeight x * k) ^ 2 := by ring
        _ ≤ C * 4 := mul_le_mul_of_nonneg_left hsquare hC₀
        _ ≤ 8 * C := by linarith
    · apply (le_div_iff₀ hk).mpr
      rw [abs_mul, abs_of_nonneg (pow_nonneg hd 3)]
      calc
        _ ≤ (cylinderWeight x ^ 3 * (C * k ^ 2)) * k :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsecond (pow_nonneg hd 3)) hk.le
        _ = C * (cylinderWeight x * k) ^ 3 := by ring
        _ ≤ C * 8 := mul_le_mul_of_nonneg_left hcube hC₀
        _ = 8 * C := by ring

end ContinuousFlexibility.Analysis
