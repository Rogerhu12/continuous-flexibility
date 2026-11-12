import ContinuousFlexibility.Radial.DirichletRiccatiComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Growth after entering the positive part of a cap

A nonnegative solution with nonnegative initial slope grows at least
like a hyperbolic cosine on any later interval where the potential has a
positive mass lower bound. This does not require that lower bound near
the original Dirichlet endpoint, where a Morse turning point has zero
potential.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

/-- Cosh comparison on a positive subinterval. The sign assumptions
can be obtained on a larger cap before the positive lower bound starts. -/
theorem terminalCap_cosh_growth {a b m : ℝ} {p q : ℝ → ℝ}
    (hab : a ≤ b) (hp : ContDiff ℝ ∞ p)
    (heq : ∀ x ∈ Icc a b, deriv (deriv p) x = q x * p x)
    (hq : ∀ x ∈ Icc a b, m ^ 2 ≤ q x)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p x) (hslope : 0 ≤ deriv p a) :
    p a * cosh (m * (b - a)) ≤ p b := by
  have hp' : ContDiff ℝ ∞ (deriv p) := (contDiff_infty_iff_deriv.mp hp).2
  have hd (x : ℝ) : HasDerivAt p (deriv p x) x :=
    (hp.differentiable (by simp) x).hasDerivAt
  have hdd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt (deriv p) (q x * p x) x := by
    rw [← heq x hx]
    exact (hp'.differentiable (by simp) x).hasDerivAt
  have hc (x : ℝ) : HasDerivAt (fun y => cosh (m * (y - a)))
      (m * sinh (m * (x - a))) x := by
    convert (((hasDerivAt_id x).sub_const a).const_mul m).cosh using 1 <;>
      simp only [id_eq, mul_one] <;> ring
  have hs (x : ℝ) : HasDerivAt (fun y => sinh (m * (y - a)))
      (m * cosh (m * (x - a))) x := by
    convert (((hasDerivAt_id x).sub_const a).const_mul m).sinh using 1 <;>
      simp only [id_eq, mul_one] <;> ring
  let W : ℝ → ℝ := fun x =>
    deriv p x * cosh (m * (x - a)) - m * (p x * sinh (m * (x - a)))
  have hW (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt W ((q x - m ^ 2) * p x * cosh (m * (x - a))) x := by
    convert ((hdd x hx).mul (hc x)).sub (((hd x).mul (hs x)).const_mul m) using 1 <;>
      (try dsimp only [W]) <;> ring
  have hmonoW : MonotoneOn W (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun x hx => (hW x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hW x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hW x (Ioo_subset_Icc_self hx)).deriv]
      exact mul_nonneg
        (mul_nonneg (sub_nonneg.mpr (hq x (Ioo_subset_Icc_self hx)))
          (hpos x (Ioo_subset_Icc_self hx)))
        (cosh_pos _).le
  have hW0 : 0 ≤ W a := by simpa only [W, sub_self, mul_zero, cosh_zero,
    sinh_zero, mul_one, sub_zero] using hslope
  have hWnonneg (x : ℝ) (hx : x ∈ Icc a b) : 0 ≤ W x :=
    hW0.trans (hmonoW ⟨le_rfl, hab⟩ hx hx.1)
  have hratio (x : ℝ) :
      HasDerivAt (fun y => p y / cosh (m * (y - a)))
        (W x / cosh (m * (x - a)) ^ 2) x := by
    convert (hd x).div (hc x) (cosh_pos _).ne' using 1 <;> (try dsimp only [W]) <;> ring
  have hmonoRatio : MonotoneOn (fun y => p y / cosh (m * (y - a))) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun x _ => (hratio x).continuousAt.continuousWithinAt
    · intro x _
      exact (hratio x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hratio x).deriv]
      exact div_nonneg (hWnonneg x (Ioo_subset_Icc_self hx)) (sq_nonneg _)
  have h := hmonoRatio ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simp only [sub_self, mul_zero, cosh_zero, div_one] at h
  exact (le_div_iff₀ (cosh_pos _)).mp h

/-- The factor two comes from cosh, rather than an assumed positive
potential at the original turning point. -/
theorem terminalCap_exponential_of_cosh {a b m : ℝ} {p q : ℝ → ℝ}
    (hab : a ≤ b) (hp : ContDiff ℝ ∞ p)
    (heq : ∀ x ∈ Icc a b, deriv (deriv p) x = q x * p x)
    (hq : ∀ x ∈ Icc a b, m ^ 2 ≤ q x)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p x) (hslope : 0 ≤ deriv p a) :
    p a ≤ 2 * p b * exp (-(m * (b - a))) := by
  have hg := terminalCap_cosh_growth hab hp heq hq hpos hslope
  have hcosh : exp (m * (b - a)) / 2 ≤ cosh (m * (b - a)) := by
    rw [cosh_eq]
    linarith only [exp_pos (-(m * (b - a)))]
  have hm := mul_le_mul_of_nonneg_left hcosh (hpos a ⟨le_rfl, hab⟩)
  calc
    p a ≤ (2 * p b) / exp (m * (b - a)) := by
      apply (le_div_iff₀ (exp_pos _)).mpr
      nlinarith only [hg, hm]
    _ = _ := by rw [exp_neg, div_eq_mul_inv]

end ContinuousFlexibility.Radial
