import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A polynomial endpoint bound for a positive short-interval solution

Reduction of order produces a solution with initial data `(0, 1)` from
an actual positive solution.  On a sufficiently short interval its
growth is bounded below directly by the mean value theorem.  The result
controls the original endpoint value using its opposite value and the
actual integral of its reciprocal square.  No exponential Gronwall
constant or lower bound for the desired endpoint is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A normalized solution with a relatively bounded second derivative
grows by at least half the affine solution on a short interval. -/
theorem n06_short_ode_normalized_lower
    {f : ℝ → ℝ} {ℓ K : ℝ} (hℓ : 0 < ℓ) (hK : 0 ≤ K)
    (hsmall : K * ℓ ^ 2 ≤ (1 / 4 : ℝ))
    (hf : ∀ x ∈ Icc (0 : ℝ) ℓ, DifferentiableAt ℝ f x)
    (hdf : ∀ x ∈ Icc (0 : ℝ) ℓ, DifferentiableAt ℝ (deriv f) x)
    (hf0 : f 0 = 0) (hdf0 : deriv f 0 = 1)
    (hdd : ∀ x ∈ Icc (0 : ℝ) ℓ, |deriv (deriv f) x| ≤ K * |f x|) :
    ℓ / 2 ≤ f ℓ := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) ℓ := ⟨le_rfl, hℓ.le⟩
  have hend : ℓ ∈ Icc (0 : ℝ) ℓ := ⟨hℓ.le, le_rfl⟩
  have hfc : ContinuousOn f (Icc (0 : ℝ) ℓ) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, hzero⟩ hfc.abs
  let M : ℝ := |f u|
  have hM : 0 ≤ M := abs_nonneg _
  have hddM (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) :
      ‖deriv (deriv f) x‖ ≤ K * M := by
    simpa only [Real.norm_eq_abs] using
      (hdd x hx).trans (mul_le_mul_of_nonneg_left (hmax hx) hK)
  have hdev (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) :
      |deriv f x - 1| ≤ K * M * x := by
    have he := Convex.norm_image_sub_le_of_norm_deriv_le hdf hddM
      (convex_Icc (0 : ℝ) ℓ) hzero hx
    simpa only [Real.norm_eq_abs, hdf0, sub_zero, abs_of_nonneg hx.1] using he
  have hderiv (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) :
      ‖deriv f x‖ ≤ 1 + K * M * ℓ := by
    rw [Real.norm_eq_abs]
    calc
      |deriv f x| = |(deriv f x - 1) + 1| := by rw [sub_add_cancel]
      _ ≤ |deriv f x - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ K * M * x + 1 := by
        rw [abs_one]
        linarith only [hdev x hx]
      _ ≤ 1 + K * M * ℓ := by
        have he := mul_le_mul_of_nonneg_left hx.2 (mul_nonneg hK hM)
        linarith only [he]
  have hvalue : M ≤ (1 + K * M * ℓ) * ℓ := by
    have he := Convex.norm_image_sub_le_of_norm_deriv_le hf hderiv
      (convex_Icc (0 : ℝ) ℓ) hzero hu
    have he' : M ≤ (1 + K * M * ℓ) * u := by
      simpa only [Real.norm_eq_abs, hf0, sub_zero, abs_of_nonneg hu.1] using he
    exact he'.trans (mul_le_mul_of_nonneg_left hu.2 (by positivity))
  have hMbound : M ≤ 2 * ℓ := by
    have hs := mul_le_mul_of_nonneg_right hsmall hM
    nlinarith only [hvalue, hs, hℓ]
  have herror : K * M * ℓ ≤ (1 / 2 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hMbound (mul_nonneg hK hℓ.le)
    nlinarith only [hm, hsmall]
  have hfirst (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) : (1 / 2 : ℝ) ≤ deriv f x := by
    have he := (hdev x hx).trans
      (mul_le_mul_of_nonneg_left hx.2 (mul_nonneg hK hM))
    have hlo := (abs_le.mp he).1
    linarith only [hlo, herror]
  have hlast := (convex_Icc (0 : ℝ) ℓ).mul_sub_le_image_sub_of_le_deriv hfc
    (fun x hx => (hf x (interior_subset hx)).differentiableWithinAt)
    (fun x hx => hfirst x (interior_subset hx)) 0 hzero ℓ hend hℓ.le
  simpa only [sub_zero, hf0, sub_zero, div_eq_mul_inv, one_mul, mul_comm] using hlast

/-- The genuine reduction-of-order function, including its normalization
at the left endpoint. -/
def n06ReductionOfOrder (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  W 0 * (W x * ∫ t in (0 : ℝ)..x, (W t)⁻¹ ^ 2)

/-- The normalized second solution gives a lower bound for the product
of the two endpoint values and the actual reciprocal-square integral. -/
theorem n06_positive_solution_reciprocal_mass
    {W V : ℝ → ℝ} {ℓ K : ℝ} (hW : ContDiff ℝ ∞ W)
    (hpos : ∀ x, 0 < W x) (hℓ : 0 < ℓ) (hK : 0 ≤ K)
    (hsmall : K * ℓ ^ 2 ≤ (1 / 4 : ℝ))
    (hV : ∀ x ∈ Icc (0 : ℝ) ℓ, |V x| ≤ K)
    (hode : ∀ x ∈ Icc (0 : ℝ) ℓ, deriv (deriv W) x + V x * W x = 0) :
    ℓ / 2 ≤ W 0 * W ℓ * ∫ t in (0 : ℝ)..ℓ, (W t)⁻¹ ^ 2 := by
  let J : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, (W t)⁻¹ ^ 2
  let S : ℝ → ℝ := n06ReductionOfOrder W
  have hWinv : ContDiff ℝ ∞ (fun x => (W x)⁻¹) := hW.inv (fun x => (hpos x).ne')
  have hIc : Continuous (fun x => (W x)⁻¹ ^ 2) := (hWinv.pow 2).continuous
  have hJderiv (x : ℝ) : HasDerivAt J ((W x)⁻¹ ^ 2) x :=
    intervalIntegral.integral_hasDerivAt_right (hIc.intervalIntegrable 0 x)
      hIc.aestronglyMeasurable.stronglyMeasurableAtFilter hIc.continuousAt
  have hJdiff : Differentiable ℝ J := fun x => (hJderiv x).differentiableAt
  have hJformula : deriv J = fun x => (W x)⁻¹ ^ 2 := funext fun x => (hJderiv x).deriv
  have hJsmooth : ContDiff ℝ ∞ J := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨hJdiff, ?_⟩
    rw [hJformula]
    exact hWinv.pow 2
  have hSsmooth : ContDiff ℝ ∞ S := contDiff_const.mul (hW.mul hJsmooth)
  have hSfirst (x : ℝ) : HasDerivAt S
      (W 0 * (deriv W x * J x + (W x)⁻¹)) x := by
    have hd := (((hW.differentiable (by simp) x).hasDerivAt).fun_mul (hJderiv x)).const_mul (W 0)
    have halg : W 0 * (deriv W x * J x + W x * (W x)⁻¹ ^ 2) =
        W 0 * (deriv W x * J x + (W x)⁻¹) := by
      field_simp [(hpos x).ne']
      <;> ring
    exact halg ▸ hd
  have hSformula : deriv S = fun x => W 0 * (deriv W x * J x + (W x)⁻¹) :=
    funext fun x => (hSfirst x).deriv
  have hSsecond (x : ℝ) : deriv (deriv S) x = W 0 * deriv (deriv W) x * J x := by
    have hdW := ((contDiff_infty_iff_deriv.mp hW).2.differentiable (by simp) x).hasDerivAt
    have hdInv := ((hW.differentiable (by simp) x).hasDerivAt).inv (hpos x).ne'
    have hd := ((hdW.fun_mul (hJderiv x)).add hdInv).const_mul (W 0)
    calc
      deriv (deriv S) x =
          W 0 * ((deriv (deriv W) x * J x + deriv W x * (W x)⁻¹ ^ 2) +
            -deriv W x / (W x) ^ 2) := by
        rw [hSformula]
        exact hd.deriv
      _ = W 0 * deriv (deriv W) x * J x := by
        field_simp [(hpos x).ne']
        <;> ring
  have hS0 : S 0 = 0 := by simp only [S, n06ReductionOfOrder, intervalIntegral.integral_same,
    mul_zero]
  have hSd0 : deriv S 0 = 1 := by
    rw [hSformula]
    simp only [J, intervalIntegral.integral_same, mul_zero, zero_add,
      mul_inv_cancel₀ (hpos 0).ne']
  have hSode (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) :
      deriv (deriv S) x = -V x * S x := by
    rw [hSsecond, show deriv (deriv W) x = -(V x * W x) by linarith only [hode x hx]]
    dsimp only [S, n06ReductionOfOrder, J]
    ring
  have hh := n06_short_ode_normalized_lower hℓ hK hsmall
    (fun x _ => hSsmooth.differentiable (by simp) x)
    (fun x _ => (contDiff_infty_iff_deriv.mp hSsmooth).2.differentiable (by simp) x)
    hS0 hSd0 (fun x hx => by
      rw [hSode x hx, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_right (hV x hx) (abs_nonneg (S x)))
  simpa only [S, n06ReductionOfOrder, mul_assoc] using hh

/-- An upper endpoint value and an upper physical reciprocal mass give
a genuine lower endpoint value, with polynomial dependence on both. -/
theorem n06_positive_solution_endpoint_lower
    {W V : ℝ → ℝ} {ℓ K B Q : ℝ} (hW : ContDiff ℝ ∞ W)
    (hpos : ∀ x, 0 < W x) (hℓ : 0 < ℓ) (hK : 0 ≤ K)
    (hsmall : K * ℓ ^ 2 ≤ (1 / 4 : ℝ))
    (hV : ∀ x ∈ Icc (0 : ℝ) ℓ, |V x| ≤ K)
    (hode : ∀ x ∈ Icc (0 : ℝ) ℓ, deriv (deriv W) x + V x * W x = 0)
    (hB : 0 < B) (hQ : 0 < Q) (hend : W ℓ ≤ B)
    (hmass : (∫ t in (0 : ℝ)..ℓ, (W t)⁻¹ ^ 2) ≤ Q) :
    ℓ / (2 * B * Q) ≤ W 0 := by
  have hlower := n06_positive_solution_reciprocal_mass hW hpos hℓ hK hsmall hV hode
  have hmass0 : 0 ≤ ∫ t in (0 : ℝ)..ℓ, (W t)⁻¹ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hℓ.le (fun _ => sq_nonneg _)
  have hupper : W 0 * W ℓ * (∫ t in (0 : ℝ)..ℓ, (W t)⁻¹ ^ 2) ≤ W 0 * B * Q :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hend (hpos 0).le) hmass0).trans
        (mul_le_mul_of_nonneg_left hmass (mul_nonneg (hpos 0).le hB.le))
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hB) hQ)).mpr
  nlinarith only [hlower, hupper]

end ContinuousFlexibility.Analysis
