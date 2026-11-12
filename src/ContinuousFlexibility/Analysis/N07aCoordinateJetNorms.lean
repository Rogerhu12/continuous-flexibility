import ContinuousFlexibility.Analysis.N07aSampleFrechetBounds
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Actual coordinate derivatives with the identity angle separated

The unwrapped angular coordinate is unbounded at order zero. Its positive
order derivatives have a fixed bound, so only the actual angle defect
uses the geometric jet estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n07a_iteratedFDeriv_linear_norm_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {n : ℕ} (hn : 0 < n) (x : E) :
    ‖iteratedFDeriv ℝ n (L : E → F) x‖ ≤ ‖L‖ := by
  cases n with
  | zero => omega
  | succ k =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (L : E → F) = fun _ => L := funext fun _ => L.fderiv
    rw [he]
    cases k with
    | zero => simp only [norm_iteratedFDeriv_zero]; exact le_rfl
    | succ k =>
      simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
      exact norm_nonneg L

theorem n07a_coordinatePair_iteratedFDeriv_bound
    {f g : PolarPoint → ℝ} {x : PolarPoint}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (d c : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖iteratedFDeriv ℝ n (fun y => (d + c * f y, y.2 + g y)) x‖ ≤
      |c| * ‖iteratedFDeriv ℝ n f x‖ + 1 + ‖iteratedFDeriv ℝ n g x‖ := by
  have hf' : ContDiffAt ℝ n f x := hf.of_le (by simp)
  have hg' : ContDiffAt ℝ n g x := hg.of_le (by simp)
  have hr : ContDiffAt ℝ n (fun y => d + c * f y) x :=
    contDiffAt_const.add (contDiffAt_const.mul hf')
  have hθ : ContDiffAt ℝ n (fun y : PolarPoint => y.2 + g y) x :=
    contDiffAt_snd.add hg'
  have hrad : ‖iteratedFDeriv ℝ n (fun y => d + c * f y) x‖ =
      |c| * ‖iteratedFDeriv ℝ n f x‖ := by
    change ‖iteratedFDeriv ℝ n ((fun _ : PolarPoint => d) + fun y => c * f y) x‖ = _
    rw [iteratedFDeriv_add_apply (f := fun _ : PolarPoint => d)
      (g := fun y => c * f y) contDiffAt_const (contDiffAt_const.mul hf')]
    have hnzero : iteratedFDeriv ℝ n (fun _ : PolarPoint => d) x = 0 := by
      cases n with
      | zero => omega
      | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply]
    rw [hnzero, zero_add]
    change ‖iteratedFDeriv ℝ n (fun y => c • f y) x‖ = _
    rw [iteratedFDeriv_const_smul_apply' hf', norm_smul, Real.norm_eq_abs]
  have hlinear : ‖iteratedFDeriv ℝ n (fun y : PolarPoint => y.2) x‖ ≤ 1 :=
    (n07a_iteratedFDeriv_linear_norm_le (ContinuousLinearMap.snd ℝ ℝ ℝ) hn x).trans
      (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  have hang : ‖iteratedFDeriv ℝ n (fun y : PolarPoint => y.2 + g y) x‖ ≤
      1 + ‖iteratedFDeriv ℝ n g x‖ := by
    change ‖iteratedFDeriv ℝ n (Prod.snd + g) x‖ ≤ _
    rw [iteratedFDeriv_add_apply contDiffAt_snd hg']
    exact (norm_add_le _ _).trans (add_le_add hlinear le_rfl)
  rw [iteratedFDeriv_prodMk hr hθ le_rfl, ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · rw [hrad]
    linarith only [norm_nonneg (iteratedFDeriv ℝ n g x)]
  · exact hang.trans (by
      nlinarith only [mul_nonneg (abs_nonneg c) (norm_nonneg (iteratedFDeriv ℝ n f x))])

end ContinuousFlexibility.Analysis
