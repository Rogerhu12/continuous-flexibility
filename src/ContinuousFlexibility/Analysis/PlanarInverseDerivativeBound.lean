module

public import ContinuousFlexibility.Analysis.AdjugateInversePrincipalField
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# A numerical bound for the actual inverse derivative

The planar max norm turns four bounded matrix entries into an operator
norm bound. The genuine inverse derivative entries are already fixed by
the inverse germ. A lower bound for the actual Jacobian therefore gives
the quantitative first inverse derivative needed by the existing
higher-jet inverse theorem, without assuming an inverse-jet estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter ContinuousFlexibility.Statements
open scoped Topology

set_option backward.isDefEq.respectTransparency false

private theorem planar_row_abs_le
    {u v a b M N : ℝ} (hN : 0 ≤ N)
    (hu : |u| ≤ N) (hv : |v| ≤ N) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |u * a + v * b| ≤ 2 * M * N := by
  calc
    |u * a + v * b| ≤ |u * a| + |v * b| := abs_add_le _ _
    _ = |u| * |a| + |v| * |b| := by rw [abs_mul, abs_mul]
    _ ≤ N * M + N * M := add_le_add
      (mul_le_mul hu ha (abs_nonneg a) hN)
      (mul_le_mul hv hb (abs_nonneg b) hN)
    _ = 2 * M * N := by ring

/-- Four actual basis entries control the planar operator norm. -/
theorem norm_planeCLM_le_of_basis_entries
    (L : PolarPoint →L[ℝ] PolarPoint) {M : ℝ} (hM : 0 ≤ M)
    (h11 : |(L (1, 0)).1| ≤ M) (h12 : |(L (0, 1)).1| ≤ M)
    (h21 : |(L (1, 0)).2| ≤ M) (h22 : |(L (0, 1)).2| ≤ M) :
    ‖L‖ ≤ 2 * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hM)
  intro x
  have hx1 : |x.1| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_fst_le x
  have hx2 : |x.2| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_snd_le x
  rw [planeCLM_apply_decompose L x, Prod.norm_def]
  apply max_le
  · simpa only [Real.norm_eq_abs] using
      planar_row_abs_le (norm_nonneg x) hx1 hx2 h11 h12
  · simpa only [Real.norm_eq_abs] using
      planar_row_abs_le (norm_nonneg x) hx1 hx2 h21 h22

/-- A genuine inverse germ, forward derivative entries and the actual
Jacobian lower bound imply a first inverse derivative bound. -/
theorem fderiv_inverse_norm_le_of_germ
    {F G : PolarPoint → PolarPoint} {x : PolarPoint} {M κ : ℝ}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G (F x))
    (hinverse : G ∘ F =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint))
    (hκ : 0 < κ) (hJ : κ ≤ |planeJacobian F x|)
    (h11 : |(fderiv ℝ F x (1, 0)).1| ≤ M)
    (h12 : |(fderiv ℝ F x (0, 1)).1| ≤ M)
    (h21 : |(fderiv ℝ F x (1, 0)).2| ≤ M)
    (h22 : |(fderiv ℝ F x (0, 1)).2| ≤ M) :
    ‖fderiv ℝ G (F x)‖ ≤ 2 * M / κ := by
  have hM : 0 ≤ M := (abs_nonneg _).trans h11
  have hdiv (v : ℝ) (hv : |v| ≤ M) : |v / planeJacobian F x| ≤ M / κ := by
    rw [abs_div]
    exact (div_le_div_of_nonneg_right hv (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left hM hκ hJ)
  have hi := fderiv_inverse_entries_of_germ hF hG hinverse
  have hg11 : |(fderiv ℝ G (F x) (1, 0)).1| ≤ M / κ := by
    rw [hi.1]
    exact hdiv _ h22
  have hg12 : |(fderiv ℝ G (F x) (0, 1)).1| ≤ M / κ := by
    rw [hi.2.1]
    exact hdiv _ (by simpa only [abs_neg] using h12)
  have hg21 : |(fderiv ℝ G (F x) (1, 0)).2| ≤ M / κ := by
    rw [hi.2.2.1]
    exact hdiv _ (by simpa only [abs_neg] using h21)
  have hg22 : |(fderiv ℝ G (F x) (0, 1)).2| ≤ M / κ := by
    rw [hi.2.2.2]
    exact hdiv _ h11
  calc
    ‖fderiv ℝ G (F x)‖ ≤ 2 * (M / κ) :=
      norm_planeCLM_le_of_basis_entries _ (div_nonneg hM hκ.le) hg11 hg12 hg21 hg22
    _ = 2 * M / κ := by ring

end ContinuousFlexibility.Analysis
