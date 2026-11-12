import ContinuousFlexibility.Analysis.N01aNegativeComponentGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Logarithmic variation on a negative component

The absolute logarithmic derivative integrates to the exact logarithmic drop
between the two roots. If the open component is contained in one reference
cell, the profile bounds extend to its closed endpoints by continuity. Their
common leading exponential cancels in the drop, leaving a quadratic bound in
the cell index.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace N01aNegativeComponent

variable {D : ReferenceData}

theorem closed_interval_mem_core (J : N01aNegativeComponent D) :
    Icc J.left J.right ⊆ radialCore D :=
  fun _ hr => ⟨J.left_mem_core.1.trans_le hr.1, hr.2.trans_lt J.right_mem_core.2⟩

theorem profile_pos_on_closed_interval (hD : RadialProfileGeometry D)
    (J : N01aNegativeComponent D) (r : ℝ) (hr : r ∈ Icc J.left J.right) :
    0 < D.w r := hD.2.2.2.2.1 r (J.closed_interval_mem_core hr)

theorem intervalIntegrable_logDerivative (hD : RadialProfileGeometry D)
    (J : N01aNegativeComponent D) :
    IntervalIntegrable (fun r => deriv D.w r / D.w r) volume J.left J.right := by
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  have hd : Continuous (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  exact (hd.continuousOn.div hw.continuous.continuousOn
    (fun r hr => (J.profile_pos_on_closed_interval hD r hr).ne')).intervalIntegrable_of_Icc
      J.left_lt_right.le

/-- The exact logarithmic drop is the integral of the absolute logarithmic derivative. -/
theorem integral_abs_logDerivative (hD : RadialProfileGeometry D)
    (J : N01aNegativeComponent D) :
    (∫ r in J.left..J.right, |deriv D.w r / D.w r|) =
      Real.log (D.w J.left) - Real.log (D.w J.right) := by
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  have hc : ContinuousOn (fun r => Real.log (D.w r)) (Icc J.left J.right) :=
    hw.continuous.continuousOn.log
      (fun r hr => (J.profile_pos_on_closed_interval hD r hr).ne')
  have hd (r : ℝ) (hr : r ∈ Ioo J.left J.right) :
      HasDerivAt (fun r => Real.log (D.w r)) (deriv D.w r / D.w r) r :=
    (hw.differentiable (by simp) r).hasDerivAt.log
      (J.profile_pos_on_closed_interval hD r (Ioo_subset_Icc_self hr)).ne'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    J.left_lt_right.le hc hd (J.intervalIntegrable_logDerivative hD)
  calc
    _ = ∫ r in J.left..J.right, -(deriv D.w r / D.w r) := by
      apply intervalIntegral.integral_congr_Ioo_of_le J.left_lt_right.le
      intro r hr
      exact abs_of_neg (div_neg_of_neg_of_pos (J.negative hr)
        (J.profile_pos_on_closed_interval hD r (Ioo_subset_Icc_self hr)))
    _ = -(∫ r in J.left..J.right, deriv D.w r / D.w r) :=
      intervalIntegral.integral_neg
    _ = _ := by rw [hFTC]; ring

theorem log_drop_nonneg (hD : RadialProfileGeometry D) (J : N01aNegativeComponent D) :
    0 ≤ Real.log (D.w J.left) - Real.log (D.w J.right) := by
  rw [← J.integral_abs_logDerivative hD]
  exact intervalIntegral.integral_nonneg_of_forall J.left_lt_right.le
    (fun r => abs_nonneg (deriv D.w r / D.w r))

/-- Cell inequalities extend to both roots, although the cell need not contain them. -/
theorem profile_bounds_on_closed_interval {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) (J : N01aNegativeComponent D) {m : ℕ}
    (hcell : J.interval ⊆ D.cells m) :
    ∀ r ∈ Icc J.left J.right,
      Real.exp (-(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) -
        C 0 * (D.cellIndex m : ℝ) ^ 2) ≤ D.w r ∧
      D.w r ≤ C 0 * Real.exp (-(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) +
        C 0 * (D.cellIndex m : ℝ) ^ 2) := by
  obtain ⟨hgeom, _, _, _, _, _, _, hlower, hupper, _⟩ := hD
  let lo : ℝ := Real.exp (-(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) -
    C 0 * (D.cellIndex m : ℝ) ^ 2)
  let hi : ℝ := C 0 * Real.exp (-(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) +
    C 0 * (D.cellIndex m : ℝ) ^ 2)
  have hw : Continuous D.w := hgeom.2.2.1.1.continuous
  have hclosed : IsClosed {r : ℝ | lo ≤ D.w r ∧ D.w r ≤ hi} :=
    (isClosed_le continuous_const hw).inter (isClosed_le hw continuous_const)
  have hopen : Ioo J.left J.right ⊆ {r : ℝ | lo ≤ D.w r ∧ D.w r ≤ hi} := by
    intro r hr
    refine ⟨hlower m r (hcell hr), (le_abs_self _).trans ?_⟩
    simpa only [radialJet, hi] using hupper m r (hcell hr) 0
  have hclosure := closure_minimal hopen hclosed
  rw [closure_Ioo J.left_lt_right.ne] at hclosure
  exact hclosure

theorem log_bounds_on_closed_interval {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) (J : N01aNegativeComponent D) {m : ℕ}
    (hcell : J.interval ⊆ D.cells m) (r : ℝ) (hr : r ∈ Icc J.left J.right) :
    -(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) - C 0 * (D.cellIndex m : ℝ) ^ 2 ≤
        Real.log (D.w r) ∧
      Real.log (D.w r) ≤ Real.log (C 0) - (D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) +
        C 0 * (D.cellIndex m : ℝ) ^ 2 := by
  have hp : 0 < D.w r := J.profile_pos_on_closed_interval hD.1 r hr
  have hC : 0 < C 0 := hD.2.2.1 0
  obtain ⟨hl, hu⟩ := J.profile_bounds_on_closed_interval hD hcell r hr
  have hl' := Real.log_le_log (Real.exp_pos _) hl
  have hu' := Real.log_le_log hp hu
  rw [Real.log_exp] at hl'
  rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at hu'
  exact ⟨hl', by linarith only [hu']⟩

/-- The large leading term in the logarithm of the profile cancels on each cell. -/
theorem log_drop_le_cell {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) (J : N01aNegativeComponent D) {m : ℕ}
    (hcell : J.interval ⊆ D.cells m) :
    Real.log (D.w J.left) - Real.log (D.w J.right) ≤
      |Real.log (C 0)| + 2 * C 0 * (D.cellIndex m : ℝ) ^ 2 := by
  have hl := J.log_bounds_on_closed_interval hD hcell J.left
    (left_mem_Icc.mpr J.left_lt_right.le)
  have hr := J.log_bounds_on_closed_interval hD hcell J.right
    (right_mem_Icc.mpr J.left_lt_right.le)
  linarith only [hl.2, hr.1, le_abs_self (Real.log (C 0))]

end N01aNegativeComponent

/-- One constant controls the variation of every component hosted by any cell. -/
theorem n01a_negativeComponent_variation_uniform_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (J : N01aNegativeComponent D) (m : ℕ),
      J.interval ⊆ D.cells m →
      (∫ r in J.left..J.right, |deriv D.w r / D.w r|) ≤
        K * (1 + (D.cellIndex m : ℝ) ^ 2) := by
  obtain ⟨C, hC⟩ := hD
  let K : ℝ := |Real.log (C 0)| + 2 * C 0 + 1
  have hC0 : 0 < C 0 := hC.2.2.1 0
  have hK : 0 < K := by
    dsimp only [K]
    linarith only [abs_nonneg (Real.log (C 0)), hC0]
  have hlog : |Real.log (C 0)| ≤ K := by dsimp only [K]; linarith only [hC0]
  have hcoeff : 2 * C 0 ≤ K := by
    dsimp only [K]
    linarith only [abs_nonneg (Real.log (C 0))]
  refine ⟨K, hK, fun J m hcell => ?_⟩
  calc
    _ = Real.log (D.w J.left) - Real.log (D.w J.right) :=
      J.integral_abs_logDerivative hC.1
    _ ≤ |Real.log (C 0)| + 2 * C 0 * (D.cellIndex m : ℝ) ^ 2 :=
      J.log_drop_le_cell hC hcell
    _ ≤ K + K * (D.cellIndex m : ℝ) ^ 2 :=
      add_le_add hlog (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))
    _ = K * (1 + (D.cellIndex m : ℝ) ^ 2) := by ring

end ContinuousFlexibility.Statements
