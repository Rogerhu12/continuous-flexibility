module

public import ContinuousFlexibility.Radial.MorseJoinActualGerms
public import ContinuousFlexibility.Scalar.Normalization
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Globally smooth scalar power perturbations

The physical composition interface requires a globally smooth scalar map
which vanishes at zero. The actual powers needed by the scalar formulas are
only smooth away from their singular base. The existing compact germ-extension
theorem supplies a genuine global map, with the same germ at every point of
the fixed interval [-1/2, 1/2].
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

theorem exists_scalarPowerPerturbation (α : ℝ) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      ∀ x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        F =ᶠ[𝓝 x] (fun y : ℝ => (1 + y) ^ α - 1) := by
  have hbase : ContDiffOn ℝ ∞ (fun y : ℝ => 1 + y)
      (Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ)) :=
    contDiffOn_const.add contDiffOn_id
  have hf : ContDiffOn ℝ ∞ (fun y : ℝ => (1 + y) ^ α - 1)
      (Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ)) := by
    refine (hbase.rpow_const_of_ne ?_).sub contDiffOn_const
    intro y hy
    have hpos : 0 < 1 + y := by linarith [hy.1]
    exact hpos.ne'
  exact Radial.exists_contDiff_joinGerm_extension
    (u := -(3 / 4 : ℝ)) (v := (3 / 4 : ℝ))
    (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hf

/-- A fixed globally smooth extension of the actual near-zero power difference. -/
def scalarPowerPerturbation (α : ℝ) : ℝ → ℝ :=
  (exists_scalarPowerPerturbation α).choose

theorem scalarPowerPerturbation_contDiff (α : ℝ) :
    ContDiff ℝ ∞ (scalarPowerPerturbation α) :=
  (exists_scalarPowerPerturbation α).choose_spec.1

theorem scalarPowerPerturbation_hasCompactSupport (α : ℝ) :
    HasCompactSupport (scalarPowerPerturbation α) :=
  (exists_scalarPowerPerturbation α).choose_spec.2.1

/-- The whole germ is retained, including at the two ends of the fixed interval. -/
theorem scalarPowerPerturbation_eventuallyEq (α : ℝ) {x : ℝ}
    (hx : |x| ≤ 1 / 2) :
    scalarPowerPerturbation α =ᶠ[𝓝 x] (fun y : ℝ => (1 + y) ^ α - 1) :=
  (exists_scalarPowerPerturbation α).choose_spec.2.2 x (abs_le.mp hx)

theorem scalarPowerPerturbation_eq (α : ℝ) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    scalarPowerPerturbation α x = (1 + x) ^ α - 1 :=
  (scalarPowerPerturbation_eventuallyEq α hx).eq_of_nhds

@[simp] theorem scalarPowerPerturbation_zero (α : ℝ) :
    scalarPowerPerturbation α 0 = 0 := by
  rw [scalarPowerPerturbation_eq α (by norm_num : |(0 : ℝ)| ≤ 1 / 2)]
  simp only [add_zero, Real.one_rpow, sub_self]

/-- The square-root perturbation used by the coframe. -/
theorem scalarPowerPerturbation_half_eq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    scalarPowerPerturbation (1 / 2 : ℝ) x = Real.sqrt (1 + x) - 1 := by
  simpa only [Real.sqrt_eq_rpow] using scalarPowerPerturbation_eq (1 / 2 : ℝ) hx

/-- The reciprocal perturbation used by the normalized Q factor. -/
theorem scalarPowerPerturbation_neg_one_eq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    scalarPowerPerturbation (-1 : ℝ) x = (1 + x)⁻¹ - 1 := by
  simpa only [Real.rpow_neg_one] using scalarPowerPerturbation_eq (-1 : ℝ) hx

/-- The inverse-root perturbation used by the connection and corrected slope. -/
theorem scalarPowerPerturbation_neg_half_eq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    scalarPowerPerturbation (-(1 / 2) : ℝ) x = (Real.sqrt (1 + x))⁻¹ - 1 := by
  have hpos : 0 < 1 + x := by linarith [(abs_le.mp hx).1]
  rw [scalarPowerPerturbation_eq (-(1 / 2) : ℝ) hx,
    Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow]

/-- The inverse-three-halves perturbation used by the actual residual and
principal scalar coefficients. -/
theorem scalarPowerPerturbation_neg_three_halves_eq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    scalarPowerPerturbation (-(3 / 2) : ℝ) x = inverseDThreeHalves (1 + x) - 1 := by
  have hpos : 0 < 1 + x := by linarith [(abs_le.mp hx).1]
  rw [scalarPowerPerturbation_eq (-(3 / 2) : ℝ) hx]
  have hp : (1 + x) ^ (-(3 / 2) : ℝ) = inverseDThreeHalves (1 + x) := by
    rw [show (-(3 / 2) : ℝ) = -(1 + 1 / 2) by norm_num,
      Real.rpow_neg hpos.le, Real.rpow_add hpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
    simp only [inverseDThreeHalves, one_div]
  exact congrArg (fun v : ℝ => v - 1) hp

end ContinuousFlexibility.Statements
