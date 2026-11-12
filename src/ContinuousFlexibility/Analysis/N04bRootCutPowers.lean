import ContinuousFlexibility.Analysis.N04bCutPullback
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The actual root powers at a canonical cut

The root coordinate has inverse travel function (2/3) ξ^(3/2). The
canonical unknown carries the radial factor ξ^(-1/4). Their derivatives,
and the common travel value at (3T/4)^(2/3), give the fixed transmission
matrix without an assumed jet identity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n04bRootTravel (r : ℝ) : ℝ := (2 / 3 : ℝ) * r ^ (3 / 2 : ℝ)

def n04bRootGauge (r : ℝ) : ℝ := r ^ (-1 / 4 : ℝ)

def n04bRootCutRadius (T : ℝ) : ℝ := (3 * T / 4) ^ (2 / 3 : ℝ)

theorem n04bRootCutRadius_pos {T : ℝ} (hT : 0 < T) :
    0 < n04bRootCutRadius T := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem n04b_hasDerivAt_rootTravel {r : ℝ} (hr : 0 < r) :
    HasDerivAt n04bRootTravel (Real.sqrt r) r := by
  have h := (Real.hasDerivAt_rpow_const
    (x := r) (p := (3 / 2 : ℝ)) (Or.inl (ne_of_gt hr))).const_mul (2 / 3 : ℝ)
  change HasDerivAt (fun y : ℝ => (2 / 3 : ℝ) * y ^ (3 / 2 : ℝ))
    (Real.sqrt r) r
  apply h.congr_deriv
  norm_num [Real.sqrt_eq_rpow] <;> ring

theorem n04b_hasDerivAt_rootGauge {r : ℝ} (hr : 0 < r) :
    HasDerivAt n04bRootGauge (-n04bRootGauge r / (4 * r)) r := by
  have h := Real.hasDerivAt_rpow_const
    (x := r) (p := (-1 / 4 : ℝ)) (Or.inl (ne_of_gt hr))
  change HasDerivAt (fun x : ℝ => x ^ (-1 / 4 : ℝ))
    (-r ^ (-1 / 4 : ℝ) / (4 * r)) r
  convert h using 1
  rw [Real.rpow_sub hr, Real.rpow_one]
  field_simp [ne_of_gt hr]
  <;> ring

theorem n04b_rootTravel_cut {T : ℝ} (hT : 0 < T) :
    n04bRootTravel (n04bRootCutRadius T) = T / 2 := by
  have hp : 0 ≤ 3 * T / 4 := by positivity
  dsimp only [n04bRootTravel, n04bRootCutRadius]
  rw [← Real.rpow_mul hp]
  norm_num <;> ring

theorem n04b_rootGauge_eq_inv_sqrt_sqrt {r : ℝ} (hr : 0 < r) :
    n04bRootGauge r = (Real.sqrt (Real.sqrt r))⁻¹ := by
  have hs : Real.sqrt (Real.sqrt r) = r ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    norm_num
  rw [hs, n04bRootGauge, show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring,
    Real.rpow_neg hr.le]

/-- The actual root powers produce the fixed transmission matrix. The
travel-coordinate field G may depend on both travel and angle. -/
theorem n04b_root_gauged_transmission
    {T : ℝ} (hT : 0 < T) (θ : ℝ) (G : PolarPoint → ℝ)
    (hG : DifferentiableAt ℝ G (T / 2, θ)) :
    n04bGaugedTravel T (-1) n04bRootTravel n04bRootGauge G
        (n04bRootCutRadius T, θ) =
      n04bGaugedTravel T 1 n04bRootTravel n04bRootGauge G
        (n04bRootCutRadius T, θ) ∧
    radialPartial (n04bGaugedTravel T (-1) n04bRootTravel n04bRootGauge G)
        (n04bRootCutRadius T, θ) =
      -radialPartial (n04bGaugedTravel T 1 n04bRootTravel n04bRootGauge G)
          (n04bRootCutRadius T, θ) -
        n04bGaugedTravel T 1 n04bRootTravel n04bRootGauge G
          (n04bRootCutRadius T, θ) / (2 * n04bRootCutRadius T) := by
  have hr := n04bRootCutRadius_pos hT
  exact n04b_gauged_cut_transmission T (n04bRootCutRadius T) θ
    (Real.sqrt (n04bRootCutRadius T)) n04bRootTravel n04bRootGauge G
    (ne_of_gt hr) (n04b_hasDerivAt_rootTravel hr)
    (n04b_hasDerivAt_rootGauge hr) (n04b_rootTravel_cut hT) hG

end ContinuousFlexibility.Analysis
