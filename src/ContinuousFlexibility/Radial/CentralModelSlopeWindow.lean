module

public import ContinuousFlexibility.Radial.CentralStatementBridges

/-!
# A fixed coercive window for the central model

The true radial logarithmic profile slope tends to one on both ends.
The model buffer can therefore be chosen beyond a single radius where
the slope is at least three quarters. This radius is fixed before any
selected tails or retained-cone lengths are chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology

theorem exists_centralModel_logSlope_window :
    ∃ Tmin : ℝ, 8 ≤ Tmin ∧ sqrt centralOscillatorA + 2 ≤ Tmin ∧
      ∀ T : ℝ, Tmin ≤ T → ∀ r : ℝ, 0 < r →
        (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
        (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r := by
  let f : ℝ → ℝ := fun x =>
    (x ^ 2 - centralOscillatorA) / centralRadiusLogDerivative x ^ 2
  have hleft : Tendsto (fun L : ℝ => f (-L)) atTop (𝓝 1) := by
    simpa only [centralRadialProfile_logarithmic_derivative (by norm_num : (0 : ℝ) < 1)] using
      (centralRadialProfile_left_logarithmic_slope_tendsto (by norm_num : (0 : ℝ) < 1))
  have hright : Tendsto f atTop (𝓝 1) := centralRightProfileSlope_tendsto
  have hboth : ∀ᶠ L : ℝ in atTop, (3 / 4 : ℝ) ≤ f (-L) ∧ (3 / 4 : ℝ) ≤ f L := by
    filter_upwards [hleft.eventually (eventually_gt_nhds (by norm_num : (3 / 4 : ℝ) < 1)),
      hright.eventually (eventually_gt_nhds (by norm_num : (3 / 4 : ℝ) < 1))] with L hL hR
    exact ⟨hL.le, hR.le⟩
  obtain ⟨R, hR⟩ := eventually_atTop.1 hboth
  let Tmin := max 8 (max (sqrt centralOscillatorA + 2) R)
  refine ⟨Tmin, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro T hT r hr hout
  let x := centralModelCoordinate r
  have hx : centralRadius x = r := centralRadius_modelCoordinate hr
  have hRT : R ≤ T :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hvalue : r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r = f x := by
    rw [← hx, centralRadialProfile_radial_logarithmic_derivative]
    rfl
  rw [hvalue]
  rcases hout with h | h
  · have hxT : x ≤ -T := strictMono_centralRadius.le_iff_le.mp (by rwa [hx])
    have hRx : R ≤ -x := hRT.trans (by linarith only [hxT])
    simpa only [neg_neg] using (hR (-x) hRx).1
  · have hxT : T ≤ x := strictMono_centralRadius.le_iff_le.mp (by rwa [hx])
    exact (hR x (hRT.trans hxT)).2

end ContinuousFlexibility.Radial
