module

public import ContinuousFlexibility.Radial.CentralModel

/-!
# The two simple turning points of the actual central profile

This is the turning-point assertion after `eq:rad-eq-sc6b` in Section 4.
The derivatives below are derivatives with respect to the actual radius,
using the constructed increasing radius and its smooth inverse. No
closed-domain spectral or resolvent statement is asserted here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Differentiating the actual profile equation at a turning point gives
the nonzero second derivative after the genuine radius change. -/
theorem centralRadialProfile_second_deriv_scaled_at_turning
    (c x : ℝ) (hx : x ^ 2 = centralOscillatorA) :
    deriv (deriv (centralRadialProfile c)) (centralRadius x) *
        (deriv centralRadius x) ^ 2 =
      2 * x * c * centralDensityRoot x ^ 2 * centralRadius x := by
  have hR := (contDiff_centralRadius.differentiable (by simp) x).hasDerivAt
  have hR' := ((contDiff_infty_iff_deriv.mp contDiff_centralRadius).2.differentiable
    (by simp) x).hasDerivAt
  have hw' := (((contDiffAt_centralRadialProfile c x).derivWithin
    (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hleft := (hw'.comp x hR).mul hR'
  let K : ℝ → ℝ := fun y => c * centralDensityRoot y ^ 2 * centralRadius y
  have hK : ContDiff ℝ ∞ K :=
    (contDiff_const.mul (contDiff_centralDensityRoot.pow 2)).mul contDiff_centralRadius
  have hq : HasDerivAt (fun y : ℝ => y ^ 2 - centralOscillatorA) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).sub_const centralOscillatorA using 1 <;> simp
  have hright := ((hK.differentiable (by simp) x).hasDerivAt).mul hq
  have hd := hleft.unique (hright.congr_of_eventuallyEq
    (Eventually.of_forall (centralRadialProfile_deriv_scaled c)))
  have hw0 : deriv (centralRadialProfile c) (centralRadius x) = 0 := by
    have h := centralRadialProfile_deriv_scaled c x
    rw [hx, sub_self, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (deriv_centralRadius_pos x).ne'
  dsimp only [K] at hd
  simp only [Function.comp_apply, hw0, hx, sub_self, mul_zero, zero_mul, zero_add,
    add_zero] at hd
  nlinarith only [hd]

/-- On the entire positive radial axis, these are exactly the two
critical points of the constructed positive central profile. -/
theorem centralRadialProfile_critical_iff
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    deriv (centralRadialProfile c) r = 0 ↔
      r = centralRadius (-sqrt centralOscillatorA) ∨
      r = centralRadius (sqrt centralOscillatorA) := by
  have hsq := sq_sqrt centralOscillatorA_pos.le
  constructor
  · intro hz
    have hx : centralModelCoordinate r ^ 2 = centralOscillatorA := by
      apply (centralRadialProfile_deriv_zero_iff hc _).mp
      rw [centralRadius_modelCoordinate hr]
      exact hz
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans hsq.symm) with h | h
    · exact Or.inr ((centralRadius_modelCoordinate hr).symm.trans (congrArg centralRadius h))
    · exact Or.inl ((centralRadius_modelCoordinate hr).symm.trans (congrArg centralRadius h))
  · rintro (rfl | rfl)
    · exact (centralRadialProfile_deriv_zero_iff hc _).mpr (by simpa only [neg_sq] using hsq)
    · exact (centralRadialProfile_deriv_zero_iff hc _).mpr hsq

theorem central_turning_radii_pos_ordered :
    0 < centralRadius (-sqrt centralOscillatorA) ∧
      centralRadius (-sqrt centralOscillatorA) < centralRadius (sqrt centralOscillatorA) := by
  refine ⟨centralRadius_pos _, strictMono_centralRadius ?_⟩
  have hs := sqrt_pos.mpr centralOscillatorA_pos
  linarith

theorem centralRadialProfile_second_deriv_left_neg {c : ℝ} (hc : 0 < c) :
    deriv (deriv (centralRadialProfile c))
      (centralRadius (-sqrt centralOscillatorA)) < 0 := by
  have hx : (-sqrt centralOscillatorA) ^ 2 = centralOscillatorA := by
    simpa only [neg_sq] using sq_sqrt centralOscillatorA_pos.le
  have hd := centralRadialProfile_second_deriv_scaled_at_turning c _ hx
  have hs : 0 < sqrt centralOscillatorA := sqrt_pos.mpr centralOscillatorA_pos
  have hneg : 2 * (-sqrt centralOscillatorA) * c *
      centralDensityRoot (-sqrt centralOscillatorA) ^ 2 *
      centralRadius (-sqrt centralOscillatorA) < 0 :=
    mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hc)
        (sq_pos_of_pos (centralDensityRoot_pos _))) (centralRadius_pos _)
  have hp := sq_pos_of_pos (deriv_centralRadius_pos (-sqrt centralOscillatorA))
  nlinarith only [hd, hneg, hp]

theorem centralRadialProfile_second_deriv_right_pos {c : ℝ} (hc : 0 < c) :
    0 < deriv (deriv (centralRadialProfile c))
      (centralRadius (sqrt centralOscillatorA)) := by
  have hd := centralRadialProfile_second_deriv_scaled_at_turning c _
    (sq_sqrt centralOscillatorA_pos.le)
  have hpos : 0 < 2 * sqrt centralOscillatorA * c *
      centralDensityRoot (sqrt centralOscillatorA) ^ 2 *
      centralRadius (sqrt centralOscillatorA) :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (sqrt_pos.mpr centralOscillatorA_pos)) hc)
      (sq_pos_of_pos (centralDensityRoot_pos _))) (centralRadius_pos _)
  have hp := sq_pos_of_pos (deriv_centralRadius_pos (sqrt centralOscillatorA))
  nlinarith only [hd, hpos, hp]

end ContinuousFlexibility.Radial
