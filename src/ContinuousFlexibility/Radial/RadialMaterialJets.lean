import ContinuousFlexibility.Radial.CentralLeftAsymptotics
import ContinuousFlexibility.Radial.CentralRightAsymptotics

/-!
# Actual derivatives in logarithmic radial coordinate

The inverse coordinate is the genuine inverse of the constructed radius.
The oriented material operator includes the minus sign on the left ray.
Its iterates agree with actual derivatives of the pullback, and each
application gains two symbol orders without changing the tail threshold.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem RadialSymbolBounds.deriv {L0 s : ℝ} {f : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) :
    RadialSymbolBounds L0 (s - 1) (deriv f) := by
  refine ⟨hf.1.deriv_of_isOpen isOpen_Ioi (by simp), ?_⟩
  intro r
  obtain ⟨C, hC, hCf⟩ := hf.2 (r + 1)
  refine ⟨C, hC, ?_⟩
  intro L hL0 hL
  rw [← iteratedDeriv_succ']
  simpa only [show s - ((r + 1 : ℕ) : ℝ) = (s - 1) - (r : ℝ) by push_cast; ring] using
    hCf L hL0 hL

/-- A real vector field acting on actual derivatives. -/
def radialMaterialDeriv (a f : ℝ → ℝ) (L : ℝ) : ℝ := a L * deriv f L

theorem contDiff_radialMaterialDeriv {a f : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (radialMaterialDeriv a f) :=
  ha.mul (contDiff_infty_iff_deriv.mp hf).2

theorem contDiff_iterate_radialMaterialDeriv {a f : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ ((radialMaterialDeriv a)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact contDiff_radialMaterialDeriv ha ih

theorem deriv_comp_radialMaterialDeriv {a η f : ℝ → ℝ}
    (hη : ∀ y : ℝ, HasDerivAt η (a (η y)) y) (hf : ContDiff ℝ ∞ f) :
    deriv (fun y => f (η y)) = fun y => radialMaterialDeriv a f (η y) := by
  funext y
  have hd := ((hf.differentiable (by simp) (η y)).hasDerivAt).comp y (hη y)
  change HasDerivAt (fun y => f (η y)) _ y at hd
  rw [hd.deriv]
  exact mul_comm _ _

/-- Global smoothness makes the iterated chain rule a genuine function
identity, including order zero. -/
theorem iteratedDeriv_comp_radialMaterialDeriv {a η f : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hη : ∀ y : ℝ, HasDerivAt η (a (η y)) y)
    (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    iteratedDeriv k (fun y => f (η y)) =
      fun y => ((radialMaterialDeriv a)^[k] f) (η y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    exact deriv_comp_radialMaterialDeriv hη (contDiff_iterate_radialMaterialDeriv ha hf k)

theorem RadialSymbolBounds.materialDeriv {L0 s : ℝ} {a f : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (ha : RadialSymbolBounds L0 (-1) a) :
    RadialSymbolBounds L0 (s - 2) (radialMaterialDeriv a f) := by
  rw [show radialMaterialDeriv a f = a * _root_.deriv f from rfl]
  simpa only [show (-1 : ℝ) + (s - 1) = s - 2 by ring] using
    ha.mul hf.deriv

theorem RadialSymbolBounds.iterate_materialDeriv {L0 s : ℝ} {a f : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (ha : RadialSymbolBounds L0 (-1) a) (k : ℕ) :
    RadialSymbolBounds L0 (s - 2 * (k : ℝ)) ((radialMaterialDeriv a)^[k] f) := by
  induction k with
  | zero => simpa only [Function.iterate_zero, id_eq, Nat.cast_zero, mul_zero, sub_zero] using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hh := ih.materialDeriv ha
    simpa only [show s - 2 * (k : ℝ) - 2 = s - 2 * ((k + 1 : ℕ) : ℝ) by push_cast; ring] using hh

/-- The actual oscillator coordinate as a function of logarithmic radius. -/
def centralLogModelCoordinate (y : ℝ) : ℝ := centralModelCoordinate (exp y)

theorem contDiff_centralLogModelCoordinate : ContDiff ℝ ∞ centralLogModelCoordinate := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hx := contDiffAt_centralModelCoordinate (centralModelCoordinate (exp y))
  rw [centralRadius_modelCoordinate (exp_pos y)] at hx
  exact hx.comp y contDiff_exp.contDiffAt

theorem centralLogModelCoordinate_logRadius (x : ℝ) :
    centralLogModelCoordinate (log (centralRadius x)) = x := by
  rw [centralLogModelCoordinate, exp_log (centralRadius_pos x), centralModelCoordinate_radius]

def centralOrientedCoordinate (ε y : ℝ) : ℝ := ε * centralLogModelCoordinate y

def centralMaterialCoefficient (ε L : ℝ) : ℝ :=
  ε * (centralRadiusLogDerivative (ε * L))⁻¹

theorem contDiff_centralMaterialCoefficient (ε : ℝ) :
    ContDiff ℝ ∞ (centralMaterialCoefficient ε) :=
  contDiff_const.mul
    ((contDiff_centralRadiusLogDerivative.comp (contDiff_const.mul contDiff_id)).inv
      (fun L => (centralRadiusLogDerivative_pos (ε * L)).ne'))

theorem contDiff_centralOrientedCoordinate (ε : ℝ) :
    ContDiff ℝ ∞ (centralOrientedCoordinate ε) :=
  contDiff_const.mul contDiff_centralLogModelCoordinate

theorem hasDerivAt_centralOrientedCoordinate {ε : ℝ} (hε : ε * ε = 1) (y : ℝ) :
    HasDerivAt (centralOrientedCoordinate ε)
      (centralMaterialCoefficient ε (centralOrientedCoordinate ε y)) y := by
  have hd := (hasDerivAt_centralLogRadiusInverse y).const_mul ε
  change HasDerivAt (centralOrientedCoordinate ε)
    (ε * (centralRadiusLogDerivative (centralLogModelCoordinate y))⁻¹) y at hd
  simpa only [centralMaterialCoefficient, centralOrientedCoordinate, ← mul_assoc, hε, one_mul] using hd

theorem centralOrientedCoordinate_logRadius {ε : ℝ} (hε : ε * ε = 1) (L : ℝ) :
    centralOrientedCoordinate ε (log (centralRadius (ε * L))) = L := by
  rw [centralOrientedCoordinate, centralLogModelCoordinate_logRadius, ← mul_assoc, hε, one_mul]

/-- This equality differentiates the actual logarithmic radial pullback. -/
theorem iteratedDeriv_comp_centralOrientedCoordinate {ε : ℝ} (hε : ε * ε = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    iteratedDeriv k (fun y => f (centralOrientedCoordinate ε y)) =
      fun y => ((radialMaterialDeriv (centralMaterialCoefficient ε))^[k] f)
        (centralOrientedCoordinate ε y) :=
  iteratedDeriv_comp_radialMaterialDeriv (contDiff_centralMaterialCoefficient ε)
    (hasDerivAt_centralOrientedCoordinate hε) hf k

theorem centralMaterialCoefficient_right_symbol :
    RadialSymbolBounds 1 (-1) (centralMaterialCoefficient 1) := by
  rw [show centralMaterialCoefficient 1 = (fun L => (centralRadiusLogDerivative L)⁻¹) by
    funext L; simp only [centralMaterialCoefficient, one_mul]]
  exact
    centralRadiusLogDerivative_right_inverse_symbol

theorem centralMaterialCoefficient_left_symbol :
    RadialSymbolBounds (centralRadiusAlpha + 1) (-1) (centralMaterialCoefficient (-1)) := by
  rw [show centralMaterialCoefficient (-1) =
      (fun L => -(centralRadiusLogDerivative (-L))⁻¹) by
    funext L; simp only [centralMaterialCoefficient, neg_one_mul]]
  simpa only [neg_one_mul] using
    centralRadiusLogDerivative_left_inverse_symbol.const_mul (-1)

/-- Material derivatives gain two powers on the same tail; only their
constants depend on the number of derivatives. -/
theorem central_material_pullback_bound {ε L0 s : ℝ} (hε : ε * ε = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialSymbolBounds L0 s f)
    (ha : RadialSymbolBounds L0 (-1) (centralMaterialCoefficient ε)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, L0 ≤ L → 0 < L →
      ‖iteratedDeriv k (fun y => f (centralOrientedCoordinate ε y))
        (log (centralRadius (ε * L)))‖ ≤ C * L ^ (s - 2 * (k : ℝ)) := by
  obtain ⟨C, hC, hCf⟩ := (hs.iterate_materialDeriv ha k).2 0
  refine ⟨C, hC, ?_⟩
  intro L hL0 hL
  rw [iteratedDeriv_comp_centralOrientedCoordinate hε hf k]
  change ‖((radialMaterialDeriv (centralMaterialCoefficient ε))^[k] f)
    (centralOrientedCoordinate ε (log (centralRadius (ε * L))))‖ ≤ _
  rw [centralOrientedCoordinate_logRadius hε L]
  simpa only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] using hCf L hL0 hL

/-- The actual logarithmic slope of the surviving radial height. -/
def centralHeightLogSlope (y : ℝ) : ℝ :=
  deriv (fun t : ℝ => centralKernelHeight (exp t)) y / centralKernelHeight (exp y)

/-- The actual logarithmic derivative of the positive radial profile. -/
def centralProfileLogSlope (c y : ℝ) : ℝ :=
  deriv (fun t : ℝ => log (centralRadialProfile c (exp t))) y

def centralHeightSlopeOnRay (ε L : ℝ) : ℝ :=
  (centralRadiusA - 2 * (ε * L)) / centralRadiusLogDerivative (ε * L)

def centralProfileSlopeOnRay (ε L : ℝ) : ℝ :=
  ((ε * L) ^ 2 - centralOscillatorA) / centralRadiusLogDerivative (ε * L) ^ 2

theorem contDiff_centralHeightSlopeOnRay (ε : ℝ) :
    ContDiff ℝ ∞ (centralHeightSlopeOnRay ε) :=
  (contDiff_const.sub (contDiff_const.mul (contDiff_const.mul contDiff_id))).div
    (contDiff_centralRadiusLogDerivative.comp (contDiff_const.mul contDiff_id))
    (fun L => (centralRadiusLogDerivative_pos (ε * L)).ne')

theorem contDiff_centralProfileSlopeOnRay (ε : ℝ) :
    ContDiff ℝ ∞ (centralProfileSlopeOnRay ε) :=
  (((contDiff_const.mul contDiff_id).pow 2).sub contDiff_const).div
    ((contDiff_centralRadiusLogDerivative.comp (contDiff_const.mul contDiff_id)).pow 2)
    (fun L => pow_ne_zero 2 (centralRadiusLogDerivative_pos (ε * L)).ne')

theorem centralHeightLogSlope_eq_oriented {ε : ℝ} (hε : ε * ε = 1) (y : ℝ) :
    centralHeightLogSlope y = centralHeightSlopeOnRay ε (centralOrientedCoordinate ε y) := by
  have hh := centralKernelHeight_logarithmic_derivative (centralLogModelCoordinate y)
  have hr : centralRadius (centralLogModelCoordinate y) = exp y :=
    centralRadius_modelCoordinate (exp_pos y)
  rw [hr, log_exp] at hh
  simpa only [centralHeightLogSlope, centralHeightSlopeOnRay, centralOrientedCoordinate,
    ← mul_assoc, hε, one_mul] using hh

theorem centralProfileLogSlope_eq_oriented {ε c : ℝ} (hε : ε * ε = 1)
    (hc : 0 < c) (y : ℝ) :
    centralProfileLogSlope c y = centralProfileSlopeOnRay ε (centralOrientedCoordinate ε y) := by
  have hh := centralRadialProfile_logarithmic_derivative hc (centralLogModelCoordinate y)
  have hr : centralRadius (centralLogModelCoordinate y) = exp y :=
    centralRadius_modelCoordinate (exp_pos y)
  rw [hr, log_exp] at hh
  simpa only [centralProfileLogSlope, centralProfileSlopeOnRay, centralOrientedCoordinate,
    ← mul_assoc, hε, one_mul] using hh

private theorem height_material_bound {ε L0 : ℝ} (hε : ε * ε = 1)
    (hs : RadialSymbolBounds L0 0 (centralHeightSlopeOnRay ε))
    (ha : RadialSymbolBounds L0 (-1) (centralMaterialCoefficient ε)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, L0 ≤ L → 0 < L →
      ‖iteratedDeriv k centralHeightLogSlope (log (centralRadius (ε * L)))‖ ≤
        C * L ^ (-2 * (k : ℝ)) := by
  have heq : centralHeightLogSlope =
      fun y => centralHeightSlopeOnRay ε (centralOrientedCoordinate ε y) :=
    funext (centralHeightLogSlope_eq_oriented hε)
  rw [heq]
  simpa only [zero_sub, neg_mul] using
    central_material_pullback_bound hε (contDiff_centralHeightSlopeOnRay ε) hs ha k

private theorem profile_material_bound {ε L0 c : ℝ} (hε : ε * ε = 1) (hc : 0 < c)
    (hs : RadialSymbolBounds L0 0 (centralProfileSlopeOnRay ε))
    (ha : RadialSymbolBounds L0 (-1) (centralMaterialCoefficient ε)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, L0 ≤ L → 0 < L →
      ‖iteratedDeriv k (centralProfileLogSlope c) (log (centralRadius (ε * L)))‖ ≤
        C * L ^ (-2 * (k : ℝ)) := by
  have heq : centralProfileLogSlope c =
      fun y => centralProfileSlopeOnRay ε (centralOrientedCoordinate ε y) :=
    funext (centralProfileLogSlope_eq_oriented hε hc)
  rw [heq]
  simpa only [zero_sub, neg_mul] using
    central_material_pullback_bound hε (contDiff_centralProfileSlopeOnRay ε) hs ha k

theorem centralHeightLogSlope_right_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      ‖iteratedDeriv k centralHeightLogSlope (log (centralRadius L))‖ ≤
        C * L ^ (-2 * (k : ℝ)) := by
  have hs : RadialSymbolBounds 1 0 (centralHeightSlopeOnRay 1) := by
    rw [show centralHeightSlopeOnRay 1 =
        (fun L => (centralRadiusA - 2 * L) / centralRadiusLogDerivative L) by
      funext L; simp only [centralHeightSlopeOnRay, one_mul]]
    exact centralRightHeightSlope_symbol
  obtain ⟨C, hC, hCL⟩ := height_material_bound (by norm_num : (1 : ℝ) * 1 = 1)
    hs centralMaterialCoefficient_right_symbol k
  exact ⟨C, hC, fun L hL => by simpa only [one_mul] using hCL L hL (zero_lt_one.trans_le hL)⟩

theorem centralHeightLogSlope_left_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, centralRadiusAlpha + 1 ≤ L →
      ‖iteratedDeriv k centralHeightLogSlope (log (centralRadius (-L)))‖ ≤
        C * L ^ (-2 * (k : ℝ)) := by
  have hs : RadialSymbolBounds (centralRadiusAlpha + 1) 0 (centralHeightSlopeOnRay (-1)) := by
    rw [show centralHeightSlopeOnRay (-1) =
        (fun L => (centralRadiusA + 2 * L) / centralRadiusLogDerivative (-L)) by
      funext L; simp only [centralHeightSlopeOnRay, neg_one_mul, mul_neg, sub_neg_eq_add]]
    exact centralKernelHeight_left_slope_symbol
  obtain ⟨C, hC, hCL⟩ := height_material_bound (by norm_num : (-1 : ℝ) * -1 = 1)
    hs centralMaterialCoefficient_left_symbol k
  refine ⟨C, hC, ?_⟩
  intro L hL
  simpa only [neg_one_mul] using hCL L hL (by linarith [centralRadiusAlpha_gt_half])

theorem centralProfileLogSlope_right_derivative_bound {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      ‖iteratedDeriv k (centralProfileLogSlope c) (log (centralRadius L))‖ ≤
        C * L ^ (-2 * (k : ℝ)) := by
  have hs : RadialSymbolBounds 1 0 (centralProfileSlopeOnRay 1) := by
    rw [show centralProfileSlopeOnRay 1 =
        (fun L => (L ^ 2 - centralOscillatorA) / centralRadiusLogDerivative L ^ 2) by
      funext L; simp only [centralProfileSlopeOnRay, one_mul]]
    exact centralRightProfileSlope_symbol
  obtain ⟨C, hC, hCL⟩ := profile_material_bound (by norm_num : (1 : ℝ) * 1 = 1)
    hc hs centralMaterialCoefficient_right_symbol k
  exact ⟨C, hC, fun L hL => by simpa only [one_mul] using hCL L hL (zero_lt_one.trans_le hL)⟩

theorem centralProfileLogSlope_left_derivative_bound {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, centralRadiusAlpha + 1 ≤ L →
      ‖iteratedDeriv k (centralProfileLogSlope c) (log (centralRadius (-L)))‖ ≤
        C * L ^ (-2 * (k : ℝ)) := by
  have hs : RadialSymbolBounds (centralRadiusAlpha + 1) 0 (centralProfileSlopeOnRay (-1)) := by
    rw [show centralProfileSlopeOnRay (-1) =
        (fun L => (L ^ 2 - centralOscillatorA) / centralRadiusLogDerivative (-L) ^ 2) by
      funext L; simp only [centralProfileSlopeOnRay, neg_one_mul, neg_sq]]
    exact centralRadialProfile_left_slope_symbol
  obtain ⟨C, hC, hCL⟩ := profile_material_bound (by norm_num : (-1 : ℝ) * -1 = 1)
    hc hs centralMaterialCoefficient_left_symbol k
  refine ⟨C, hC, ?_⟩
  intro L hL
  simpa only [neg_one_mul] using hCL L hL (by linarith [centralRadiusAlpha_gt_half])

end ContinuousFlexibility.Radial
