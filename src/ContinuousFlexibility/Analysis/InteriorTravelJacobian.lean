import ContinuousFlexibility.Analysis.RootTravelDifferential

/-!
# The actual Jacobian after converting travel time to the root coordinate

The scalar root-power derivative rescales the first row of any travel
chart. Its determinant lower bound therefore uses the actual travel
Jacobian and an upper bound on the square root of the root coordinate.
The characteristic formula below is the existing principal-density
calculation expressed directly with the two physical speeds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def rootPowerTravelChart (F : PolarPoint → PolarPoint) (p : PolarPoint) : PolarPoint :=
  (rootTravelPower (F p).1, (F p).2)

theorem fderiv_rootPowerTravelChart_apply
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (hτ : 0 < (F p).1) (v : PolarPoint) :
    fderiv ℝ (rootPowerTravelChart F) p v =
      ((Real.sqrt (rootTravelPower (F p).1))⁻¹ * (fderiv ℝ F p v).1,
        (fderiv ℝ F p v).2) := by
  have hd := ((hasDerivAt_rootTravelPower hτ).comp_hasFDerivAt p
    hF.hasFDerivAt.fst).prodMk hF.hasFDerivAt.snd
  have he : (fun q : PolarPoint =>
      ((rootTravelPower ∘ (fun y => (F y).1)) q, (F q).2)) =
      rootPowerTravelChart F := by
    funext q
    simp only [Function.comp_apply, rootPowerTravelChart]
  rw [he] at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]

theorem planeJacobian_rootPowerTravelChart
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (hτ : 0 < (F p).1) :
    planeJacobian (rootPowerTravelChart F) p =
      (Real.sqrt (rootTravelPower (F p).1))⁻¹ * planeJacobian F p :=
  planeJacobian_of_scaled_radial_differential
    (fderiv_rootPowerTravelChart_apply hF hτ (1, 0))
    (fderiv_rootPowerTravelChart_apply hF hτ (0, 1))

theorem abs_planeJacobian_rootPowerTravelChart
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (hτ : 0 < (F p).1) :
    |planeJacobian (rootPowerTravelChart F) p| =
      |planeJacobian F p| / Real.sqrt (rootTravelPower (F p).1) := by
  have hξ : 0 < rootTravelPower (F p).1 :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hτ) _
  rw [planeJacobian_rootPowerTravelChart hF hτ, abs_mul,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hξ)), inv_mul_eq_div]

/-- Both radial orientations satisfy this same absolute-Jacobian bound. -/
theorem rootPowerTravelChart_jacobian_lower
    {F : PolarPoint → PolarPoint} {p : PolarPoint} {κ u : ℝ}
    (hF : DifferentiableAt ℝ F p) (hτ : 0 < (F p).1)
    (hκ : 0 ≤ κ) (hJ : κ ≤ |planeJacobian F p|)
    (hu : Real.sqrt (rootTravelPower (F p).1) ≤ u) :
    κ / u ≤ |planeJacobian (rootPowerTravelChart F) p| := by
  have hξ : 0 < rootTravelPower (F p).1 :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hτ) _
  have hv : 0 < Real.sqrt (rootTravelPower (F p).1) := Real.sqrt_pos.mpr hξ
  rw [abs_planeJacobian_rootPowerTravelChart hF hτ]
  exact (div_le_div_of_nonneg_left hκ hv hu).trans
    (div_le_div_of_nonneg_right hJ hv.le)

theorem planeJacobian_characteristicTravelChart_speed_gap
    {U V : PolarPoint → ℝ} {p : PolarPoint} {fplus fminus : ℝ}
    (hU : DifferentiableAt ℝ U p) (hV : DifferentiableAt ℝ V p)
    (hUr : radialPartial U p = -fplus * angularPartial U p)
    (hVr : radialPartial V p = -fminus * angularPartial V p) :
    planeJacobian (characteristicTravelChart U V) p =
      (fplus - fminus) * angularPartial U p * angularPartial V p / 2 := by
  have hplus : (fplus + fminus) / 2 + (fplus - fminus) / 2 = fplus := by ring
  have hminus : (fplus + fminus) / 2 - (fplus - fminus) / 2 = fminus := by ring
  have hUr' : radialPartial U p =
      -((fplus + fminus) / 2 + (fplus - fminus) / 2) * angularPartial U p := by
    rw [hplus]
    exact hUr
  have hVr' : radialPartial V p =
      -((fplus + fminus) / 2 - (fplus - fminus) / 2) * angularPartial V p := by
    rw [hminus]
    exact hVr
  rw [planeJacobian_characteristicTravelChart hU hV hUr' hVr']
  ring

/-- Reversing travel from a fixed terminal section changes only the sign. -/
theorem planeJacobian_reflected_travel
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (c : ℝ) :
    planeJacobian (fun q => (c - (F q).1, (F q).2)) p = -planeJacobian F p := by
  have hd := ((hasFDerivAt_const (c := c) (x := p)).fun_sub
    hF.hasFDerivAt.fst).prodMk hF.hasFDerivAt.snd
  simp only [planeJacobian, hd.fderiv, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', zero_sub]
  ring

end ContinuousFlexibility.Analysis
