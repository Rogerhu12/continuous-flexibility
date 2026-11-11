import ContinuousFlexibility.Radial.InnerCentralModelBorder
import ContinuousFlexibility.Radial.InnerLiouvillePoissonEquation
import ContinuousFlexibility.Radial.InnerLiouvillePoissonTransport

/-!
# The fixed temporary central column in the actual radial measure

The inverse-adjoint lift of the model source is exactly the R03 compact
auxiliary column. Once the cuts enclose its fixed support, its physical
L² class does not depend on the cuts. This identifies the scalar column
and row of the same local central inverse used in finite weak gluing.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

theorem continuous_centralAuxiliaryColumnFunction {height : ℝ} (hh : 0 < height) :
    Continuous (centralAuxiliaryColumnFunction height) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  by_cases hr : 0 < r
  · have hv : ContinuousAt (centralRadialVarpi height) r :=
      ((continuousOn_centralRadialVarpi height) r hr).continuousAt
        (isOpen_Ioi.mem_nhds hr)
    exact (continuousAt_const.mul contDiff_centralAuxiliaryFunction.continuous.continuousAt).div
      hv (centralRadialVarpi_pos hh hr).ne'
  · have hout : r ∉ tsupport centralAuxiliaryFunction :=
      fun h => hr (centralAuxiliaryFunction_tsupport_positive h)
    have hz : centralAuxiliaryColumnFunction height =ᶠ[𝓝 r] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hout] with y hy
      simp only [centralAuxiliaryColumnFunction, hy, mul_zero, zero_div]
    exact continuousAt_const.congr_of_eventuallyEq hz

/-- Enclosing the fixed model support encloses the actual compact
radial auxiliary column, including its values at the exterior cuts. -/
theorem innerCentralAuxiliaryColumnFunction_outside {height X₀ r : ℝ}
    (hh : 0 < height) (hX : innerCentralModelBorderRadius < X₀)
    (hr : r ∉ Ioo (centralRadius (-X₀)) (centralRadius X₀)) :
    centralAuxiliaryColumnFunction height r = 0 := by
  by_cases hrpos : 0 < r
  · let x := centralModelCoordinate r
    have hxR : centralRadius x = r := centralRadius_modelCoordinate hrpos
    have hxout : x ∉ tsupport innerCentralModelBorderFunction := by
      intro hx
      have hxbound := innerCentralModelBorderFunction_tsupport hx
      apply hr
      rw [← hxR]
      exact ⟨strictMono_centralRadius (by linarith only [hxbound.1, hX]),
        strictMono_centralRadius (by linarith only [hxbound.2, hX])⟩
    have hz := image_eq_zero_of_notMem_tsupport hxout
    rw [← hxR, ← innerCentralModelBorderFunction_physical hh x, hz, zero_div]
  · have hz : centralAuxiliaryFunction r = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h => hrpos (centralAuxiliaryFunction_tsupport_positive h))
    simp only [centralAuxiliaryColumnFunction, hz, mul_zero, zero_div]

section ActualMeasure

variable (D : ReferenceData) {height X₀ : ℝ}
  (hh : 0 < height) (hX : innerCentralModelBorderRadius < X₀)
  (hcore : Ioo (centralRadius (-X₀)) (centralRadius X₀) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc (-X₀) X₀,
    D.w (centralRadius x) = height * centralDensityRoot x ^ 2 * deriv centralRadius x)

include hX in
private theorem innerCentral_cut_order : -X₀ ≤ X₀ := by
  have hR := innerCentralModelBorderRadius_ge_one
  linarith only [hX, hR]

private theorem innerCentral_chart_positive (x : ℝ) (_hx : x ∈ Icc (-X₀) X₀) :
    0 < centralRadius x ∧ 0 < deriv centralRadius x ∧ 0 < centralDensityRoot x :=
  ⟨centralRadius_pos x, deriv_centralRadius_pos x, centralDensityRoot_pos x⟩

/-- The unique physical compact column, represented in the original
radial measure of the assembled reference. -/
def innerCentralPhysicalTemporaryColumn : RadialModeL2 D :=
  innerLiouvilleColumnLift D (innerCentral_cut_order hX) hh contDiff_centralRadius
    contDiff_centralDensityRoot innerCentral_chart_positive hcore hw innerCentralModelBorder

theorem innerCentralPhysicalTemporaryColumn_ae :
    (innerCentralPhysicalTemporaryColumn D hh hX hcore hw : ℝ → ℝ) =ᵐ[
      radialHilbertMeasure D] centralAuxiliaryColumnFunction height := by
  let g := innerCentralPhysicalTemporaryColumn D hh hX hcore hw
  have hin : (g : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo (centralRadius (-X₀)) (centralRadius X₀))]
      centralAuxiliaryColumnFunction height := by
    apply innerLiouvilleInterval_pushforward_ae D (innerCentral_cut_order hX) hh
      contDiff_centralRadius contDiff_centralDensityRoot innerCentral_chart_positive hcore hw
      ((Lp.memLp g).restrict _).aestronglyMeasurable
      (continuous_centralAuxiliaryColumnFunction hh).aestronglyMeasurable
    filter_upwards [innerLiouvilleColumnLift_pullback_ae D (innerCentral_cut_order hX) hh
      contDiff_centralRadius contDiff_centralDensityRoot innerCentral_chart_positive hcore hw
      innerCentralModelBorder, ae_restrict_of_ae (s := Ioo (-X₀) X₀)
        innerCentralModelBorder_ae] with x hx hg
    change innerLiouvilleColumnLift D (innerCentral_cut_order hX) hh
      contDiff_centralRadius contDiff_centralDensityRoot innerCentral_chart_positive hcore hw
      innerCentralModelBorder (centralRadius x) = _
    rw [hx, hg, innerCentralModelBorderFunction_physical hh]
  have hout := innerLiouvilleColumnLift_support_ae D (innerCentral_cut_order hX) hh
    contDiff_centralRadius contDiff_centralDensityRoot innerCentral_chart_positive hcore hw
    innerCentralModelBorder
  filter_upwards [ae_imp_of_ae_restrict hin, hout] with r hi ho
  by_cases hr : r ∈ Ioo (centralRadius (-X₀)) (centralRadius X₀)
  · exact hi hr
  · change innerLiouvilleColumnLift D (innerCentral_cut_order hX) hh
      contDiff_centralRadius contDiff_centralDensityRoot innerCentral_chart_positive hcore hw
      innerCentralModelBorder r = _
    rw [ho hr, innerCentralAuxiliaryColumnFunction_outside hh hX hr]

theorem innerCentralAuxiliaryColumnFunction_memLp_actual :
    MemLp (centralAuxiliaryColumnFunction height) 2 (radialHilbertMeasure D) :=
  (Lp.memLp (innerCentralPhysicalTemporaryColumn D hh hX hcore hw)).congr
    (innerCentralPhysicalTemporaryColumn_ae D hh hX hcore hw)

end ActualMeasure

end ContinuousFlexibility.Radial
