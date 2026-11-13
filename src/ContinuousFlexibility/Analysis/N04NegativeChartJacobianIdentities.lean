import ContinuousFlexibility.Analysis.N04SourceColumnsIdentities
import ContinuousFlexibility.Analysis.N04NegativeChartData

/-!
# The forward determinant in the two actual coordinate atoms

The normalized radial coordinate and angle defect reconstruct the stored
chart. The physical unit map contributes its physical width, so the
forward determinant has the canonical/physical width ratio. All identities
refer to the actual chart at the fixed physical unit point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

theorem n04NegativeChart_chart_unit_eq (z : AnnularState S × ℝ) (m : ℕ)
    (hwidth : K.right m - K.left m ≠ 0) :
    (fun p => K.chart z m (physicalUnitPoint K m p)) =
      (fun p => (K.left m + (K.right m - K.left m) *
        atom D T S C L K z m .chartRadial p,
        p.2 + atom D T S C L K z m .chartAngleDefect p)) := by
  funext p
  apply Prod.ext
  · change (K.chart z m (physicalUnitPoint K m p)).1 =
      K.left m + (K.right m - K.left m) *
        (((K.chart z m (physicalUnitPoint K m p)).1 - K.left m) /
          (K.right m - K.left m))
    field_simp [hwidth]
    <;> ring
  · change (K.chart z m (physicalUnitPoint K m p)).2 =
      p.2 + ((K.chart z m (physicalUnitPoint K m p)).2 - p.2)
    ring

theorem n04NegativeChart_physicalUnitPoint_jacobian (m : ℕ) (p : PolarPoint) :
    planeJacobian (physicalUnitPoint K m) p = K.physicalRight m - K.physicalLeft m := by
  have hr : HasFDerivAt
      (fun q : PolarPoint => K.physicalLeft m +
        (K.physicalRight m - K.physicalLeft m) * q.1)
      ((K.physicalRight m - K.physicalLeft m) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    (hasFDerivAt_fst.const_mul (K.physicalRight m - K.physicalLeft m)).const_add
      (K.physicalLeft m)
  have ha : HasFDerivAt (fun q : PolarPoint => q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  change planeJacobian (fun q : PolarPoint =>
    (K.physicalLeft m + (K.physicalRight m - K.physicalLeft m) * q.1, q.2)) p = _
  simp only [planeJacobian, (hr.prodMk ha).fderiv, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- First derivatives of the actual two forward atoms give the physical
chart determinant with precisely its stored width normalization. -/
theorem n04NegativeChart_jacobian_unit_mixed
    (z : AnnularState S × ℝ) (m : ℕ)
    (hphysical : K.physicalRight m - K.physicalLeft m ≠ 0)
    (hcanonical : K.right m - K.left m ≠ 0)
    (hradial : ContDiffOn ℝ ∞ (atom D T S C L K z m .chartRadial) unitStrip)
    (hangle : ContDiffOn ℝ ∞ (atom D T S C L K z m .chartAngleDefect) unitStrip)
    {p : PolarPoint} (hp : p ∈ unitStrip)
    (hchart : DifferentiableAt ℝ (K.chart z m) (physicalUnitPoint K m p)) :
    planeJacobian (K.chart z m) (physicalUnitPoint K m p) =
      ((K.right m - K.left m) / (K.physicalRight m - K.physicalLeft m)) *
        (mixedDerivative 1 0 (atom D T S C L K z m .chartRadial) p *
            (1 + mixedDerivative 0 1 (atom D T S C L K z m .chartAngleDefect) p) -
          mixedDerivative 1 0 (atom D T S C L K z m .chartAngleDefect) p *
            mixedDerivative 0 1 (atom D T S C L K z m .chartRadial) p) := by
  have hu : DifferentiableAt ℝ (physicalUnitPoint K m) p :=
    ((differentiableAt_const (K.physicalLeft m)).add
      ((differentiableAt_const (K.physicalRight m - K.physicalLeft m)).mul
        differentiableAt_fst)).prodMk differentiableAt_snd
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hr := (hradial.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have ha := (hangle.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hcomp := planeJacobian_comp hu hchart
  rw [n04NegativeChart_physicalUnitPoint_jacobian] at hcomp
  have hpair := n04SourceColumns_planeJacobian_coordinatePair hr ha
    (K.left m) (K.right m - K.left m)
  have heq := n04NegativeChart_chart_unit_eq (D := D) (T := T) (C := C) (L := L)
    z m hcanonical
  have hscaled := hcomp.symm.trans
    ((congrArg (fun F => planeJacobian F p) heq).trans hpair)
  have hraw := (eq_div_iff hphysical).mpr hscaled
  rw [radialPartial_eq_mixedDerivative_on hU hradial hp,
    angularPartial_eq_mixedDerivative_on hU hangle hp,
    radialPartial_eq_mixedDerivative_on hU hangle hp,
    angularPartial_eq_mixedDerivative_on hU hradial hp] at hraw
  exact hraw.trans (by ring)

/-- The first-jet polynomial shared by current and reference formulas. -/
def n04NegativeChartDeterminant (c : ℕ → ℝ) (R A : ℕ → PolarPoint → ℝ) :
    ℕ → PolarPoint → ℝ := fun m q => c m *
  (mixedDerivative 1 0 (R m) q * (1 + mixedDerivative 0 1 (A m) q) -
    mixedDerivative 1 0 (A m) q * mixedDerivative 0 1 (R m) q)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_jacobian_unit_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_jacobian_unit_mixed
