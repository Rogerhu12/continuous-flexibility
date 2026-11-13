import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
import ContinuousFlexibility.Analysis.PositiveChartRangeGeometry
import ContinuousFlexibility.Analysis.RootUniformCollar

/-!
# Spatial regularity of the actual positive geometry atoms

The global range certificate of the chosen positive chart gives smoothness
and angular periodicity of its eight stored scalar atoms. The physical and
canonical affine unit maps stay distinct. The pulled height is evaluated
at the actual inverse chart, on the same canonical unit map.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
  (z : AnnularState S × ℝ) (m : ℕ)

theorem n04PositiveGeometry_physicalUnitPoint_period (q : PolarPoint) :
    physicalUnitPoint K m (q + (0, Real.pi)) =
      physicalUnitPoint K m q + (0, Real.pi) := by
  ext <;> simp only [physicalUnitPoint, Prod.add_fst, Prod.add_snd, add_zero]

theorem n04PositiveGeometry_canonicalUnitPoint_period (q : PolarPoint) :
    canonicalUnitPoint K m (q + (0, Real.pi)) =
      canonicalUnitPoint K m q + (0, Real.pi) := by
  ext <;> simp only [canonicalUnitPoint, Prod.add_fst, Prod.add_snd, add_zero]

/-- This concerns the literal stored atom, including the absolute
Jacobian and both normalized radial coordinates. -/
theorem n04PositiveGeometry_atom_regular
    (h : PositiveChartRangeGeometry (K.chart z m) (K.inverseChart z m) (K.height z m)
      (K.physicalLeft m) (K.physicalRight m) (K.left m) (K.right m))
    (a : Atom) (ha : atomIsGeometry a) :
    ContDiff ℝ ∞ (atom D T S C L K z m a) ∧
      ∀ q, atom D T S C L K z m a (q + (0, Real.pi)) =
        atom D T S C L K z m a q := by
  have hp : ContDiff ℝ ∞ (physicalUnitPoint K m) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hc : ContDiff ℝ ∞ (canonicalUnitPoint K m) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hJ : ContDiff ℝ ∞ (planeJacobian (K.chart z m)) :=
    contDiff_iff_contDiffAt.mpr (fun _ =>
      ContinuousFlexibility.contDiffAt_planeJacobian h.chart_smooth.contDiffAt)
  have hJa : ContDiff ℝ ∞ (fun q => |planeJacobian (K.chart z m) q|) :=
    hJ.abs (fun q => (h.jacobian_positive q).ne')
  have hFp (q : PolarPoint) :
      K.chart z m (physicalUnitPoint K m (q + (0, Real.pi))) =
        K.chart z m (physicalUnitPoint K m q) + (0, Real.pi) := by
    rw [n04PositiveGeometry_physicalUnitPoint_period]
    exact h.period_add _
  have hGp (q : PolarPoint) :
      K.inverseChart z m (canonicalUnitPoint K m (q + (0, Real.pi))) =
        K.inverseChart z m (canonicalUnitPoint K m q) + (0, Real.pi) := by
    rw [n04PositiveGeometry_canonicalUnitPoint_period]
    exact h.inverse_period_add _
  have hHp (q : PolarPoint) :
      K.height z m (physicalUnitPoint K m (q + (0, Real.pi))) =
        K.height z m (physicalUnitPoint K m q) := by
    rw [n04PositiveGeometry_physicalUnitPoint_period]
    exact h.height_period _
  have hJperiod (q : PolarPoint) :
      planeJacobian (K.chart z m) (q + (0, Real.pi)) =
        planeJacobian (K.chart z m) q := by
    have hshift (r θ : ℝ) : K.chart z m (r, θ + Real.pi) =
        K.chart z m (r, θ) + (0, Real.pi) := by
      simpa only [Prod.mk_add_mk, add_zero] using h.period_add (r, θ)
    simpa only [Prod.mk_add_mk, add_zero] using
      planeJacobian_periodic_snd hshift q.1 q.2
  have hJp (q : PolarPoint) :
      planeJacobian (K.chart z m) (physicalUnitPoint K m (q + (0, Real.pi))) =
        planeJacobian (K.chart z m) (physicalUnitPoint K m q) := by
    rw [n04PositiveGeometry_physicalUnitPoint_period]
    exact hJperiod _
  cases a
  case chartRadial =>
    refine ⟨((h.chart_smooth.fst.comp hp).sub contDiff_const).div_const _, ?_⟩
    intro q
    simp only [atom, hFp, Prod.add_fst, add_zero]
  case chartAngleDefect =>
    refine ⟨(h.chart_smooth.snd.comp hp).sub hp.snd, ?_⟩
    intro q
    simp only [atom, hFp, Prod.add_snd, physicalUnitPoint]
    ring
  case inverseRadial =>
    refine ⟨((h.inverse_smooth.fst.comp hc).sub contDiff_const).div_const _, ?_⟩
    intro q
    simp only [atom, hGp, Prod.add_fst, add_zero]
  case inverseAngleDefect =>
    refine ⟨(h.inverse_smooth.snd.comp hc).sub hc.snd, ?_⟩
    intro q
    simp only [atom, hGp, Prod.add_snd, canonicalUnitPoint]
    ring
  case height =>
    exact ⟨h.height_smooth.comp hp, hHp⟩
  case heightInverse =>
    refine ⟨(h.height_smooth.inv (fun q => (h.height_positive q).ne')).comp hp, ?_⟩
    intro q
    exact congrArg Inv.inv (hHp q)
  case jacobian =>
    refine ⟨hJa.comp hp, ?_⟩
    intro q
    exact congrArg abs (hJp q)
  case jacobianInverse =>
    refine ⟨(hJa.inv (fun q => abs_ne_zero.mpr (h.jacobian_positive q).ne')).comp hp, ?_⟩
    intro q
    exact congrArg (fun t : ℝ => |t|⁻¹) (hJp q)
  all_goals exact False.elim ha

/-- The actual height at the actual inverse point is also globally
smooth and periodic; no reference representative is substituted. -/
theorem n04PositiveGeometry_pulledHeight_regular
    (h : PositiveChartRangeGeometry (K.chart z m) (K.inverseChart z m) (K.height z m)
      (K.physicalLeft m) (K.physicalRight m) (K.left m) (K.right m)) :
    ContDiff ℝ ∞ (fun q => K.height z m (K.inverseChart z m (canonicalUnitPoint K m q))) ∧
      ∀ q, K.height z m (K.inverseChart z m (canonicalUnitPoint K m (q + (0, Real.pi)))) =
        K.height z m (K.inverseChart z m (canonicalUnitPoint K m q)) := by
  have hc : ContDiff ℝ ∞ (canonicalUnitPoint K m) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  refine ⟨h.height_smooth.comp (h.inverse_smooth.comp hc), ?_⟩
  intro q
  rw [n04PositiveGeometry_canonicalUnitPoint_period, h.inverse_period_add, h.height_period]

end ContinuousFlexibility.Analysis
