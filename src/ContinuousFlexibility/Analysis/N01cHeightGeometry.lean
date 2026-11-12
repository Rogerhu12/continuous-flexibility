import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
import ContinuousFlexibility.Analysis.MaterialHeightRegularity
import ContinuousFlexibility.Blueprint.Statements
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The genuine spatial inputs of the nonlinear coefficient formula

Only the reference and control conclusions of N01a are used to establish
global smoothness of the profile and its actual integral primitive. The
fundamental theorem of calculus then identifies the first and second
spatial height jets. No abstract height-jet family replaces the integral
in `stateHeight`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Blueprint ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem contDiff_stateProfile_of_partA
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hA : N01PartA D T S C) (x : AnnularState S) :
    ContDiff ℝ ∞ (stateProfile D S C x) :=
  contDiff_stateProfile_of_controlData hS hT hA.1 hA.2.2.1 hA.2.2.2.1 hA.2.2.2.2 x

/-- FTC for the exact primitive based at the outer endpoint. -/
theorem hasDerivAt_stateRadialHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (x : AnnularState S) (r : ℝ) :
    HasDerivAt (stateRadialHeight D S C x) (stateProfile D S C x r) r := by
  have hw := (contDiff_stateProfile_of_partA hS hT hA x).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable D.b r)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt

theorem deriv_stateRadialHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hA : N01PartA D T S C) (x : AnnularState S) :
    deriv (stateRadialHeight D S C x) = stateProfile D S C x :=
  funext fun r => (hasDerivAt_stateRadialHeight hS hT hA x r).deriv

theorem contDiff_stateRadialHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hA : N01PartA D T S C) (x : AnnularState S) :
    ContDiff ℝ ∞ (stateRadialHeight D S C x) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun r => (hasDerivAt_stateRadialHeight hS hT hA x r).differentiableAt, ?_⟩
  rw [deriv_stateRadialHeight hS hT hA]
  exact contDiff_stateProfile_of_partA hS hT hA x

theorem contDiff_stateU
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    ContDiff ℝ ∞ (stateU S x) :=
  physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4) x.1.1 x.1.2

theorem stateHeight_eq_heightFamily (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) :
    stateHeight D S C z =
      heightFamily (radialHeightField (stateRadialHeight D S C z.1)) (stateU S z.1) z.2 := rfl

theorem contDiff_stateHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hA : N01PartA D T S C) (z : AnnularState S × ℝ) :
    ContDiff ℝ ∞ (stateHeight D S C z) := by
  rw [stateHeight_eq_heightFamily]
  exact contDiff_heightFamily
    (contDiff_radialHeightField (contDiff_stateRadialHeight hS hT hA z.1))
    (contDiff_stateU hT hS z.1) z.2

/-- The radial first jet uses the actual profile by FTC. -/
theorem heightRadial_stateHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    heightRadial (stateHeight D S C z) p =
      stateProfile D S C z.1 p.1 + z.2 * heightRadial (stateU S z.1) p := by
  rw [stateHeight_eq_heightFamily,
    heightRadial_heightFamily
      ((contDiff_radialHeightField (contDiff_stateRadialHeight hS hT hA z.1)).differentiable
        (by simp)) ((contDiff_stateU hT hS z.1).differentiable (by simp)),
    heightRadial_radialHeightField (hasDerivAt_stateRadialHeight hS hT hA z.1)]
  rfl

theorem heightAngular_stateHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    heightAngular (stateHeight D S C z) p = z.2 * heightAngular (stateU S z.1) p := by
  rw [stateHeight_eq_heightFamily,
    heightAngular_heightFamily
      ((contDiff_radialHeightField (contDiff_stateRadialHeight hS hT hA z.1)).differentiable
        (by simp)) ((contDiff_stateU hT hS z.1).differentiable (by simp)),
    heightAngular_radialHeightField (hasDerivAt_stateRadialHeight hS hT hA z.1)]
  exact zero_add _

/-- The three second height jets retain the exact normalized polar partials
of the decoded physical height. -/
theorem radialPartial_heightRadial_stateHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    radialPartial (heightRadial (stateHeight D S C z)) p =
      deriv (stateProfile D S C z.1) p.1 +
        z.2 * radialPartial (heightRadial (stateU S z.1)) p := by
  rw [stateHeight_eq_heightFamily,
    radialPartial_heightRadial_heightFamily
      (contDiff_radialHeightField (contDiff_stateRadialHeight hS hT hA z.1))
      (contDiff_stateU hT hS z.1),
    heightRadial_radialHeightField (hasDerivAt_stateRadialHeight hS hT hA z.1),
    radialPartial_radialHeightField
      ((contDiff_stateProfile_of_partA hS hT hA z.1).differentiable (by simp) p.1)]

theorem radialPartial_heightAngular_stateHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hr : p.1 ≠ 0) :
    radialPartial (heightAngular (stateHeight D S C z)) p =
      z.2 * radialPartial (heightAngular (stateU S z.1)) p := by
  rw [stateHeight_eq_heightFamily,
    radialPartial_heightAngular_heightFamily
      (contDiff_radialHeightField (contDiff_stateRadialHeight hS hT hA z.1))
      (contDiff_stateU hT hS z.1) hr,
    heightAngular_radialHeightField (hasDerivAt_stateRadialHeight hS hT hA z.1),
    radialPartial_const, zero_add]

theorem angularPartial_heightAngular_stateHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hr : p.1 ≠ 0) :
    angularPartial (heightAngular (stateHeight D S C z)) p =
      z.2 * angularPartial (heightAngular (stateU S z.1)) p := by
  rw [stateHeight_eq_heightFamily,
    angularPartial_heightAngular_heightFamily
      (contDiff_radialHeightField (contDiff_stateRadialHeight hS hT hA z.1))
      (contDiff_stateU hT hS z.1) hr,
    heightAngular_radialHeightField (hasDerivAt_stateRadialHeight hS hT hA z.1),
    angularPartial_const, zero_add]

end ContinuousFlexibility.Statements
