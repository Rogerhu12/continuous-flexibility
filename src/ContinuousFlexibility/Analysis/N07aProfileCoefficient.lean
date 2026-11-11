import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The actual radial profile as a coefficient slice

At zero amplitude the nonlinear height is the actual primitive of the
controlled profile. Its leading coefficient is therefore exactly that
profile. This identifies profile variation with an existing N01 coefficient
family, including its genuine parameter derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n07a_stateRadialHeight_hasDerivAt
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (x : AnnularState S) (r : ℝ) :
    HasDerivAt (stateRadialHeight D S C x) (stateProfile D S C x r) r := by
  have hw := contDiff_stateProfile_of_n01 hS hT h01 x
  exact intervalIntegral.integral_hasDerivAt_right
    (hw.continuous.intervalIntegrable D.b r)
    hw.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    hw.continuous.continuousAt

theorem n07a_stateHeight_zero (x : AnnularState S) :
    stateHeight D S C (x, 0) =
      Radial.radialHeightField (stateRadialHeight D S C x) := by
  funext p
  simp only [stateHeight, zero_mul, add_zero, Radial.radialHeightField]

theorem n07a_originalLeadingCoefficient_zero
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (x : AnnularState S) (p : PolarPoint) :
    (originalCoefficients D S C (x, 0)).a p = stateProfile D S C x p.1 := by
  have hd := n07a_stateRadialHeight_hasDerivAt hS hT h01 x
  change polarLinearA (stateProfile D S C x) (stateHeight D S C (x, 0)) p = _
  rw [n07a_stateHeight_zero]
  unfold polarLinearA polarScale
  rw [Radial.heightRadial_radialHeightField hd,
    Radial.heightAngular_radialHeightField hd,
    Radial.polarDiscriminant_radialHeightField hd]
  simp only [linearRadial, heightQ, angularPartial_const, mul_zero, add_zero,
    inverseDThreeHalves_one, mul_one, Radial.radialHeightField]

theorem n07a_originalMixedCoefficient_zero
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (x : AnnularState S) (p : PolarPoint) :
    (originalCoefficients D S C (x, 0)).b p = 0 := by
  have hd := n07a_stateRadialHeight_hasDerivAt hS hT h01 x
  change polarLinearB (stateProfile D S C x) (stateHeight D S C (x, 0)) p = _
  rw [n07a_stateHeight_zero]
  unfold polarLinearB
  rw [Radial.heightAngular_radialHeightField hd, radialPartial_const]
  simp only [linearMixed, mul_zero, zero_mul, neg_zero]

/-- Equality of the actual spatial jet functions; no interchange of
parameter and spatial differentiation is assumed. -/
theorem n07a_coefficientFamily_profile_slice
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (a b : ℕ) (p : PolarPoint) (x : AnnularState S) :
    coefficientFamily D S C 0 a b p (x, 0) =
      mixedDerivative a b (fun q : PolarPoint =>
        stateProfile D S C x q.1 - stateProfile D S C C.referenceState q.1) p := by
  simp only [coefficientFamily, ite_true, n07a_originalLeadingCoefficient_zero hS hT h01]

end ContinuousFlexibility.Analysis
