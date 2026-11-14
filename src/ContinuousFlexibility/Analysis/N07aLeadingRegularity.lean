module

public import ContinuousFlexibility.Analysis.N07aLeadingCoefficient
public import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Spatial regularity of the actual leading coefficient

Only interior smoothness of the decoded height is needed here. The actual
controlled radial profile is already globally smooth from N01, and its
primitive supplies the radial part of the nonlinear height.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

theorem n07a_stateRadialHeight_contDiff
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (x : AnnularState S) :
    ContDiff ℝ ∞ (stateRadialHeight D S C x) := by
  have hw := contDiff_stateProfile_of_n01 hS hT h01 x
  have hd (r : ℝ) : HasDerivAt (stateRadialHeight D S C x)
      (stateProfile D S C x r) r :=
    intervalIntegral.integral_hasDerivAt_right (hw.continuous.intervalIntegrable D.b r)
      hw.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuous.continuousAt
  have he : deriv (stateRadialHeight D S C x) = stateProfile D S C x :=
    funext fun r => (hd r).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun r => (hd r).differentiableAt, ?_⟩
  rwa [he]

theorem n07a_stateHeight_contDiffOn
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ) :
    ContDiffOn ℝ ∞ (stateHeight D S C z) (annularOpen D) := by
  have hdecode := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 z.1.1.1).1
  have hchi : ContDiff ℝ ∞ (fun p : PolarPoint => S.chiLeft p.1) :=
    hS.2.2.1.1.comp contDiff_fst
  have hU : ContDiffOn ℝ ∞ (stateU S z.1) (annularOpen D) :=
    hdecode.add (contDiffOn_const.mul hchi.contDiffOn)
  exact ((n07a_stateRadialHeight_contDiff hS hT h01 z.1).comp contDiff_fst).contDiffOn.add
    (contDiffOn_const.mul hU)

theorem n07a_originalLeadingCoefficient_contDiffOn
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    ContDiffOn ℝ ∞ (originalCoefficients D S C z).a (annularOpen D) := by
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hw := contDiff_stateProfile_of_n01 hS hT h01 z.1
  have hh := n07a_stateHeight_contDiffOn hS hT h01 z
  have hgeom := h01.1.1.choose_spec.1
  intro p hp
  have hpoint := h01.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  have hwp : 0 < stateProfile D S C z.1 p.1 := by
    dsimp only [stateProfile]
    exact mul_pos (hgeom.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
  have hQlower := (le_div_iff₀ hwp).mp hpoint.2.2.1
  have hQpos : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) := by
    linarith only [hwp, hQlower]
  have hΔpos : 0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hpoint.2.2.2.2.1
  exact (contDiffAt_heightLinearCoefficients hw.contDiffAt
    (hh.contDiffAt (hopen.mem_nhds hp))
    (hgeom.1.trans hp.1.1).ne' hΔpos hQpos.ne').1.contDiffWithinAt

theorem n07a_correctedLeadingCoefficient_contDiffOn
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    ContDiffOn ℝ ∞ (L.coefficients z).a (annularOpen D) := by
  have he : (L.coefficients z).a = (originalCoefficients D S C z).a :=
    funext (h03.1 z hz hs)
  rw [he]
  exact n07a_originalLeadingCoefficient_contDiffOn hS hT h01 hz hs

theorem n07a_correctedLeadingCoefficient_inverse_contDiffOn
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    ContDiffOn ℝ ∞ (fun p => ((L.coefficients z).a p)⁻¹) (annularOpen D) :=
  (n07a_correctedLeadingCoefficient_contDiffOn hS hT h01 h03 hz hs).inv
    (fun _ hp => (n07a_correctedLeadingCoefficient_pos h01 h03 hz hs hp).ne')

end ContinuousFlexibility.Analysis
