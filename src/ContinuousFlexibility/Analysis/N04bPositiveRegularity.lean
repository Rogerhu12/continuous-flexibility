import ContinuousFlexibility.Analysis.N04bCanonicalOperator
import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
import ContinuousFlexibility.Analysis.MaterialHeightRegularity
import ContinuousFlexibility.Scalar.TypeCorrection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual coefficient regularity on positive canonical pieces

The nonlinear profile and height are genuinely smooth functions. The
quantitative geometric inequalities in N01 keep the discriminant and Q
away from zero. N03 identifies the corrected coefficients with their
original germs on the nonnegative region. Thus the positive-piece
canonical operator identity needs no additional regularity assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n04b_contDiff_stateRadialHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) :
    ContDiff ℝ ∞ (stateRadialHeight D S C x) := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN x
  have hd (r : ℝ) : HasDerivAt (stateRadialHeight D S C x)
      (stateProfile D S C x r) r :=
    intervalIntegral.integral_hasDerivAt_right (hw.continuous.intervalIntegrable D.b r)
      hw.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hw.continuous.continuousAt
  have he : deriv (stateRadialHeight D S C x) = stateProfile D S C x :=
    funext fun r => (hd r).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun r => (hd r).differentiableAt, ?_⟩
  rw [he]
  exact hw

theorem n04b_contDiff_stateHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ) :
    ContDiff ℝ ∞ (stateHeight D S C z) := by
  have hu : ContDiff ℝ ∞ (stateU S z.1) :=
    physical_height_with_cutoff_contDiff hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) z.1.1.1 z.1.1.2
  exact ((n04b_contDiff_stateRadialHeight hT hS hN z.1).comp contDiff_fst).add
    (contDiff_const.mul hu)

theorem n04b_originalCoefficients_contDiffAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (originalCoefficients D S C z).a p ∧
      ContDiffAt ℝ ∞ (originalCoefficients D S C z).b p ∧
      ContDiffAt ℝ ∞ (originalCoefficients D S C z).c p := by
  obtain ⟨B, hBounds⟩ := hN.1.1
  have hGeom : RadialProfileGeometry D := hBounds.1
  have hr : p.1 ≠ 0 := ne_of_gt (hGeom.1.trans hp.1.1)
  have hw0 : 0 < stateProfile D S C z.1 p.1 :=
    mul_pos (hGeom.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
  have hgeo := hN.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  have hQ0 : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) := by
    have hq := (le_div_iff₀ hw0).mp hgeo.2.2.1
    nlinarith
  have hD0 : 0 < polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) p := by
    linarith [hgeo.2.2.2.2.1]
  have h := contDiffAt_heightLinearCoefficients
    (contDiff_stateProfile_of_n01 hS hT hN z.1).contDiffAt
    (n04b_contDiff_stateHeight hT hS hN z).contDiffAt hr hD0 hQ0.ne'
  exact ⟨h.1, h.2.1, h.2.2.2.1⟩

/-- On the nonnegative region, N03 supplies actual equal germs. -/
theorem n04b_returnCoefficients_nonnegative_contDiffAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hsign : 0 ≤ deriv D.w p.1) :
    ContDiffAt ℝ ∞ (L.coefficients z).a p ∧
      ContDiffAt ℝ ∞ (L.coefficients z).b p ∧
      ContDiffAt ℝ ∞ (L.coefficients z).c p := by
  have hOrig := n04b_originalCoefficients_contDiffAt hT hS hN.1.1 hz hs hp
  have ha : (L.coefficients z).a = (originalCoefficients D S C z).a :=
    funext fun q => hN.2.1 z hz hs q
  have hmatch : (L.coefficients z).b =ᶠ[𝓝 p] (originalCoefficients D S C z).b ∧
      (L.coefficients z).c =ᶠ[𝓝 p] (originalCoefficients D S C z).c := by
    rcases lt_or_eq_of_le hsign with hpos | heq
    · exact hN.2.2.1 z hz hs p hp hpos
    · exact hN.2.2.2.1 z hz hs p hp heq.symm
  refine ⟨?_, hOrig.2.1.congr_of_eventuallyEq hmatch.1,
    hOrig.2.2.congr_of_eventuallyEq hmatch.2⟩
  rw [ha]
  exact hOrig.1

/-- The complete positive-piece operator identity follows from the original
cumulative hypotheses and PartA, with the explicit canonical fields. -/
theorem n04bCanonicalOperatorData_positive_operator
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = true)
    (W : PolarPoint → ℝ) (hW : ContDiff ℝ ∞ W)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalOperator S (n04bCanonicalOperatorData S L K) L z m W p =
      (if K.positive m then -1 else (1 : ℝ)) *
        divergenceOperator ((n04bCanonicalOperatorData S L K).coefficients z m) W p +
      (n04bCanonicalOperatorData S L K).potential z m p * W p := by
  have hcharts := hA.charts z hz hs m
  have hx : K.inverseChart z m p ∈ physicalPieceOpen S K z m := hcharts.2.1 hp
  have hAnn : K.inverseChart z m p ∈ annularOpen D :=
    (hA.domains z hz hs m).2.2.1 hx
  have hpos : 0 < deriv D.w (K.inverseChart z m p).1 :=
    (hA.domains z hz hs m).2.2.2.2.2.2.1 _ hx hm
  obtain ⟨ha, hb, hc⟩ :=
    n04b_returnCoefficients_nonnegative_contDiffAt hT hS hN hz hs hAnn hpos.le
  exact n04bCanonicalOperatorData_operator hA hz hs m hp ha hb hc W hW

end ContinuousFlexibility.Analysis
