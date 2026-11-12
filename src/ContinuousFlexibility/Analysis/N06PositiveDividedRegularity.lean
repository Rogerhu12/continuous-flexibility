import ContinuousFlexibility.Analysis.N06PositiveCanonicalRegularity
import ContinuousFlexibility.Analysis.N06Neighborhood
import ContinuousFlexibility.Analysis.N05ReferenceResidual

/-!
# Positive coefficient regularity on the same complete N05 witness

The one smaller neighbourhood preserves every cumulative property, the
same graph and inverse, and the same canonical spaces. The actual cubic
quotient then gives smooth divided coefficients. No state regularity or
quantitative smallness of those quotients is asserted here.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The complete original N05 witness is retained while all positive
principal and divided coefficient fields acquire their proved regularity. -/
theorem n06_exists_positive_regular_through05
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hthrough : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base ε', stateSector S z.1 →
        ∀ m, K.positive m = true →
          (ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
            ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
            ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m)) ∧
          (ContDiffOn ℝ ∞ (K.dividedDifference z m).a (canonicalOpen S K m) ∧
            ContDiffOn ℝ ∞ (K.dividedDifference z m).b (canonicalOpen S K m) ∧
            ContDiffOn ℝ ∞ (K.dividedDifference z m).c (canonicalOpen S K m)) := by
  have h01 := hthrough.1.1.1.1
  have h03 := hthrough.1.1.2
  have h04 := hthrough.1.2.2.2.2
  obtain ⟨ε', hε', hle, hreg⟩ :=
    n06_exists_positive_canonical_regular_neighborhood hT hS h01 h03 h04
  refine ⟨ε', hε', hle, n06_NonlinearPropertiesThrough05_mono hT hthrough
    le_rfl hε' hle, ?_⟩
  intro z hz hs m hm
  have hzold : z ∈ stateNeighborhood S C base ε :=
    ⟨hz.1.trans_le hle, hz.2.trans_le hle⟩
  have hcur := hreg z hz hs m hm
  have href := hreg (C.referenceState, 0) (n05_referenceState_mem hε')
    (n05_referenceState_sector h01.2.2.1) m hm
  exact ⟨hcur, contDiffOn_canonicalDividedDifference
    (n06_N04_qualitative_parts h04).2 hzold hs m hm
    hcur.1 hcur.2.1 hcur.2.2 href.1 href.2.1 href.2.2⟩

/-- The positive interior density interface is expressed at an actual
physical point, for use with the closed forward boundary calculation. -/
theorem n06_positive_physical_density_of_regular_coefficients
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = true)
    (hreg : ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m) :
    (K.coefficients z m).a (K.chart z m x) =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).a x ∧
      (K.coefficients z m).b (K.chart z m x) =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).b x ∧
      (K.coefficients z m).c (K.chart z m x) =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).c x := by
  have hparts := n06_N04_qualitative_parts h04
  have hcharts := hparts.1.charts z hz hs m
  have hp := hcharts.1 hx
  have hi := hcharts.2.2.1 x hx
  have hpa : x ∈ annularOpen D := (h04.1.domains z hz hs m).2.2.1 hx
  have hphys := n06_correctedCoefficients_contDiffAt_of_nonneg hT hS h01 h03 hz hs hpa
    ((h04.1.domains z hz hs m).2.2.2.2.2.2.1 x hx hm).le
  have hregAt := fun {f : PolarPoint → ℝ}
      (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m)) =>
    (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have ha : DifferentiableAt ℝ (L.coefficients z).a (K.inverseChart z m (K.chart z m x)) := by
    simpa only [hi] using hphys.1.differentiableAt (by simp)
  have hb : DifferentiableAt ℝ (L.coefficients z).b (K.inverseChart z m (K.chart z m x)) := by
    simpa only [hi] using hphys.2.1.differentiableAt (by simp)
  have hc : DifferentiableAt ℝ (L.coefficients z).c (K.inverseChart z m (K.chart z m x)) := by
    simpa only [hi] using hphys.2.2.differentiableAt (by simp)
  have hid := canonicalPrincipalCoefficients_eq_density hparts.1 hparts.2 hz hs m hp
    ha hb hc (hregAt hreg.1) (hregAt hreg.2.1) (hregAt hreg.2.2)
  simpa only [hi] using hid

end ContinuousFlexibility.Statements
