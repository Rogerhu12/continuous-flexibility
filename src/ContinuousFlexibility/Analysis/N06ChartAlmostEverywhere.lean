import ContinuousFlexibility.Analysis.N06PhysicalReconstruction
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Transport of null exceptional sets by the actual canonical charts

The inverse chart is smooth on its open domain. Its image of a Lebesgue
null set is therefore null, which transfers almost-everywhere statements
without assuming a representative is pointwise equal. This is used before
passing canonical L² identities into physical distributional pairings.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A smooth left inverse transports null exceptional sets. Only the
actual inverse identities and differentiability are required. -/
theorem n06_ae_comp_of_smooth_leftInverse
    {F G : PolarPoint → PolarPoint} {U W : Set PolarPoint}
    (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hG : DifferentiableOn ℝ G W) (hF : MapsTo F U W)
    (hleft : ∀ x ∈ U, G (F x) = x)
    {P : PolarPoint → Prop} (hP : ∀ᵐ y ∂volume.restrict W, P y) :
    ∀ᵐ x ∂volume.restrict U, P (F x) := by
  classical
  let E : Set PolarPoint := {y | y ∈ W ∧ ¬P y}
  have hE : volume E = 0 := by
    have hh := (ae_iff.mp ((ae_restrict_iff' hW).mp hP))
    exact measure_mono_null (fun y hy => fun h => hy.2 (h hy.1)) hh
  have hGE : volume (G '' E) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hG.mono (fun _ hy => hy.1)) hE
  apply (ae_restrict_iff' hU).mpr
  have havoid : ∀ᵐ x ∂volume, x ∉ G '' E := by
    apply ae_iff.mpr
    exact measure_mono_null (fun _ hx => Classical.not_not.mp hx) hGE
  filter_upwards [havoid] with x hx hxU
  by_contra hbad
  exact hx ⟨F x, ⟨hF hxU, hbad⟩, hleft x hxU⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- Almost-everywhere predicates on the whole canonical strip pull back
through the actual state-dependent chart. -/
theorem n06_canonical_ae_pullback
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {P : PolarPoint → Prop}
    (hP : ∀ᵐ y ∂volume.restrict (canonicalOpen S K m), P y) :
    ∀ᵐ x ∂volume.restrict (physicalPieceOpen S K z m), P (K.chart z m x) := by
  have hcharts := hN04.1.charts
  obtain ⟨hmap, _, hleft, _, _, hinverse, _, _⟩ := hcharts z hz hs m
  exact n06_ae_comp_of_smooth_leftInverse
    (hN04.1.domains z hz hs m).1.measurableSet
    (measurableSet_Ioo.prod MeasurableSet.univ)
    (hinverse.differentiableOn (by simp)) hmap hleft hP

/-- The physical-to-canonical direction uses the smooth chart itself as
the inverse of the inverse chart, so it has the same null-set justification. -/
theorem n06_physical_ae_pushforward
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {P : PolarPoint → Prop}
    (hP : ∀ᵐ x ∂volume.restrict (physicalPieceOpen S K z m), P x) :
    ∀ᵐ y ∂volume.restrict (canonicalOpen S K m), P (K.inverseChart z m y) := by
  have hcharts := hN04.1.charts
  obtain ⟨_, hmap, _, hright, hchart, _, _, _⟩ := hcharts z hz hs m
  exact n06_ae_comp_of_smooth_leftInverse
    (measurableSet_Ioo.prod MeasurableSet.univ)
    (hN04.1.domains z hz hs m).1.measurableSet
    (hchart.differentiableOn (by simp)) hmap hright hP

end ContinuousFlexibility.Statements
