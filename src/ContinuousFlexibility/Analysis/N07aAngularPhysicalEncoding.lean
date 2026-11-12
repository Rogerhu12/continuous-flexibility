import ContinuousFlexibility.Analysis.N07aAngularPhysicalMeasure
import ContinuousFlexibility.Analysis.N07aAngularInnerIntervals

/-!
# Returning the same physical representative to its canonical classes

The actual chart Jacobian pushes physical measure to canonical measure.
Composing the true interior inverse with that map gives the reverse
weighted-measure identity. Thus physical a.e. equalities push back to
canonical a.e. equalities, without any measurability or endpoint meaning
being imposed on the inverse-coordinate candidate outside its open strip.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_inverseChart_aemeasurable
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    AEMeasurable (K.inverseChart z m) (canonicalMeasure S K m) := by
  have hg := (h04.1.charts z hz hs m).2.2.2.2.2.1
  exact (hg.continuousOn.mono (fun p hp => ⟨hp.1, mem_univ _⟩)).aemeasurable
    (measurableSet_Ioo.prod measurableSet_Ioc)

theorem n07a_inverseChart_map
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    Measure.map (K.inverseChart z m) (canonicalMeasure S K m) =
      (n07aPhysicalMeasure S K z m).withDensity
        (n07aChartDensity K z m) := by
  let μ := (n07aPhysicalMeasure S K z m).withDensity
    (n07aChartDensity K z m)
  have hc : AEMeasurable (K.chart z m) μ :=
    (n07a_chart_aemeasurable h04 hz hs m).mono_ac
      (withDensity_absolutelyContinuous _ (n07aChartDensity K z m))
  have hi : AEMeasurable (K.inverseChart z m) (Measure.map (K.chart z m) μ) := by
    rw [n07a_chart_map_withDensity h04 hz hs m]
    exact n07a_inverseChart_aemeasurable h04 hz hs m
  have he : (K.inverseChart z m ∘ K.chart z m) =ᵐ[μ] id := by
    have hmem := n07aPhysicalMeasure_ae h04 hz hs m
    have hw := hmem.filter_mono (withDensity_absolutelyContinuous _
      (n07aChartDensity K z m)).ae_le
    filter_upwards [hw] with p hp
    exact (h04.1.charts z hz hs m).2.2.1 p hp

  calc
    _ = Measure.map (K.inverseChart z m) (Measure.map (K.chart z m) μ) := by
      rw [n07a_chart_map_withDensity h04 hz hs m]
    _ = Measure.map (K.inverseChart z m ∘ K.chart z m) μ := hi.map_map_of_aemeasurable hc
    _ = μ := (Measure.map_congr he).trans Measure.map_id

theorem n07a_inverseChart_ae_pullback {E : Type*}
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f g : PolarPoint → E}
    (he : f =ᵐ[n07aPhysicalMeasure S K z m] g) :
    (fun p => f (K.inverseChart z m p)) =ᵐ[canonicalMeasure S K m]
      fun p => g (K.inverseChart z m p) := by
  have hw := he.filter_mono (withDensity_absolutelyContinuous _
    (n07aChartDensity K z m)).ae_le
  rw [← n07a_inverseChart_map h04 hz hs m] at hw
  exact ae_of_ae_map (n07a_inverseChart_aemeasurable h04 hz hs m) hw

theorem n07a_canonicalHeight_congr_physical_ae
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f g : PolarPoint → ℝ}
    (he : f =ᵐ[n07aPhysicalMeasure S K z m] g) :
    canonicalHeight S K z m f =ᵐ[canonicalMeasure S K m] canonicalHeight S K z m g := by
  filter_upwards [n07a_inverseChart_ae_pullback h04 hz hs m he] with p hp
  exact congrArg (· / K.height z m (K.inverseChart z m p)) hp

/-- The globally reconstructed physical field keeps every original
canonical unknown coordinate, including the explicit left scalar. -/
theorem n07a_canonicalRepresentation_replace_height
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {η v f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    (he : v =ᵐ[canonicalMeasure S (n07aRadialIntervalData K D.a D.b) 0] η) :
    HasCanonicalRepresentation D S C K z U F v f := by
  refine ⟨?_, hrep.2⟩
  intro m
  have he' := he.filter_mono (ae_mono (n07aPhysicalMeasure_le_annulus h04 hz hs m))
  have hrem : (fun p => v p - U.2.1 * S.chiLeft p.1) =ᵐ[
      n07aPhysicalMeasure S K z m]
      fun p => η p - U.2.1 * S.chiLeft p.1 :=
    he'.mono fun p hp => congrArg (· - U.2.1 * S.chiLeft p.1) hp
  exact (hrep.1 m).trans (n07a_canonicalHeight_congr_physical_ae h04 hz hs m hrem).symm

end ContinuousFlexibility.Analysis
