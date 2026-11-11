import ContinuousFlexibility.Analysis.N05CanonicalPhysicalChange
import ContinuousFlexibility.Analysis.N05CanonicalPhysicalRepresentatives

/-!
# The actual canonical height transform of a physical field

The inverse chart transfers the measurable representative class. The genuine
Jacobian formula then identifies the square integral of the height transform
with its physical density, before any weighted estimate is applied.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory

/-- The inverse of the genuine chart preserves the physical measurable
class on its canonical rectangle. -/
theorem n05_inverseChart_aestronglyMeasurable_comp
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K m, (K.chart z m p).2 = p.2)
    {f : PolarPoint → ℝ} (hf : AEStronglyMeasurable f (radialPhysicalMeasure D)) :
    AEStronglyMeasurable (fun p => f (K.inverseChart z m p))
      (canonicalMeasure S K m) := by
  have hpull := n05_inverseChart_ae_eq_of_physical h04 hz hs m hangle hf.ae_eq_mk
  rcases h04 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  have hc := (hcharts z hz hs m).2.2.2.2.2.1.continuousOn
  have hmap : AEMeasurable (K.inverseChart z m) (canonicalMeasure S K m) :=
    (hc.mono (fun _ hp => ⟨hp.1, mem_univ _⟩)).aemeasurable
      (measurableSet_Ioo.prod measurableSet_Ioc)
  exact (hf.measurable_mk.comp_aemeasurable hmap).aestronglyMeasurable.congr hpull.symm

theorem n05_canonicalHeight_aestronglyMeasurable
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K m, (K.chart z m p).2 = p.2)
    {f : PolarPoint → ℝ} (hf : AEStronglyMeasurable f (radialPhysicalMeasure D)) :
    AEStronglyMeasurable (canonicalHeight S K z m f) (canonicalMeasure S K m) := by
  have hcomp := n05_inverseChart_aestronglyMeasurable_comp h04 hz hs m hangle hf
  rcases h04 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  obtain ⟨_, hmap, _, _, _, hΨ, hheight, _⟩ := hcharts z hz hs m
  have hden : ContinuousOn (fun p => K.height z m (K.inverseChart z m p))
      (canonicalOpen S K m) :=
    hheight.continuousOn.comp hΨ.continuousOn hmap
  exact hcomp.div₀
    ((hden.mono (fun _ hp => ⟨hp.1, mem_univ _⟩)).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioc))

/-- Evaluating the height transform at the actual chart recovers the
physical height divided by its actual normalization factor. -/
theorem n05_canonicalHeight_chart_ae
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (f : PolarPoint → ℝ) :
    (fun p => canonicalHeight S K z m f (K.chart z m p)) =ᵐ[
      volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ
        Ioc (0 : ℝ) Real.pi)] (fun p => f p / K.height z m p) := by
  rcases h04 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  have hleft := (hcharts z hz hs m).2.2.1
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  simp only [canonicalHeight, hleft p ⟨hp.1, mem_univ _⟩]

theorem n05_canonicalHeight_sq_integrable_iff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K m, (K.chart z m p).2 = p.2)
    (f : PolarPoint → ℝ) :
    Integrable (fun p => canonicalHeight S K z m f p ^ 2) (canonicalMeasure S K m) ↔
      Integrable (fun p => |planeJacobian (K.chart z m) p| * (f p / K.height z m p) ^ 2)
        (volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ
          Ioc (0 : ℝ) Real.pi)) := by
  refine (n05_canonicalChart_integrable_iff h04 hz hs m hangle _).trans ?_
  apply integrable_congr
  filter_upwards [n05_canonicalHeight_chart_ae h04 hz hs m f] with p hp
  exact congrArg (fun x : ℝ => |planeJacobian (K.chart z m) p| * x ^ 2) hp

theorem n05_canonicalHeight_sq_integral
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K m, (K.chart z m p).2 = p.2)
    (f : PolarPoint → ℝ) :
    (∫ p, canonicalHeight S K z m f p ^ 2 ∂canonicalMeasure S K m) =
      ∫ p, |planeJacobian (K.chart z m) p| * (f p / K.height z m p) ^ 2
        ∂volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ
          Ioc (0 : ℝ) Real.pi) := by
  refine (n05_canonicalChart_integral h04 hz hs m hangle _).trans ?_
  apply integral_congr_ae
  filter_upwards [n05_canonicalHeight_chart_ae h04 hz hs m f] with p hp
  exact congrArg (fun x : ℝ => |planeJacobian (K.chart z m) p| * x ^ 2) hp

end ContinuousFlexibility.Statements
