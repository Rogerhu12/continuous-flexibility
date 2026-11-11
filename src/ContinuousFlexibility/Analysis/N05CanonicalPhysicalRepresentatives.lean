import ContinuousFlexibility.Analysis.N05CanonicalPhysicalAE

/-!
# Physical representatives determine both canonical transforms

The physical measure controls every half-period piece. The actual inverse
chart transfers that equality to the canonical rectangle, where the frozen
height and source formulas preserve it. No pointwise or smooth representative
is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory

/-- The genuine N04 pieces lie in the radial physical measure. -/
theorem n05_physical_ae_on_canonicalPiece
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {f g : PolarPoint → ℝ} (hfg : f =ᵐ[radialPhysicalMeasure D] g) (m : ℕ) :
    f =ᵐ[volume.restrict
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)] g := by
  rcases h04 with ⟨_, _, _, hpieces, _⟩
  have hp := ae_imp_of_ae_restrict hfg
  apply (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioc)).mpr
  filter_upwards [hp] with p hp
  intro hpm
  apply hp
  refine ⟨(hpieces m).2.2 hpm.1, hpm.2.1, ?_⟩
  exact hpm.2.2.trans (by linarith [Real.pi_pos])

/-- Equality for the real physical measure survives composition with the
actual inverse chart, with no change-of-measure premise. -/
theorem n05_inverseChart_ae_eq_of_physical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K m, (K.chart z m p).2 = p.2)
    {f g : PolarPoint → ℝ} (hfg : f =ᵐ[radialPhysicalMeasure D] g) :
    (fun p => f (K.inverseChart z m p)) =ᵐ[canonicalMeasure S K m]
      (fun p => g (K.inverseChart z m p)) := by
  have hpiece := n05_physical_ae_on_canonicalPiece h04 hfg m
  apply (n05_canonicalChart_ae_iff h04 hz hs m hangle
    (fun p => f (K.inverseChart z m p) = g (K.inverseChart z m p))).mpr
  rcases h04 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  have hleft := (hcharts z hz hs m).2.2.1
  filter_upwards [hpiece,
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
  simpa only [hleft p ⟨hpm.1, mem_univ _⟩] using hp

/-- Both frozen transforms depend only on the actual physical equivalence
class, once the genuine controlled reference coordinates are fixed. -/
theorem n05_referenceCanonical_representatives_congr_ae
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {f g : PolarPoint → ℝ} (hfg : f =ᵐ[radialPhysicalMeasure D] g) (m : ℕ) :
    (canonicalHeight S K (C.referenceState, 0) m f
      =ᵐ[canonicalMeasure S K m] canonicalHeight S K (C.referenceState, 0) m g) ∧
    (canonicalSource S K (C.referenceState, 0) m f
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m g) := by
  have h01 := h.1.1.1
  have hpull := n05_inverseChart_ae_eq_of_physical h.2.2.2.2
    (n05_referenceState_mem h01.2.1)
    (n05_referenceState_sector h01.2.2.1) m
    (fun _ hp => n05_controlledReference_chart_second hcoordinates m hp) hfg
  constructor
  · filter_upwards [hpull] with p hp
    simp only [canonicalHeight, hp]
  · filter_upwards [hpull] with p hp
    simp only [canonicalSource, hp]

end ContinuousFlexibility.Statements
