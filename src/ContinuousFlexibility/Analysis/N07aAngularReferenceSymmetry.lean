module

public import ContinuousFlexibility.Analysis.N07aAngularReferenceTransport
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalEven

/-!
# The same reference transport keeps the actual angular symmetries
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_physical_periodic_of_piecewise
    (h04 : N04Properties D T S C L K base loss ε)
    {v : PolarPoint → ℝ} (hv : ContinuousOn v (annularOpen D))
    (hzero : ∀ p, p ∉ annularOpen D → v p = 0)
    (hperiod : ∀ m p, p ∈ referencePhysicalPieceOpen S K m → v (p + (0, Real.pi)) = v p) :
    Function.Periodic v (0, Real.pi) := by
  obtain ⟨E, hE, hcover⟩ := h04.1.referencePartition
  have hEr : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ E := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hE
  rintro ⟨r, θ⟩
  by_cases hr : r ∈ Ioo D.a D.b
  · have hpoint : ∀ᵐ t ∂volume.restrict (Ioo D.a D.b),
        v (t, θ + Real.pi) = v (t, θ) := by
      have hEr' := hEr.filter_mono (ae_mono (Measure.restrict_le_self
        (μ := (volume : Measure ℝ)) (s := Ioo D.a D.b)))
      filter_upwards [hEr', ae_restrict_mem measurableSet_Ioo] with t ht htD
      obtain ⟨m, hm, _⟩ := hcover t ⟨htD, ht⟩
      simpa only [Prod.mk_add_mk, add_zero] using hperiod m (t, θ) ⟨hm, mem_univ _⟩
    have he := Measure.eqOn_open_of_ae_eq hpoint isOpen_Ioo
      (hv.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ ht => ⟨ht, mem_univ _⟩))
      (hv.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ ht => ⟨ht, mem_univ _⟩)) hr
    simpa only [Prod.mk_add_mk, add_zero] using he
  · rw [hzero ((r, θ) + (0, Real.pi))
      (fun hp => hr (by simpa only [Prod.fst_add, add_zero] using hp.1)),
      hzero (r, θ) (fun hp => hr hp.1)]

theorem n07aReferencePieceHeight_even_on
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (aL : ℝ) {η : PolarPoint → ℝ} (hη : ∀ r θ, η (r, -θ) = η (r, θ)) (m : ℕ) :
    ∀ p ∈ referencePhysicalPieceOpen S K m,
      n07aReferencePieceHeight C K z (K.inverseChart z) aL η m (p.1, -p.2) =
        n07aReferencePieceHeight C K z (K.inverseChart z) aL η m p := by
  intro p hp
  have hrefz := n07a_reference_mem_stateNeighborhood h01
  have hrefs := h01.2.2.1.stateSector
  have hpref : p ∈ physicalPieceOpen S K (C.referenceState, 0) m := by
    rw [h04.1.referenceDomain m]
    exact hp
  have hr := h04.1.reflection (C.referenceState, 0) hrefz hrefs m p hpref
  have hcanon := (h04.1.charts (C.referenceState, 0) hrefz hrefs m).1 hpref
  have hphys := (h04.1.charts z hz hs m).2.1 hcanon
  have hinv := h04.1.inverseReflection z hz hs m
    (K.chart (C.referenceState, 0) m p) hcanon
  have hc := h04.1.reflection z hz hs m
    (K.inverseChart z m (K.chart (C.referenceState, 0) m p)) hphys
  simp only [n07aReferencePieceHeight, hr.1, hr.2.1, hinv, hc.2.1, hη]

end ContinuousFlexibility.Analysis
