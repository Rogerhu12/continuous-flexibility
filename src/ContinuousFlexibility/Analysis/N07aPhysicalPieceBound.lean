module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalEven

/-!
# Continuous physical inequalities extend from the actual open pieces

The original exceptional set is null in the radial variable and works
at every fixed angle. Equality with the pointwise minimum extends from
almost everywhere to the entire open annulus.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_physicalPieceInterior_ae
    (h04 : N04Properties D T S C L K base loss ε) :
    ∀ᵐ r ∂volume.restrict (radialCore D),
      ∃ m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) := by
  obtain ⟨E, hE, hcover⟩ := h04.1.referencePartition
  have hEr : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ E := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hE
  have hEr' := hEr.filter_mono (ae_mono (Measure.restrict_le_self
    (μ := (volume : Measure ℝ)) (s := radialCore D)))
  filter_upwards [hEr', ae_restrict_mem measurableSet_Ioo] with r hr hrD
  obtain ⟨m, hm, _⟩ := hcover r ⟨hrD, hr⟩
  exact ⟨m, hm⟩

theorem n07a_physicalPiece_bound
    (h04 : N04Properties D T S C L K base loss ε)
    {f B : PolarPoint → ℝ} (hf : ContinuousOn f (annularOpen D))
    (hB : ContinuousOn B (annularOpen D))
    (hbound : ∀ m p, p ∈ referencePhysicalPieceOpen S K m → f p ≤ B p) :
    ∀ p ∈ annularOpen D, f p ≤ B p := by
  intro p hp
  have hfc : ContinuousOn (fun r => f (r, p.2)) (radialCore D) :=
    hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hr, mem_univ _⟩)
  have hBc : ContinuousOn (fun r => B (r, p.2)) (radialCore D) :=
    hB.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hr, mem_univ _⟩)
  have he : (fun r => f (r, p.2)) =ᵐ[volume.restrict (radialCore D)]
      (fun r => min (f (r, p.2)) (B (r, p.2))) := by
    filter_upwards [n07a_physicalPieceInterior_ae h04] with r hr
    obtain ⟨m, hm⟩ := hr
    exact (min_eq_left (hbound m (r, p.2) ⟨hm, mem_univ _⟩)).symm
  have hpoint := Measure.eqOn_open_of_ae_eq he isOpen_Ioo hfc
    ((continuous_fst.min continuous_snd).comp_continuousOn (hfc.prodMk hBc)) hp.1
  exact hpoint.trans_le (min_le_right _ _)

end ContinuousFlexibility.Analysis
