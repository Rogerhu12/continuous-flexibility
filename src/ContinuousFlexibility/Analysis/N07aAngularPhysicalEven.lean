module

public import ContinuousFlexibility.Analysis.N07aAngularPhysicalRepresentative
public import ContinuousFlexibility.Analysis.N07aCanonicalSmoothJets
public import ContinuousFlexibility.Analysis.N07aOpenClassicalNormal
public import ContinuousFlexibility.Analysis.N07aAngularCandidateCoordinates

/-!
# Actual physical evenness survives gluing across all interfaces

The canonical reflection fixes each original L² coordinate. Its smooth
decoder is therefore even, and the actual reference/current chart symmetry
transfers that fact to each physical piece. The reference radial cover and the current planar cover are treated
separately; continuity supplies equality at roots and artificial cuts.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_physical_even_of_piecewise
    (h04 : N04Properties D T S C L K base loss ε)
    {v : PolarPoint → ℝ} (hv : ContinuousOn v (annularOpen D))
    (hzero : ∀ p, p ∉ annularOpen D → v p = 0)
    (heven : ∀ m p, p ∈ referencePhysicalPieceOpen S K m → v (p.1, -p.2) = v p) :
    ∀ r θ, v (r, -θ) = v (r, θ) := by
  obtain ⟨E, hE, hcover⟩ := h04.1.referencePartition
  have hEr : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ E := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hE
  intro r θ
  by_cases hr : r ∈ Ioo D.a D.b
  · have hpoint : ∀ᵐ t ∂volume.restrict (Ioo D.a D.b), v (t, -θ) = v (t, θ) := by
      have hEr' := hEr.filter_mono (ae_mono (Measure.restrict_le_self
        (μ := (volume : Measure ℝ)) (s := Ioo D.a D.b)))
      filter_upwards [hEr', ae_restrict_mem measurableSet_Ioo] with t ht htD
      obtain ⟨m, hm, _⟩ := hcover t ⟨htD, ht⟩
      exact heven m (t, θ) ⟨hm, mem_univ _⟩
    exact Measure.eqOn_open_of_ae_eq hpoint isOpen_Ioo
      (hv.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ ht => ⟨ht, mem_univ _⟩))
      (hv.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ ht => ⟨ht, mem_univ _⟩)) hr
  · rw [hzero (r, -θ) (fun hp => hr hp.1), hzero (r, θ) (fun hp => hr hp.1)]

/-- The planar current atlas transfers pointwise piecewise evenness to
the complete annulus by its genuine planar null-set cover. -/
theorem n07a_current_physical_even_of_piecewise
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {v : PolarPoint → ℝ} (hv : ContinuousOn v (annularOpen D))
    (hzero : ∀ p, p ∉ annularOpen D → v p = 0)
    (heven : ∀ m p, p ∈ physicalPieceOpen S K z m → v (p.1, -p.2) = v p) :
    ∀ r theta, v (r, -theta) = v (r, theta) := by
  obtain ⟨E, hE, hcover⟩ := h04.1.partition z hz hs
  have hEae : ∀ᵐ p : PolarPoint ∂volume, p ∉ E := by
    apply ae_iff.mpr
    simpa only [not_not, setOf_mem_eq] using hE
  have hpoint : (fun p : PolarPoint => v (p.1, -p.2)) =ᵐ[
      volume.restrict (annularOpen D)] v := by
    filter_upwards [hEae.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem (isOpen_Ioo.prod isOpen_univ).measurableSet] with p hpE hpD
    obtain ⟨m, hm, _⟩ := hcover p ⟨hpD, hpE⟩
    exact heven m p hm
  have he : EqOn (fun p : PolarPoint => v (p.1, -p.2)) v (annularOpen D) :=
    Measure.eqOn_open_of_ae_eq hpoint (isOpen_Ioo.prod isOpen_univ)
      (hv.comp (continuous_fst.prodMk continuous_snd.neg).continuousOn
        (fun p hp => ⟨hp.1, mem_univ _⟩)) hv
  intro r theta
  by_cases hr : r ∈ Ioo D.a D.b
  · have hp : (r, theta) ∈ annularOpen D := ⟨hr, mem_univ _⟩
    exact he hp
  · rw [hzero (r, -theta) (fun hp => hr hp.1),
      hzero (r, theta) (fun hp => hr hp.1)]

/-- Evenness concerns the same globally reconstructed physical field,
not an independently averaged replacement of the solution. -/
theorem n07a_canonicalRepresentation_smooth_even
    (hS : IsPhysicalSpaces D T S)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {v f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K z U F v f)
    (hU : ∀ m n, N07aCanonicalNormalRegular S K m (U.1 m) n)
    (hEven : ∀ m, n07aAngularReflection m (U.1 m) = U.1 m)
    (hv : ContDiffOn ℝ ∞ v (annularOpen D))
    (hvp : Function.Periodic v (0, Real.pi))
    (hzero : ∀ p, p ∉ annularOpen D → v p = 0) :
    ∀ r theta, v (r, -theta) = v (r, theta) := by
  apply n07a_current_physical_even_of_piecewise h04 hz hs hv.continuousOn hzero
  intro m p hp
  have hm : K.left m < K.right m := (h04.1.referenceBounds m).2.1
  let u : n07aCanonicalSmoothSpace S K m := ⟨U.1 m, hU m⟩
  let w := n07aCanonicalSmoothDecode hm u
  have hw := n07aCanonicalSmoothRepresentative_properties hm u
  have hwe : ∀ q ∈ canonicalOpen S K m, w (q.1, -q.2) = w q := by
    intro q _
    exact n07aCanonicalSmoothRepresentative_even hm u
      ((n07aAngularReflection_fixed_iff m (U.1 m)).mp (hEven m)) q
  have hchi : ContDiff ℝ ∞ (fun q : PolarPoint => U.2.1 * S.chiLeft q.1) :=
    contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)
  let rem : PolarPoint → ℝ := fun q => v q - U.2.1 * S.chiLeft q.1
  have hremp : Function.Periodic rem (0, Real.pi) := by
    intro q
    simp only [rem, hvp q, Prod.fst_add, add_zero]
  have hecan : EqOn w (canonicalHeight S K z m rem) (canonicalOpen S K m) :=
    n07a_canonical_periodicOn_eqOn_of_ae_eq hw.1.continuousOn
      (n07a_candidateCanonicalHeight_contDiffOn h04 hz hs (hv.sub hchi.contDiffOn) m).continuousOn
      (fun q _ => hw.2.1 q) (n07a_candidateCanonicalHeight_periodic h04 hz hs hremp m)
      (hw.2.2.1.trans (hrep.1 m))
  have hgeo := h04.1.charts z hz hs m
  have hephys : EqOn (n07aPhysicalHeightRepresentative K z m w) rem
      (physicalPieceOpen S K z m) := by
    intro q hq
    simp only [n07aPhysicalHeightRepresentative, hecan (hgeo.1 hq),
      canonicalHeight, hgeo.2.2.1 q hq]
    field_simp [(hgeo.2.2.2.2.2.2.2 q hq).1.ne']
  have hplus := hephys hp
  have hminus := hephys (((h04.1.domains z hz hs m).2.2.2.2.1 p).mpr hp)
  have hflip := n07aPhysicalHeightRepresentative_even_on h04 hz hs m hwe p hp
  dsimp only [rem] at hplus hminus
  linarith only [hplus, hminus, hflip]

end ContinuousFlexibility.Analysis
