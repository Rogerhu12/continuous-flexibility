import ContinuousFlexibility.Analysis.N07aAngularPhysicalRepresentative
import ContinuousFlexibility.Analysis.N07aCanonicalSmoothJets
import ContinuousFlexibility.Analysis.N07aOpenClassicalNormal

/-!
# Actual physical evenness survives gluing across all interfaces

The canonical reflection fixes each original L² coordinate. Its smooth
decoder is therefore even, and the actual reference/current chart symmetry
transfers that fact to each physical piece. A.e. radial coverage and
continuity then give evenness at roots and artificial cuts as well.
-/

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
    (heven : ∀ m p, p ∈ physicalPieceOpen S K m → v (p.1, -p.2) = v p) :
    ∀ r θ, v (r, -θ) = v (r, θ) := by
  obtain ⟨E, hE, hcover⟩ := h04.2.2.2.2.2.2.1
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
    ∀ r θ, v (r, -θ) = v (r, θ) := by
  apply n07a_physical_even_of_piecewise h04 hv.continuousOn hzero
  intro m p hp
  have hm : K.left m < K.right m := (h04.2.2.2.1 m).2.1
  let u : n07aCanonicalSmoothSpace S K m := ⟨U.1 m, hU m⟩
  let w := n07aCanonicalSmoothDecode hm u
  have hw := n07aCanonicalSmoothRepresentative_properties hm u
  have hwe : ∀ q ∈ canonicalOpen S K m, w (q.1, -q.2) = w q := by
    intro q _
    exact n07aCanonicalSmoothRepresentative_even hm u
      ((n07aAngularReflection_fixed_iff m (U.1 m)).mp (hEven m)) q
  let wp := n07aPhysicalHeightRepresentative K z m w
  have hwp := n07aPhysicalHeightRepresentative_contDiffOn h04 hz hs m hw.1
  have hwpp := n07aPhysicalHeightRepresentative_periodic_on h04 hz hs m hw.2.1
  have hwpe := n07aPhysicalHeightRepresentative_even_on h04 hz hs m hwe
  have hae := n07aPhysicalHeightRepresentative_ae h04 hz hs hrep m hw.2.2.1.symm
  have hsub : physicalPieceOpen S K m ⊆ annularOpen D :=
    fun q hq => ⟨(h04.2.2.2.1 m).2.2 hq.1, mem_univ _⟩
  have hχ : ContDiff ℝ ∞ (fun q : PolarPoint => U.2.1 * S.chiLeft q.1) :=
    contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)
  have he : EqOn wp (fun q => v q - U.2.1 * S.chiLeft q.1) (physicalPieceOpen S K m) :=
    n07a_canonical_periodicOn_eqOn_of_ae_eq
      (S := S) (K := n07aPhysicalIntervalData K) (m := m) hwp.continuousOn
      ((hv.mono hsub).sub hχ.contDiffOn).continuousOn hwpp
      (fun q _ => by simp only [hvp q, Prod.fst_add, add_zero]) hae
  have hplus := he hp
  have hminus := he (show (p.1, -p.2) ∈ physicalPieceOpen S K m from ⟨hp.1, mem_univ _⟩)
  have hflip := hwpe p hp
  dsimp only [wp] at hplus hminus
  linarith only [hplus, hminus, hflip]

end ContinuousFlexibility.Analysis
