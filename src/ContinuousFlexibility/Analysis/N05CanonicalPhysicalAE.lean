import ContinuousFlexibility.Analysis.N05ReferenceInterface
import ContinuousFlexibility.Analysis.N05ReferenceResidual
import ContinuousFlexibility.Analysis.SpacesMollifierL1
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Almost-everywhere transfer through the actual canonical charts

Differentiability of the genuine inverse chart sends the canonical exceptional
null set to a physical null set. The actual height and Jacobian then permit
cancellation in the frozen source formula. Periodicity and the N04 null-set
cover identify the physical source on its full physical measure.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- The controlled reference chart preserves the actual angular coordinate. -/
theorem n05_controlledReference_chart_second
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ referencePhysicalPieceOpen S K m) :
    (K.chart (C.referenceState, 0) m p).2 = p.2 := by
  have he := congrArg (fun q : PolarPoint => q.2) (hcoordinates.1 m p hp).1
  exact he

/-- A differentiable left inverse transfers almost-everywhere predicates.
The null set need not be measurable. -/
theorem n05_differentiableInverse_ae_pullback
    {U V : Set PolarPoint} {Φ Ψ : PolarPoint → PolarPoint}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hΦ : MapsTo Φ U V) (hleft : ∀ x ∈ U, Ψ (Φ x) = x)
    (hΨ : DifferentiableOn ℝ Ψ V) {P : PolarPoint → Prop}
    (hP : ∀ᵐ y ∂volume.restrict V, P y) :
    ∀ᵐ x ∂volume.restrict U, P (Φ x) := by
  have hbad : volume ({y | ¬ P y} ∩ V) = 0 := by
    simpa only [Measure.restrict_apply' hV] using ae_iff.mp hP
  have himg : volume (Ψ '' ({y | ¬ P y} ∩ V)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hΨ.mono inter_subset_right) hbad
  apply ae_iff.mpr
  rw [Measure.restrict_apply' hU]
  apply measure_mono_null ?_ himg
  rintro x ⟨hx, hxU⟩
  exact ⟨Φ x, ⟨hx, hΦ hxU⟩, hleft x hxU⟩

/-- Both directions follow from the same null-image argument. -/
theorem n05_diffeomorphism_ae_iff
    {U V : Set PolarPoint} {Φ Ψ : PolarPoint → PolarPoint}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hΦ : MapsTo Φ U V) (hΨ : MapsTo Ψ V U)
    (hleft : ∀ x ∈ U, Ψ (Φ x) = x) (hright : ∀ y ∈ V, Φ (Ψ y) = y)
    (hΦd : DifferentiableOn ℝ Φ U) (hΨd : DifferentiableOn ℝ Ψ V)
    (P : PolarPoint → Prop) :
    (∀ᵐ y ∂volume.restrict V, P y) ↔
      ∀ᵐ x ∂volume.restrict U, P (Φ x) := by
  constructor
  · exact n05_differentiableInverse_ae_pullback hU hV hΦ hleft hΨd
  · intro hP
    have hpull := n05_differentiableInverse_ae_pullback hV hU hΨ hright hΦd hP
    filter_upwards [hpull, ae_restrict_mem hV] with y hy hyV
    simpa only [hright y hyV] using hy

/-- The N04 charts preserve null sets on the actual physical half-period tiles
whenever their angular coordinate is unchanged. This applies to the controlled
reference coordinates without assuming a pushforward-measure identity. -/
theorem n05_canonicalChart_ae_iff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K z m, (K.chart z m p).2 = p.2)
    (P : PolarPoint → Prop) :
    (∀ᵐ y ∂canonicalMeasure S K m, P y) ↔
      ∀ᵐ x ∂volume.restrict
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)),
        P (K.chart z m x) := by
  obtain ⟨hΦ, hΨ, hleft, hright, hΦc, hΨc, _, _⟩ := h04.1.charts z hz hs m
  let U : Set PolarPoint :=
    physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)
  let V : Set PolarPoint :=
    Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi
  have hUopen : U ⊆ physicalPieceOpen S K z m := inter_subset_left
  have hVopen : V ⊆ canonicalOpen S K m :=
    fun _ hp => ⟨hp.1, mem_univ _⟩
  have hΦUV : MapsTo (K.chart z m) U V := by
    intro p hp
    refine ⟨(hΦ (hUopen hp)).1, ?_⟩
    simpa only [hangle p (hUopen hp)] using hp.2.2
  have hΨVU : MapsTo (K.inverseChart z m) V U := by
    intro p hp
    have hpopen := hVopen hp
    have hsecond : (K.inverseChart z m p).2 = p.2 := by
      have he := congrArg Prod.snd (hright p hpopen)
      simpa only [hangle _ (hΨ hpopen)] using he
    exact ⟨hΨ hpopen, mem_univ _, by simpa only [hsecond] using hp.2⟩
  exact n05_diffeomorphism_ae_iff
    ((h04.1.domains z hz hs m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc))
    (measurableSet_Ioo.prod measurableSet_Ioc)
    hΦUV hΨVU (fun p hp => hleft p (hUopen hp))
    (fun p hp => hright p (hVopen hp))
    ((hΦc.differentiableOn (by simp)).mono hUopen)
    ((hΨc.differentiableOn (by simp)).mono hVopen) P

/-- Equality of canonical source representatives is equivalent to equality
of the actual physical sources on a piece. The source multiplier is cancelled
using N04's strictly positive height and nonzero genuine Jacobian. -/
theorem n05_canonicalSource_ae_iff_physicalPiece
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K z m, (K.chart z m p).2 = p.2)
    (f g : PolarPoint → ℝ) :
    canonicalSource S K z m f =ᵐ[canonicalMeasure S K m] canonicalSource S K z m g ↔
      f =ᵐ[volume.restrict
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))] g := by
  have htransport := n05_canonicalChart_ae_iff h04 hz hs m hangle
    (fun p => canonicalSource S K z m f p = canonicalSource S K z m g p)
  obtain ⟨_, _, hleft, _, _, _, _, hnonzero⟩ := h04.1.charts z hz hs m
  have hmeas : MeasurableSet
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) :=
    (h04.1.domains z hz hs m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc)
  refine htransport.trans ?_
  constructor
  · intro hfg
    filter_upwards [hfg,
      ae_restrict_mem hmeas] with p hp hpU
    have hpopen : p ∈ physicalPieceOpen S K z m := hpU.1
    have hpos := hnonzero p hpopen
    simp only [canonicalSource, hleft p hpopen] at hp
    exact mul_left_cancel₀ hpos.1.ne'
      ((div_left_inj' (abs_ne_zero.mpr hpos.2.1)).mp hp)
  · intro hfg
    filter_upwards [hfg,
      ae_restrict_mem hmeas] with p hp hpU
    have hpopen : p ∈ physicalPieceOpen S K z m := hpU.1
    simp only [canonicalSource, hleft p hpopen, hp]

/-- Translating a genuine π-periodic field backwards by one period preserves
its value. The equality is stated with the actual product addition. -/
theorem n05_piPeriodic_sub {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) (p : PolarPoint) :
    f (p - (0, Real.pi)) = f p := by
  have he : f ((p - (0, Real.pi)) + (0, Real.pi)) = f (p - (0, Real.pi)) :=
    hf (p - (0, Real.pi))
  have hp : (p - ((0, Real.pi) : PolarPoint)) + (0, Real.pi) = p :=
    sub_add_cancel p ((0, Real.pi) : PolarPoint)
  exact he.symm.trans (congrArg f hp)

/-- A genuine π-periodic pair equal on the canonical half-period is equal
on the full angular interval in the frozen physical measure. -/
theorem n05_piPeriodic_ae_eq_fullPeriod
    {J : Set ℝ} (hJ : MeasurableSet J) {f g : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi))
    (hg : Function.Periodic g (0, Real.pi))
    (hfg : f =ᵐ[volume.restrict (J ×ˢ Ioc (0 : ℝ) Real.pi)] g) :
    f =ᵐ[volume.restrict (J ×ˢ Ioc (0 : ℝ) (2 * Real.pi))] g := by
  have hhalf := ae_imp_of_ae_restrict hfg
  have hshift := (measurePreserving_sub_right volume
    ((0, Real.pi) : PolarPoint)).quasiMeasurePreserving.ae hhalf
  apply (ae_restrict_iff' (hJ.prod measurableSet_Ioc)).mpr
  filter_upwards [hhalf, hshift] with p hp hs
  intro hpfull
  by_cases hθ : p.2 ≤ Real.pi
  · exact hp ⟨hpfull.1, hpfull.2.1, hθ⟩
  · have hθ' : Real.pi < p.2 := lt_of_not_ge hθ
    have hq : p - (0, Real.pi) ∈ J ×ˢ Ioc (0 : ℝ) Real.pi := by
      constructor
      · simpa using hpfull.1
      · change 0 < p.2 - Real.pi ∧ p.2 - Real.pi ≤ Real.pi
        constructor <;> linarith [hpfull.2.2]
    calc
      f p = f (p - (0, Real.pi)) := (n05_piPeriodic_sub hf p).symm
      _ = g (p - (0, Real.pi)) := hs hq
      _ = g p := n05_piPeriodic_sub hg p

/-- Canonical representatives determine the actual periodic physical source
on every point outside the genuine N04 null exceptional cover. -/
theorem n05_referenceCanonicalSource_ae_physical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {f g : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi))
    (hg : Function.Periodic g (0, Real.pi))
    (hfg : ∀ m, canonicalSource S K (C.referenceState, 0) m f
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m g) :
    f =ᵐ[radialPhysicalMeasure D] g := by
  have h01 := h.1.1.1
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hs : stateSector S C.referenceState :=
    n05_referenceState_sector h01.2.2.1
  have hpiece : ∀ m, ∀ᵐ p : PolarPoint ∂volume,
      p ∈ Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ
        Ioc (0 : ℝ) (2 * Real.pi) → f p = g p := by
    intro m
    apply ae_imp_of_ae_restrict
    apply n05_piPeriodic_ae_eq_fullPeriod measurableSet_Ioo hf hg
    have hangle : ∀ p ∈ physicalPieceOpen S K (C.referenceState, 0) m,
        (K.chart (C.referenceState, 0) m p).2 = p.2 := by
      intro p hp
      apply n05_controlledReference_chart_second hcoordinates m
      simpa only [h.2.2.2.2.1.1.referenceDomain m] using hp
    have hp := (n05_canonicalSource_ae_iff_physicalPiece h.2.2.2.2.1 hz hs m
      hangle f g).mp (hfg m)
    simpa only [h.2.2.2.2.1.1.referenceDomain m, referencePhysicalPieceOpen,
      prod_inter_prod, inter_univ, univ_inter] using hp
  obtain ⟨E, hE, hcover⟩ := h.2.2.2.2.1.1.referencePartition
  have hEplane : ∀ᵐ p : PolarPoint ∂volume, p.1 ∉ E := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae (measure_eq_zero_iff_ae_notMem.mp hE)
  change ∀ᵐ p ∂volume.restrict (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) (2 * Real.pi)), f p = g p
  apply (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioc)).mpr
  filter_upwards [ae_all_iff.mpr hpiece, hEplane] with p hp hpE
  intro hpD
  obtain ⟨m, hm, _⟩ := hcover p.1 ⟨hpD.1, hpE⟩
  exact hp m ⟨hm, hpD.2⟩

end ContinuousFlexibility.Statements
