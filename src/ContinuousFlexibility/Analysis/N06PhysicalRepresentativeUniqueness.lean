import ContinuousFlexibility.Analysis.N06PeriodicAlmostEverywhere

/-!
# Canonical equality determines the physical representative almost everywhere

The inverse lift identity follows from N04's actual inverse identities.
Periodic canonical heights therefore agree on the whole strip whenever
they agree in the measured half-period tile. The smooth chart then transports
this identity to the physical piece. The countable piece cover gives the
global statement on the annulus.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n06_inverseChart_lift
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    K.inverseChart z m (p + (0, Real.pi)) = K.inverseChart z m p + (0, Real.pi) := by
  have hc := hN04.2.2.2.2.2.2.2.1 z hz hs m
  have hpI := hc.2.1 hp
  have hpI' : K.inverseChart z m p + (0, Real.pi) ∈ physicalPieceOpen S K m := by
    exact ⟨by simpa only [Prod.fst_add, add_zero] using hpI.1, mem_univ _⟩
  have hlift := (hc.2.2.2.2.2.2.2 _ hpI).2.2.1
  have hchart : K.chart z m (K.inverseChart z m p + (0, Real.pi)) = p + (0, Real.pi) :=
    hlift.trans (congrArg (fun q : PolarPoint => q + (0, Real.pi)) (hc.2.2.2.1 p hp))
  exact (congrArg (K.inverseChart z m) hchart).symm.trans (hc.2.2.1 _ hpI')

theorem n06_canonicalHeight_periodic_slice
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {η : PolarPoint → ℝ}
    (hη : Function.Periodic η (0, Real.pi)) {y : ℝ}
    (hy : y ∈ Ioo (K.left m) (K.right m)) :
    Function.Periodic (fun θ => canonicalHeight S K z m η (y, θ)) Real.pi := by
  intro θ
  have hp : (y, θ) ∈ canonicalOpen S K m := ⟨hy, mem_univ _⟩
  have hc := hN04.2.2.2.2.2.2.2.1 z hz hs m
  have hheight := (hc.2.2.2.2.2.2.2 _ (hc.2.1 hp)).2.2.2
  have hlift := n06_inverseChart_lift hN04 hz hs m hp
  have hlift' : K.inverseChart z m (y, θ + Real.pi) =
      K.inverseChart z m (y, θ) + (0, Real.pi) := by
    simpa only [Prod.mk_add_mk, add_zero] using hlift
  change η (K.inverseChart z m (y, θ + Real.pi)) /
      K.height z m (K.inverseChart z m (y, θ + Real.pi)) = _
  rw [hlift', hη, hheight]
  rfl

/-- The actual canonical height is injective on periodic physical fields
modulo equality almost everywhere on its physical piece. -/
theorem n06_canonicalHeight_ae_injective_piece
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {η ξ : PolarPoint → ℝ}
    (hη : Function.Periodic η (0, Real.pi)) (hξ : Function.Periodic ξ (0, Real.pi))
    (heq : canonicalHeight S K z m η =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m ξ) :
    η =ᵐ[volume.restrict (physicalPieceOpen S K m)] ξ := by
  have hall := n06_periodic_ae_eq_on_strip
    (fun y hy => n06_canonicalHeight_periodic_slice hN04 hz hs m hη hy)
    (fun y hy => n06_canonicalHeight_periodic_slice hN04 hz hs m hξ hy) heq
  have hphysical := n06_canonical_ae_pullback hN04 hz hs m hall
  have hc := hN04.2.2.2.2.2.2.2.1 z hz hs m
  filter_upwards [hphysical,
    ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with p hp hpU
  have hleft := hc.2.2.1 p hpU
  have hheight := (hc.2.2.2.2.2.2.2 p hpU).1.ne'
  change η (K.inverseChart z m (K.chart z m p)) /
      K.height z m (K.inverseChart z m (K.chart z m p)) =
    ξ (K.inverseChart z m (K.chart z m p)) /
      K.height z m (K.inverseChart z m (K.chart z m p)) at hp
  rw [hleft] at hp
  exact (div_left_inj' hheight).mp hp

theorem n06_physical_piece_cover_ae
    (hN04 : N04Properties D T S C L K base loss ε) :
    ∀ᵐ p ∂volume.restrict (annularOpen D), ∃ m, p ∈ physicalPieceOpen S K m := by
  obtain ⟨_, _, _, _, _, _, ⟨E, hE, hcover⟩, _⟩ := hN04
  have hr : ∀ᵐ r ∂volume.restrict (Ioo D.a D.b),
      ∃ m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    have havoid : ∀ᵐ r ∂volume, r ∉ E := by
      apply ae_iff.mpr
      exact measure_mono_null (fun _ hr => Classical.not_not.mp hr) hE
    filter_upwards [havoid] with r hr hrU
    exact (hcover r ⟨hrU, hr⟩).exists
  have hprod := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (Ioo D.a D.b)) (ν := (volume : Measure ℝ))).ae hr
  have hmeasure : (volume.restrict (Ioo D.a D.b)).prod (volume : Measure ℝ) =
      volume.restrict (annularOpen D) := by
    change _ = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      (Ioo D.a D.b ×ˢ univ)
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hmeasure] at hprod
  filter_upwards [hprod] with p hp
  obtain ⟨m, hm⟩ := hp
  exact ⟨m, hm, mem_univ _⟩

/-- Equality of all canonical heights determines the periodic physical
field on the whole open annulus, even though the piece cover is only a.e. -/
theorem n06_canonicalHeight_ae_injective
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {η ξ : PolarPoint → ℝ}
    (hη : Function.Periodic η (0, Real.pi)) (hξ : Function.Periodic ξ (0, Real.pi))
    (heq : ∀ m, canonicalHeight S K z m η =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m ξ) : η =ᵐ[volume.restrict (annularOpen D)] ξ := by
  have hpieces : ∀ᵐ p ∂volume, ∀ m, p ∈ physicalPieceOpen S K m → η p = ξ p := by
    apply ae_all_iff.mpr
    intro m
    exact (ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)).mp
      (n06_canonicalHeight_ae_injective_piece hN04 hz hs m hη hξ (heq m))
  have hpieces' : ∀ᵐ p ∂volume.restrict (annularOpen D),
      ∀ m, p ∈ physicalPieceOpen S K m → η p = ξ p :=
    hpieces.filter_mono ae_restrict_le
  filter_upwards [hpieces', n06_physical_piece_cover_ae hN04] with p hp hcover
  obtain ⟨m, hm⟩ := hcover
  exact hp m hm

end ContinuousFlexibility.Statements
