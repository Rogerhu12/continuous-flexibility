import ContinuousFlexibility.Analysis.CanonicalSourceConversion
import ContinuousFlexibility.Analysis.N07bCanonicalSourceJets
import ContinuousFlexibility.Analysis.N07aCanonicalHalfStrip

/-!
# The actual current physical measure and closed-piece bounds

The integration domain follows the state. Fixed radial rectangles are
retained only for reference-state wrappers. Bounds here are qualitative:
their constants may depend on the particular state and piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- The fixed reference physical interval, used by reference-only APIs. -/
def n07aPhysicalIntervalData {S : PhysicalSpacesData} (K : CanonicalData S) :
    CanonicalData S :=
  { K with left := K.physicalLeft, right := K.physicalRight }

/-- The actual state-dependent physical piece on one angular period. -/
def n07aPhysicalMeasure (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : Measure PolarPoint :=
  volume.restrict (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07aPhysicalMeasure_reference
    (h04 : N04Properties D T S C L K base loss ε) (m : ℕ) :
    n07aPhysicalMeasure S K (C.referenceState, 0) m =
      canonicalMeasure S (n07aPhysicalIntervalData K) m := by
  rw [n07aPhysicalMeasure, h04.1.referenceDomain]
  simp only [referencePhysicalPieceOpen, canonicalMeasure,
    n07aPhysicalIntervalData, prod_inter_prod, inter_univ, univ_inter]

theorem n07aPhysicalMeasure_eq_openAngularStrip (m : ℕ) :
    n07aPhysicalMeasure S K z m =
      volume.restrict (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) :=
  Measure.restrict_congr_set
    (polarDomain_Ioc_ae_eq_Ioo (physicalPieceOpen S K z m) 0 Real.pi)

theorem n07a_canonicalMeasure_eq_openAngularStrip (m : ℕ) :
    canonicalMeasure S K m =
      volume.restrict (canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) := by
  simpa only [canonicalMeasure, canonicalOpen, prod_inter_prod,
    inter_univ, univ_inter] using
    Measure.restrict_congr_set
      (polarStrip_Ioc_ae_eq_Ioo (K.left m) (K.right m) 0 Real.pi)

theorem n07aPhysicalMeasure_ae
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    ∀ᵐ p ∂n07aPhysicalMeasure S K z m, p ∈ physicalPieceOpen S K z m :=
  (ae_restrict_mem ((h04.1.domains z hz hs m).1.measurableSet.inter
    (MeasurableSet.univ.prod measurableSet_Ioc))).mono fun _ hp => hp.1

theorem n07aPhysicalMeasure_le_annulus
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    n07aPhysicalMeasure S K z m ≤
      volume.restrict (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi) := by
  apply Measure.restrict_mono _ le_rfl
  intro p hp
  exact ⟨((h04.1.domains z hz hs m).2.2.1 hp.1).1, hp.2.2⟩

/-- Use the open angular strip for exact image identities; its omitted
angular boundary has zero measure on every actual current domain. -/
theorem n07a_physicalHalfGeometry
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    let Q := physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)
    (K.chart z m '' Q = canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) ∧
    InjOn (K.chart z m) Q ∧
    (∀ p ∈ Q, HasFDerivWithinAt (K.chart z m) (fderiv ℝ (K.chart z m) p) Q p) ∧
    (∀ p ∈ Q, K.inverseChart z m (K.chart z m p) = p ∧
      K.height z m p ≠ 0 ∧ planeJacobian (K.chart z m) p ≠ 0) := by
  have hgeo := h04.1.charts z hz hs m
  have hopen := (h04.1.domains z hz hs m).1
  refine ⟨canonicalChart_image_openStrip h04.1 hz hs m,
    (canonicalChart_injOn h04.1 hz hs m).mono inter_subset_left, ?_, ?_⟩
  · intro p hp
    exact ((hgeo.2.2.2.2.1.contDiffAt (hopen.mem_nhds hp.1)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  · intro p hp
    exact ⟨hgeo.2.2.1 p hp.1, (hgeo.2.2.2.2.2.2.2 p hp.1).1.ne',
      (hgeo.2.2.2.2.2.2.2 p hp.1).2.1⟩

theorem n07a_current_inverseChart_periodic
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    ∀ p ∈ canonicalOpen S K m,
      K.inverseChart z m (p + (0, Real.pi)) = K.inverseChart z m p + (0, Real.pi) := by
  have hgeo := h04.1.charts z hz hs m
  exact fun _ hp => inverseChart_periodic_of_chart_periodic_on hgeo.2.1
    (fun p hp => ((h04.1.domains z hz hs m).2.2.2.1 p).mpr hp)
    hgeo.2.2.1 hgeo.2.2.2.1
    (fun p hp => (hgeo.2.2.2.2.2.2.2 p hp).2.2.1) hp

/-- Closed-piece smoothness bounds every actual physical derivative on
the current fundamental piece by compactness in canonical coordinates. -/
theorem n07a_physical_mixedDerivative_bound_ae
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ p ∈ physicalPieceClosed S K z m, ContDiffAt ℝ ∞ f p) (a b : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ p ∂n07aPhysicalMeasure S K z m,
      |mixedDerivative a b f p| ≤ B := by
  let e : PolarPoint → ℝ := fun q => mixedDerivative a b f (K.inverseChart z m q)
  have he : ∀ q ∈ canonicalClosed S K m, ContDiffAt ℝ ∞ e q := by
    intro q hq
    exact (contDiffAt_mixedDerivative
      (hf _ ((h04.1.boundary z hz hs m).2.1 hq)) a b).comp q
        (n04b_inverseChart_contDiffAt_closed h04.1 hz hs m hq)
  obtain ⟨B, hB, hbound⟩ := n07b_canonical_mixedDerivative_bound_closed m he 0 0
  refine ⟨B, hB, ?_⟩
  rw [n07aPhysicalMeasure_eq_openAngularStrip]
  have hQ := ((h04.1.domains z hz hs m).1.inter
    (isOpen_univ.prod isOpen_Ioo)).measurableSet
  filter_upwards [ae_restrict_mem hQ] with p hp
  have himage : K.chart z m p ∈
      canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi) := by
    rw [← canonicalChart_image_openStrip h04.1 hz hs m]
    exact mem_image_of_mem _ hp
  have hb := hbound (K.chart z m p)
    ⟨Ioo_subset_Icc_self himage.1.1, Ioo_subset_Icc_self himage.2.2⟩
  simpa only [spaces_mixedDerivative_zero, e,
    (h04.1.charts z hz hs m).2.2.1 p hp.1, Real.norm_eq_abs] using hb

end ContinuousFlexibility.Analysis
