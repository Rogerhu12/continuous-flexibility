import ContinuousFlexibility.Analysis.N05ReferenceSymbolClosure
import ContinuousFlexibility.Analysis.CanonicalStripGeometry
import ContinuousFlexibility.Analysis.N04bBoundaryInverseRegularity

/-!
# Period and reflection identities on the closed canonical pieces

N04 specifies these identities in the open physical pieces.  Its actual
closed-piece smoothness extends them to both endpoints for every admitted
state, without imposing any values on the inverse chart at the endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n05_canonical_closed_periodicity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K z m) :
    K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) ∧
      K.height z m (p + (0, Real.pi)) = K.height z m p := by
  have hperiodic := (h04.1.charts z hz hs m).2.2.2.2.2.2.2
  have hclosed := (h04.1.boundary z hz hs m).2.2.2.2.1
  have hτ : Continuous (fun q : PolarPoint => q + (0, Real.pi)) :=
    continuous_id.add continuous_const
  have hshiftOpen : MapsTo (fun q : PolarPoint => q + (0, Real.pi))
      (physicalPieceOpen S K z m) (physicalPieceOpen S K z m) := by
    intro q hq
    exact ((h04.1.domains z hz hs m).2.2.2.1 q).mpr hq
  have hshift : MapsTo (fun q : PolarPoint => q + (0, Real.pi))
      (physicalPieceClosed S K z m) (physicalPieceClosed S K z m) :=
    hshiftOpen.closure_of_continuousOn hτ.continuousOn
  have hchart : EqOn (fun q => K.chart z m (q + (0, Real.pi)))
      (fun q => K.chart z m q + (0, Real.pi)) (physicalPieceOpen S K z m) :=
    fun q hq => (hperiodic q hq).2.2.1
  have hheight : EqOn (fun q => K.height z m (q + (0, Real.pi)))
      (K.height z m) (physicalPieceOpen S K z m) :=
    fun q hq => (hperiodic q hq).2.2.2
  constructor
  · apply hchart.of_subset_closure ?_ ?_ subset_closure (Subset.rfl) hp
    · intro q hq
      exact ((hclosed (q + (0, Real.pi)) (hshift hq)).1.continuousAt.comp
        (f := fun r : PolarPoint => r + (0, Real.pi))
        hτ.continuousAt).continuousWithinAt
    · intro q hq
      exact ((hclosed q hq).1.continuousAt.add continuousAt_const).continuousWithinAt
  · apply hheight.of_subset_closure ?_ ?_ subset_closure (Subset.rfl) hp
    · intro q hq
      exact ((hclosed (q + (0, Real.pi)) (hshift hq)).2.1.continuousAt.comp
        (f := fun r : PolarPoint => r + (0, Real.pi))
        hτ.continuousAt).continuousWithinAt
    · intro q hq
      exact (hclosed q hq).2.1.continuousAt.continuousWithinAt

theorem n05_canonical_closed_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K z m) :
    K.chart z m (p.1, -p.2) = ((K.chart z m p).1, -(K.chart z m p).2) ∧
      K.height z m (p.1, -p.2) = K.height z m p := by
  have hclosed := (h04.1.boundary z hz hs m).2.2.2.2.1
  have hτ : Continuous (fun q : PolarPoint => (q.1, -q.2)) :=
    continuous_fst.prodMk continuous_snd.neg
  have hreflectOpen : MapsTo (fun q : PolarPoint => (q.1, -q.2))
      (physicalPieceOpen S K z m) (physicalPieceOpen S K z m) := by
    intro q hq
    exact ((h04.1.domains z hz hs m).2.2.2.2.1 q).mpr hq
  have hreflect : MapsTo (fun q : PolarPoint => (q.1, -q.2))
      (physicalPieceClosed S K z m) (physicalPieceClosed S K z m) :=
    hreflectOpen.closure_of_continuousOn hτ.continuousOn
  have hchart : EqOn (fun q => K.chart z m (q.1, -q.2))
      (fun q => ((K.chart z m q).1, -(K.chart z m q).2))
      (physicalPieceOpen S K z m) :=
    fun q hq => (h04.1.reflection z hz hs m q hq).1
  have hheight : EqOn (fun q => K.height z m (q.1, -q.2))
      (K.height z m) (physicalPieceOpen S K z m) :=
    fun q hq => (h04.1.reflection z hz hs m q hq).2.1
  constructor
  · apply hchart.of_subset_closure ?_ ?_ subset_closure (Subset.rfl) hp
    · intro q hq
      exact ((hclosed (q.1, -q.2) (hreflect hq)).1.continuousAt.comp
        (f := fun r : PolarPoint => (r.1, -r.2))
        hτ.continuousAt).continuousWithinAt
    · intro q hq
      have hqChart := (hclosed q hq).1.continuousAt
      exact (hqChart.fst.prodMk hqChart.snd.neg).continuousWithinAt
  · apply hheight.of_subset_closure ?_ ?_ subset_closure (Subset.rfl) hp
    · intro q hq
      exact ((hclosed (q.1, -q.2) (hreflect hq)).2.1.continuousAt.comp
        (f := fun r : PolarPoint => (r.1, -r.2))
        hτ.continuousAt).continuousWithinAt
    · intro q hq
      exact (hclosed q hq).2.1.continuousAt.continuousWithinAt

/-- The actual closed inverse is injective because the forward chart is its
left inverse throughout the canonical closed cylinder. -/
theorem n05_canonical_closed_inverse_injOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    InjOn (K.inverseChart z m) (canonicalClosed S K m) := by
  have hright := (h04.1.boundary z hz hs m).2.2.2.1
  intro p hp q hq he
  exact (hright p hp).symm.trans ((congrArg (K.chart z m) he).trans (hright q hq))

/-- Angular translation passes to the stored inverse on the entire closed
canonical cylinder through the actual closed-domain inverse identities. -/
theorem n05_canonical_closed_inverse_periodicity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalClosed S K m) :
    K.inverseChart z m (p + (0, Real.pi)) = K.inverseChart z m p + (0, Real.pi) := by
  have hb := h04.1.boundary z hz hs m
  have hτ : Continuous (fun q : PolarPoint => q + (0, Real.pi)) :=
    continuous_id.add continuous_const
  have hshiftOpen : MapsTo (fun q : PolarPoint => q + (0, Real.pi))
      (physicalPieceOpen S K z m) (physicalPieceOpen S K z m) := by
    intro q hq
    exact ((h04.1.domains z hz hs m).2.2.2.1 q).mpr hq
  have hshift : MapsTo (fun q : PolarPoint => q + (0, Real.pi))
      (physicalPieceClosed S K z m) (physicalPieceClosed S K z m) :=
    hshiftOpen.closure_of_continuousOn hτ.continuousOn
  exact Analysis.inverseChart_periodic_of_chart_periodic_on hb.2.1
    (fun _ hq => hshift hq) hb.2.2.1 hb.2.2.2.1
    (fun _ hq => (n05_canonical_closed_periodicity h04 hz hs m hq).1) hp

/-- Reflection also passes to the actual closed inverse without a physical
radial-strip assumption. -/
theorem n05_canonical_closed_inverse_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalClosed S K m) :
    K.inverseChart z m (p.1, -p.2) =
      ((K.inverseChart z m p).1, -(K.inverseChart z m p).2) := by
  have hb := h04.1.boundary z hz hs m
  have hτ : Continuous (fun q : PolarPoint => (q.1, -q.2)) :=
    continuous_fst.prodMk continuous_snd.neg
  have hreflectOpen : MapsTo (fun q : PolarPoint => (q.1, -q.2))
      (physicalPieceOpen S K z m) (physicalPieceOpen S K z m) := by
    intro q hq
    exact ((h04.1.domains z hz hs m).2.2.2.2.1 q).mpr hq
  have hreflect : MapsTo (fun q : PolarPoint => (q.1, -q.2))
      (physicalPieceClosed S K z m) (physicalPieceClosed S K z m) :=
    hreflectOpen.closure_of_continuousOn hτ.continuousOn
  have hx := hb.2.1 hp
  have he := (n05_canonical_closed_reflection h04 hz hs m hx).1
  rw [hb.2.2.2.1 p hp] at he
  calc
    K.inverseChart z m (p.1, -p.2) = K.inverseChart z m
        (K.chart z m ((K.inverseChart z m p).1, -(K.inverseChart z m p).2)) :=
      congrArg (K.inverseChart z m) he.symm
    _ = _ := hb.2.2.1 _ (hreflect hx)

/-- The angular open strip is detected on the fixed closed canonical
cylinder, whose inverse image may be a curved physical domain. -/
theorem n05_canonical_closed_inverse_angle_mem_Ioo_iff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalClosed S K m) :
    (K.inverseChart z m p).2 ∈ Ioo (0 : ℝ) Real.pi ↔ p.2 ∈ Ioo (0 : ℝ) Real.pi := by
  apply Analysis.chart_angle_mem_openInterval_iff Real.pi_pos
    (n05_canonical_closed_inverse_injOn h04 hz hs m) ?_
    (fun _ hq => n05_canonical_closed_inverse_periodicity h04 hz hs m hq)
    (fun _ hq => n05_canonical_closed_inverse_reflection h04 hz hs m hq) hp
  intro q hq
  exact (Analysis.n04b_inverseChart_contDiffAt_closed h04.1 hz hs m hq).continuousAt.continuousWithinAt

/-- Both angular boundary fibers are fixed, so the same inverse also
preserves and detects the closed half-period interval. -/
theorem n05_canonical_closed_inverse_angle_mem_Icc_iff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalClosed S K m) :
    (K.inverseChart z m p).2 ∈ Icc (0 : ℝ) Real.pi ↔ p.2 ∈ Icc (0 : ℝ) Real.pi := by
  have hzero (q : PolarPoint) (hq : q ∈ canonicalClosed S K m) :
      (K.inverseChart z m q).2 = 0 ↔ q.2 = 0 := by
    constructor
    · exact Analysis.chart_angle_eq_zero_of_reflection
        (n05_canonical_closed_inverse_injOn h04 hz hs m)
        (fun _ hr => n05_canonical_closed_inverse_reflection h04 hz hs m hr) hq
    · intro hqzero
      have he := congrArg Prod.snd
        (n05_canonical_closed_inverse_reflection h04 hz hs m hq)
      have hqreflect : (q.1, -q.2) = q := by
        apply Prod.ext
        · rfl
        · simp only [hqzero, neg_zero]
      rw [hqreflect] at he
      change (K.inverseChart z m q).2 = -(K.inverseChart z m q).2 at he
      linarith only [he]
  have hpminus : p - (0, Real.pi) ∈ canonicalClosed S K m := by
    refine ⟨?_, mem_univ _⟩
    simpa only [Prod.fst_sub, sub_zero] using hp.1
  have htranslate : (K.inverseChart z m p).2 =
      (K.inverseChart z m (p - (0, Real.pi))).2 + Real.pi := by
    have he := congrArg Prod.snd
      (n05_canonical_closed_inverse_periodicity h04 hz hs m hpminus)
    simpa only [sub_add_cancel, Prod.snd_add] using he
  have hpi : (K.inverseChart z m p).2 = Real.pi ↔ p.2 = Real.pi := by
    constructor
    · intro he
      have hqzero := (hzero _ hpminus).mp (by linarith only [htranslate, he])
      change p.2 - Real.pi = 0 at hqzero
      linarith only [hqzero]
    · intro he
      have hqzero := (hzero _ hpminus).mpr (by
        change p.2 - Real.pi = 0
        rw [he, sub_self])
      linarith only [htranslate, hqzero]
  have hopen := n05_canonical_closed_inverse_angle_mem_Ioo_iff h04 hz hs m hp
  constructor
  · intro hangle
    by_cases hz0 : (K.inverseChart z m p).2 = 0
    · rw [(hzero p hp).mp hz0]
      exact ⟨le_rfl, Real.pi_pos.le⟩
    by_cases hzpi : (K.inverseChart z m p).2 = Real.pi
    · rw [hpi.mp hzpi]
      exact ⟨Real.pi_pos.le, le_rfl⟩
    exact mem_Icc_of_Ioo (hopen.mp
      ⟨lt_of_le_of_ne hangle.1 hz0.symm, lt_of_le_of_ne hangle.2 hzpi⟩)
  · intro hangle
    by_cases hz0 : p.2 = 0
    · rw [(hzero p hp).mpr hz0]
      exact ⟨le_rfl, Real.pi_pos.le⟩
    by_cases hzpi : p.2 = Real.pi
    · rw [hpi.mpr hzpi]
      exact ⟨Real.pi_pos.le, le_rfl⟩
    exact mem_Icc_of_Ioo (hopen.mpr
      ⟨lt_of_le_of_ne hangle.1 hz0.symm, lt_of_le_of_ne hangle.2 hzpi⟩)

/-- The forward chart detects the same closed angular interval on its
actual closed physical domain. -/
theorem n05_canonical_closed_chart_angle_mem_Icc_iff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K z m) :
    (K.chart z m p).2 ∈ Icc (0 : ℝ) Real.pi ↔ p.2 ∈ Icc (0 : ℝ) Real.pi := by
  have hb := h04.1.boundary z hz hs m
  have he := n05_canonical_closed_inverse_angle_mem_Icc_iff h04 hz hs m (hb.1 hp)
  rw [hb.2.2.1 p hp] at he
  exact he.symm

/-- The closed angular tiles correspond under the actual maps, including
their genuine physical boundary traces. -/
theorem n05_canonicalChart_closedAngular_maps
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    MapsTo (K.chart z m)
      (physicalPieceClosed S K z m ∩ (univ ×ˢ Icc (0 : ℝ) Real.pi))
      (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) ∧
    MapsTo (K.inverseChart z m)
      (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi)
      (physicalPieceClosed S K z m ∩ (univ ×ˢ Icc (0 : ℝ) Real.pi)) := by
  have hb := h04.1.boundary z hz hs m
  constructor
  · intro p hp
    exact ⟨(hb.1 hp.1).1,
      (n05_canonical_closed_chart_angle_mem_Icc_iff h04 hz hs m hp.1).mpr hp.2.2⟩
  · intro p hp
    have hpclosed : p ∈ canonicalClosed S K m := ⟨hp.1, mem_univ _⟩
    exact ⟨hb.2.1 hpclosed, mem_univ _,
      (n05_canonical_closed_inverse_angle_mem_Icc_iff h04 hz hs m hpclosed).mpr hp.2⟩

end ContinuousFlexibility.Statements
