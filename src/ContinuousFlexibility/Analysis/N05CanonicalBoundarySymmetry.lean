import ContinuousFlexibility.Analysis.N05ReferenceSymbolClosure
import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess

/-!
# Period and reflection identities on the actual closed canonical pieces

The current-state identities extend from the actual open physical domain to
its closure. The fixed radial interval is used only after specialization to
the reference state through the stored `referenceDomain` identity.
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
  obtain ⟨_, _, _, _, _, _, _, hperiodic⟩ := h04.1.charts z hz hs m
  have hclosed := (h04.1.boundary z hz hs m).2.2.2.2.1
  have hshiftOpen : MapsTo (fun q : PolarPoint => q + (0, Real.pi))
      (physicalPieceOpen S K z m) (physicalPieceOpen S K z m) :=
    fun q hq => ((h04.1.domains z hz hs m).2.2.2.1 q).mpr hq
  have hshiftClosed := hshiftOpen.closure (continuous_id.add continuous_const)
  change p ∈ closure (physicalPieceOpen S K z m) at hp
  constructor
  · have heq : EqOn (fun q => K.chart z m (q + (0, Real.pi)))
        (fun q => K.chart z m q + (0, Real.pi)) (physicalPieceOpen S K z m) :=
      fun q hq => (hperiodic q hq).2.2.1
    refine heq.of_subset_closure ?_ ?_ subset_closure Subset.rfl hp
    · intro q hq
      exact ((hclosed (q + (0, Real.pi)) (hshiftClosed hq)).1.continuousAt.comp
        (f := fun r : PolarPoint => r + (0, Real.pi))
        (continuousAt_id.add continuousAt_const)).continuousWithinAt
    · intro q hq
      exact ((hclosed q hq).1.continuousAt.add continuousAt_const).continuousWithinAt
  · have heq : EqOn (fun q => K.height z m (q + (0, Real.pi)))
        (K.height z m) (physicalPieceOpen S K z m) :=
      fun q hq => (hperiodic q hq).2.2.2
    refine heq.of_subset_closure ?_ ?_ subset_closure Subset.rfl hp
    · intro q hq
      exact ((hclosed (q + (0, Real.pi)) (hshiftClosed hq)).2.1.continuousAt.comp
        (f := fun r : PolarPoint => r + (0, Real.pi))
        (continuousAt_id.add continuousAt_const)).continuousWithinAt
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
  have hreflection := h04.1.reflection z hz hs m
  have hclosed := (h04.1.boundary z hz hs m).2.2.2.2.1
  have hreflectionOpen : MapsTo (fun q : PolarPoint => (q.1, -q.2))
      (physicalPieceOpen S K z m) (physicalPieceOpen S K z m) :=
    fun q hq => ((h04.1.domains z hz hs m).2.2.2.2.1 q).mpr hq
  have hreflectionClosed := hreflectionOpen.closure
    (continuous_fst.prodMk continuous_snd.neg)
  change p ∈ closure (physicalPieceOpen S K z m) at hp
  constructor
  · have heq : EqOn (fun q => K.chart z m (q.1, -q.2))
        (fun q => ((K.chart z m q).1, -(K.chart z m q).2))
        (physicalPieceOpen S K z m) := fun q hq => (hreflection q hq).1
    refine heq.of_subset_closure ?_ ?_ subset_closure Subset.rfl hp
    · intro q hq
      exact ((hclosed (q.1, -q.2) (hreflectionClosed hq)).1.continuousAt.comp
        (f := fun r : PolarPoint => (r.1, -r.2))
        (continuousAt_fst.prodMk continuousAt_snd.neg)).continuousWithinAt
    · intro q hq
      have hqChart := (hclosed q hq).1.continuousAt
      exact (hqChart.fst.prodMk hqChart.snd.neg).continuousWithinAt
  · have heq : EqOn (fun q => K.height z m (q.1, -q.2))
        (K.height z m) (physicalPieceOpen S K z m) :=
      fun q hq => (hreflection q hq).2.1
    refine heq.of_subset_closure ?_ ?_ subset_closure Subset.rfl hp
    · intro q hq
      exact ((hclosed (q.1, -q.2) (hreflectionClosed hq)).2.1.continuousAt.comp
        (f := fun r : PolarPoint => (r.1, -r.2))
        (continuousAt_fst.prodMk continuousAt_snd.neg)).continuousWithinAt
    · intro q hq
      exact (hclosed q hq).2.1.continuousAt.continuousWithinAt

/-- At the reference state the actual closed domain is the stored rectangle. -/
theorem n05_reference_closed_periodicity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    K.chart (C.referenceState, 0) m (p + (0, Real.pi)) =
        K.chart (C.referenceState, 0) m p + (0, Real.pi) ∧
      K.height (C.referenceState, 0) m (p + (0, Real.pi)) =
        K.height (C.referenceState, 0) m p := by
  have hp' : p ∈ physicalPieceClosed S K (C.referenceState, 0) m := by
    rw [n05_reference_physicalClosed_eq h04 m]
    exact ⟨hp, mem_univ _⟩
  exact n05_canonical_closed_periodicity h04 hz hs m hp'

theorem n05_reference_closed_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    K.chart (C.referenceState, 0) m (p.1, -p.2) =
        ((K.chart (C.referenceState, 0) m p).1,
          -(K.chart (C.referenceState, 0) m p).2) ∧
      K.height (C.referenceState, 0) m (p.1, -p.2) =
        K.height (C.referenceState, 0) m p := by
  have hp' : p ∈ physicalPieceClosed S K (C.referenceState, 0) m := by
    rw [n05_reference_physicalClosed_eq h04 m]
    exact ⟨hp, mem_univ _⟩
  exact n05_canonical_closed_reflection h04 hz hs m hp'

end ContinuousFlexibility.Statements
