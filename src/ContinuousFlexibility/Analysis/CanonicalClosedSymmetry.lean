import ContinuousFlexibility.Analysis.CanonicalBoundaryLift
import ContinuousFlexibility.Analysis.CanonicalStripGeometry
import ContinuousFlexibility.Analysis.N04bBoundaryInverseRegularity

/-!
# True inverse symmetry on the closed canonical rectangle

The stored inverse is smooth at every closed-strip point. Its interior
reflection and translation identities therefore hold at both ordinary
boundaries as well. Closed inverse identities give actual injectivity,
which identifies the two reflection-axis fibers without a radial-graph
assumption on the current physical boundary.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem inverse_eq_at_closure
    {U : Set PolarPoint} {F G : PolarPoint → PolarPoint} {p : PolarPoint}
    (hp : p ∈ closure U) (hF : ContinuousAt F p) (hG : ContinuousAt G p)
    (he : EqOn F G U) : F p = G p := by
  haveI : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hnear : F =ᶠ[𝓝[U] p] G := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact he hq
  exact tendsto_nhds_unique_of_eventuallyEq
    (hF.mono_left nhdsWithin_le_nhds) (hG.mono_left nhdsWithin_le_nhds) hnear

theorem canonicalClosed_mem_closure_open
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (hlen : K.left m < K.right m) {q : PolarPoint}
    (hq : q ∈ canonicalClosed S K m) : q ∈ closure (canonicalOpen S K m) := by
  simpa only [canonicalClosed, canonicalOpen, closure_prod_eq, closure_Ioo hlen.ne, closure_univ]
    using hq

theorem canonicalInverse_injOn_closed
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    InjOn (K.inverseChart z m) (canonicalClosed S K m) := by
  intro p hp q hq he
  have hclosed := hA.boundary z hz hs m
  calc
    p = K.chart z m (K.inverseChart z m p) := (hclosed.2.2.2.1 p hp).symm
    _ = K.chart z m (K.inverseChart z m q) := congrArg (K.chart z m) he
    _ = q := hclosed.2.2.2.1 q hq

theorem canonicalInverse_reflection_on_closed
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {q : PolarPoint}
    (hq : q ∈ canonicalClosed S K m) :
    K.inverseChart z m (q.1, -q.2) =
      ((K.inverseChart z m q).1, -(K.inverseChart z m q).2) := by
  have hr : (q.1, -q.2) ∈ canonicalClosed S K m := ⟨hq.1, mem_univ _⟩
  have hG := (n04b_inverseChart_contDiffAt_closed hA hz hs m hq).continuousAt
  have hGr := (n04b_inverseChart_contDiffAt_closed hA hz hs m hr).continuousAt
  have hreflect : ContinuousAt (fun p : PolarPoint => (p.1, -p.2)) q :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  exact inverse_eq_at_closure
    (canonicalClosed_mem_closure_open (hA.referenceBounds m).2.1 hq)
    (ContinuousAt.comp (f := fun p : PolarPoint => (p.1, -p.2)) (x := q) hGr hreflect)
    (hG.fst.prodMk hG.snd.neg)
    (fun p hp => hA.inverseReflection z hz hs m p hp)

theorem canonicalInverse_periodic_on_closed
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {q : PolarPoint}
    (hq : q ∈ canonicalClosed S K m) :
    K.inverseChart z m (q + (0, Real.pi)) = K.inverseChart z m q + (0, Real.pi) := by
  have hq' : q + (0, Real.pi) ∈ canonicalClosed S K m := by
    exact ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
  exact periodic_lift_at_closure
    (canonicalClosed_mem_closure_open (hA.referenceBounds m).2.1 hq)
    (n04b_inverseChart_contDiffAt_closed hA hz hs m hq).continuousAt
    (n04b_inverseChart_contDiffAt_closed hA hz hs m hq').continuousAt
    (fun p hp => canonicalInverse_periodic_on_open hA hz hs m hp)

theorem canonicalInverse_zero_axis_iff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {q : PolarPoint}
    (hq : q ∈ canonicalClosed S K m) :
    (K.inverseChart z m q).2 = 0 ↔ q.2 = 0 := by
  have he := canonicalInverse_reflection_on_closed hA hz hs m hq
  constructor
  · intro hzero
    have hmaps : K.inverseChart z m (q.1, -q.2) = K.inverseChart z m q := by
      rw [he]
      exact Prod.ext rfl (by rw [hzero, neg_zero])
    have hr : (q.1, -q.2) ∈ canonicalClosed S K m := ⟨hq.1, mem_univ _⟩
    have hqeq : (q.1, -q.2) = q :=
      canonicalInverse_injOn_closed hA hz hs m hr hq hmaps
    have hangle := congrArg Prod.snd hqeq
    change -q.2 = q.2 at hangle
    linarith only [hangle]
  · intro hzero
    have hqeq : (q.1, -q.2) = q := Prod.ext rfl (by rw [hzero, neg_zero])
    rw [hqeq] at he
    have hangle := congrArg Prod.snd he
    change (K.inverseChart z m q).2 = -(K.inverseChart z m q).2 at hangle
    linarith only [hangle]

theorem canonicalInverse_half_pi_axis_iff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {q : PolarPoint}
    (hq : q ∈ canonicalClosed S K m) :
    (K.inverseChart z m q).2 = Real.pi / 2 ↔ q.2 = Real.pi / 2 := by
  have hr : (q.1, -q.2) ∈ canonicalClosed S K m := ⟨hq.1, mem_univ _⟩
  have htr : (q.1, -q.2) + (0, Real.pi) ∈ canonicalClosed S K m := by
    exact ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
  have he := canonicalInverse_periodic_on_closed hA hz hs m hr
  rw [canonicalInverse_reflection_on_closed hA hz hs m hq] at he
  constructor
  · intro hang
    have hmaps : K.inverseChart z m ((q.1, -q.2) + (0, Real.pi)) =
        K.inverseChart z m q := by
      rw [he]
      apply Prod.ext
      · simp only [Prod.fst_add, add_zero]
      · simp only [Prod.snd_add]
        linarith only [hang]
    have hqeq := canonicalInverse_injOn_closed hA hz hs m htr hq hmaps
    have hangle := congrArg Prod.snd hqeq
    simp only [Prod.snd_add] at hangle
    linarith only [hangle]
  · intro hang
    have hqeq : (q.1, -q.2) + (0, Real.pi) = q := by
      apply Prod.ext
      · simp only [Prod.fst_add, add_zero]
      · simp only [Prod.snd_add]
        linarith only [hang]
    rw [hqeq] at he
    have hangle := congrArg Prod.snd he
    simp only [Prod.snd_add] at hangle
    linarith only [hangle]

end ContinuousFlexibility.Analysis
