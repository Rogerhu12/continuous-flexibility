import ContinuousFlexibility.Analysis.N07aCanonicalRoughPairing
import Mathlib.Algebra.Field.Periodic
import Mathlib.Topology.Order.IntermediateValue

/-!
# The genuine forward chart at the boundary

Only the forward chart has prescribed smooth boundary values. Its open
periodicity extends to the closed physical strip by continuity. The
angular map on either boundary is then onto, so current and reference
boundary values can be compared without assigning a meaning to the
inverse candidate at a boundary point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n07a_strip_eqOn_closed {E : Type*} [TopologicalSpace E] [T2Space E]
    {a b : ℝ} (hab : a < b) {f g : PolarPoint → E}
    (he : EqOn f g (Ioo a b ×ˢ univ))
    (hf : ∀ p ∈ Icc a b ×ˢ univ, ContinuousAt f p)
    (hg : ∀ p ∈ Icc a b ×ˢ univ, ContinuousAt g p) :
    EqOn f g (Icc a b ×ˢ univ) := by
  apply he.of_subset_closure
    (fun p hp => (hf p hp).continuousWithinAt)
    (fun p hp => (hg p hp).continuousWithinAt)
  · intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩
  · rw [closure_prod_eq, closure_Ioo hab.ne, closure_univ]

theorem n07a_equivariant_angle_surjective {f : ℝ → ℝ}
    (hf : Continuous f) (hπ : ∀ θ, f (θ + Real.pi) = f θ + Real.pi) :
    Function.Surjective f := by
  let d : ℝ → ℝ := fun θ => f θ - θ
  have hd : Function.Periodic d Real.pi := by
    intro θ
    dsimp only [d]
    rw [hπ]
    ring
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn d (Icc 0 Real.pi) from (hf.sub continuous_id).continuousOn)
  have hb (θ : ℝ) : |f θ - θ| ≤ A := by
    obtain ⟨q, hq, he⟩ := hd.exists_mem_Ico₀ Real.pi_pos θ
    have h := hA q ⟨hq.1, hq.2.le⟩
    simpa only [Real.norm_eq_abs, ← he, d] using h
  intro y
  exact mem_range_of_exists_le_of_exists_ge hf
    ⟨y - A, by linarith [(abs_le.mp (hb (y - A))).2]⟩
    ⟨y + A, by linarith [(abs_le.mp (hb (y + A))).1]⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_chart_equivariance_closed
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) := by
  have hgeom := h04.2.2.2.2.2.2.2.1 z hz hs m
  have hclosed := h04.2.2.2.2.2.2.2.2.1 z hz hs m
  apply n07a_strip_eqOn_closed (h04.2.2.2.1 m).1
    (f := fun q => K.chart z m (q + (0, Real.pi)))
    (g := fun q => K.chart z m q + (0, Real.pi))
    (fun q hq => (hgeom.2.2.2.2.2.2.2 q hq).2.2.1) _ _ ⟨hp, mem_univ _⟩
  · intro q hq
    have hshift : (q + (0, Real.pi)).1 ∈
        Icc (K.physicalLeft m) (K.physicalRight m) := by
      simpa only [Prod.fst_add, add_zero] using hq.1
    exact (hclosed (q + (0, Real.pi)) hshift).1.continuousAt.comp
      (f := fun x : PolarPoint => x + (0, Real.pi)) (x := q)
      (continuousAt_id.add continuousAt_const)
  · intro q hq
    exact (hclosed q hq.1).1.continuousAt.add continuousAt_const

theorem n07a_height_periodic_closed
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    K.height z m (p + (0, Real.pi)) = K.height z m p := by
  have hgeom := h04.2.2.2.2.2.2.2.1 z hz hs m
  have hclosed := h04.2.2.2.2.2.2.2.2.1 z hz hs m
  apply n07a_strip_eqOn_closed (h04.2.2.2.1 m).1
    (f := fun q => K.height z m (q + (0, Real.pi)))
    (g := K.height z m)
    (fun q hq => (hgeom.2.2.2.2.2.2.2 q hq).2.2.2) _ _ ⟨hp, mem_univ _⟩
  · intro q hq
    have hshift : (q + (0, Real.pi)).1 ∈
        Icc (K.physicalLeft m) (K.physicalRight m) := by
      simpa only [Prod.fst_add, add_zero] using hq.1
    exact (hclosed (q + (0, Real.pi)) hshift).2.1.continuousAt.comp
      (f := fun x : PolarPoint => x + (0, Real.pi)) (x := q)
      (continuousAt_id.add continuousAt_const)
  · intro q hq
    exact (hclosed q hq.1).2.1.continuousAt

theorem n07a_boundary_chart_angle_surjective
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {c : ℝ}
    (hc : c ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    Function.Surjective (fun θ => (K.chart z m (c, θ)).2) := by
  apply n07a_equivariant_angle_surjective
  · apply continuous_iff_continuousAt.mpr
    intro θ
    exact ((h04.2.2.2.2.2.2.2.2.1 z hz hs m (c, θ) hc).1.continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).snd
  · intro θ
    have h := congrArg Prod.snd (n07a_chart_equivariance_closed h04 hz hs m
      (p := (c, θ)) hc)
    simpa only [Prod.mk_add_mk, zero_add, add_zero, Prod.snd_add] using h

theorem n07a_reference_chart_radial_closed
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceRadial S C K)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    K.chart (C.referenceState, 0) m p =
      ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2) := by
  have hclosed := h04.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) hz hs m
  apply n07a_strip_eqOn_closed (h04.2.2.2.1 m).1
    (f := K.chart (C.referenceState, 0) m)
    (g := fun q => ((K.chart (C.referenceState, 0) m (q.1, 0)).1, q.2))
    (fun q hq => (href.1 m q hq).1) _ _ ⟨hp, mem_univ _⟩
  · intro q hq
    exact (hclosed q hq.1).1.continuousAt
  · intro q hq
    exact (((hclosed (q.1, 0) hq.1).1.continuousAt.comp
      (f := fun x : PolarPoint => (x.1, 0)) (x := q)
      (continuousAt_fst.prodMk continuousAt_const)).fst).prodMk continuousAt_snd

end ContinuousFlexibility.Analysis
