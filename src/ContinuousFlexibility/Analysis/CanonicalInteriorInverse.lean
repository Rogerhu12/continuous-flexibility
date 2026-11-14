module

public import ContinuousFlexibility.Analysis.CanonicalEndpointInverse
public import ContinuousFlexibility.Analysis.CanonicalBoundaryImage
public import ContinuousFlexibility.Analysis.N04bBoundaryInverseRegularity
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Convex.Topology

/-!
# Agreement of genuine local inverses on the canonical interior

The generic rectangular lemmas use connectedness and endpoint avoidance
to determine the physical side of a local inverse. For the actual current
physical domain, the closed inverse contract already gives continuity and
the exact inverse value. These identify the local inverse on a nearby
canonical interior without imposing a rectangular shape on the domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem mapsTo_Ioo_of_preconnected_avoids_endpoints
    {X : Type*} [TopologicalSpace X] {W : Set X} (hW : IsPreconnected W)
    {g : X → ℝ} (hg : ContinuousOn g W) {a b : ℝ}
    (hstart : ∃ x ∈ W, g x ∈ Ioo a b)
    (havoid : ∀ x ∈ W, g x ≠ a ∧ g x ≠ b) :
    MapsTo g W (Ioo a b) := by
  obtain ⟨x, hx, hxab⟩ := hstart
  intro y hy
  constructor
  · by_contra h
    obtain ⟨z, hz, hgz⟩ :=
      hW.intermediate_value hy hx hg ⟨le_of_not_gt h, hxab.1.le⟩
    exact (havoid z hz).1 hgz
  · by_contra h
    obtain ⟨z, hz, hgz⟩ :=
      hW.intermediate_value hx hy hg ⟨hxab.2.le, le_of_not_gt h⟩
    exact (havoid z hz).2 hgz

/-- A local inverse takes a whole nearby canonical interior into the
physical open strip. Endpoint avoidance determines the side by continuity,
using one physical interior point arbitrarily close to the endpoint. -/
theorem exists_localInverse_mapsTo_openStrip
    {a b α β : ℝ} (hab : a < b) {F : PolarPoint → PolarPoint}
    (hmap : MapsTo F (Ioo a b ×ˢ (univ : Set ℝ))
      (Ioo α β ×ˢ (univ : Set ℝ)))
    (hboundary : ∀ x : PolarPoint, x.1 = a ∨ x.1 = b →
      (F x).1 ∉ Ioo α β)
    (e : OpenPartialHomeomorph PolarPoint PolarPoint)
    (heF : (e : PolarPoint → PolarPoint) = F)
    {p : PolarPoint} (hpe : p ∈ e.source) (hp : p.1 ∈ Icc a b) :
    ∃ δ > 0, Metric.ball (F p) δ ⊆ e.target ∧
      MapsTo e.symm
        (Metric.ball (F p) δ ∩ (Ioo α β ×ˢ (univ : Set ℝ)))
        (Ioo a b ×ˢ (univ : Set ℝ)) := by
  have hFp : F p ∈ e.target := by
    rw [← heF]
    exact e.map_source hpe
  obtain ⟨δ, hδ, htarget⟩ :=
    Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hFp)
  let W : Set PolarPoint :=
    Metric.ball (F p) δ ∩ (Ioo α β ×ˢ (univ : Set ℝ))
  have hWtarget : W ⊆ e.target := fun _ hq => htarget hq.1
  have hW : IsPreconnected W :=
    ((convex_ball (F p) δ).inter
      ((convex_Ioo α β).prod (convex_univ : Convex ℝ (univ : Set ℝ)))).isPreconnected
  have hcont : ContinuousOn (fun q : PolarPoint => (e.symm q).1) W :=
    (e.symm.continuousOn.mono hWtarget).fst
  have hpcl : p ∈ closure (Ioo a b ×ˢ (univ : Set ℝ)) := by
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_univ]
    exact ⟨hp, mem_univ _⟩
  haveI : NeBot (𝓝[Ioo a b ×ˢ (univ : Set ℝ)] p) :=
    mem_closure_iff_nhdsWithin_neBot.mp hpcl
  have hFcont : ContinuousAt F p := by
    rw [← heF]
    exact e.continuousAt hpe
  have hnear : ∀ᶠ x in 𝓝 p, x ∈ e.source ∧ F x ∈ Metric.ball (F p) δ :=
    Filter.Eventually.and (e.open_source.mem_nhds hpe)
      (hFcont.eventually (Metric.ball_mem_nhds (F p) hδ))
  obtain ⟨x, hx, hxe, hxball⟩ :=
    Filter.Eventually.exists (Filter.Eventually.and (self_mem_nhdsWithin :
      ∀ᶠ x in 𝓝[Ioo a b ×ˢ (univ : Set ℝ)] p,
        x ∈ Ioo a b ×ˢ (univ : Set ℝ))
      (hnear.filter_mono nhdsWithin_le_nhds))
  have hstart : ∃ q ∈ W, (e.symm q).1 ∈ Ioo a b := by
    refine ⟨F x, ⟨hxball, hmap hx⟩, ?_⟩
    have hinv : e.symm (F x) = x := by
      rw [← heF]
      exact e.left_inv hxe
    rw [hinv]
    exact hx.1
  have havoid : ∀ q ∈ W, (e.symm q).1 ≠ a ∧ (e.symm q).1 ≠ b := by
    intro q hq
    apply not_or.mp
    intro hedge
    have hinv : F (e.symm q) = q := by
      rw [← heF]
      exact e.right_inv (hWtarget hq)
    apply hboundary (e.symm q) hedge
    rw [hinv]
    exact hq.2.1
  have hinside := mapsTo_Ioo_of_preconnected_avoids_endpoints hW hcont hstart havoid
  exact ⟨δ, hδ, htarget, fun q hq => ⟨hinside hq, mem_univ _⟩⟩

/-- Every right inverse with values in the physical interior agrees with
the local inverse throughout a nearby canonical interior. -/
theorem exists_rightInverse_eq_localInverse_on_openStrip
    {a b α β : ℝ} (hab : a < b) {F G : PolarPoint → PolarPoint}
    (hmap : MapsTo F (Ioo a b ×ˢ (univ : Set ℝ))
      (Ioo α β ×ˢ (univ : Set ℝ)))
    (hboundary : ∀ x : PolarPoint, x.1 = a ∨ x.1 = b →
      (F x).1 ∉ Ioo α β)
    (hinj : InjOn F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hG : MapsTo G (Ioo α β ×ˢ (univ : Set ℝ))
      (Ioo a b ×ˢ (univ : Set ℝ)))
    (hright : ∀ q ∈ Ioo α β ×ˢ (univ : Set ℝ), F (G q) = q)
    (e : OpenPartialHomeomorph PolarPoint PolarPoint)
    (heF : (e : PolarPoint → PolarPoint) = F)
    {p : PolarPoint} (hpe : p ∈ e.source) (hp : p.1 ∈ Icc a b) :
    ∃ δ > 0, Metric.ball (F p) δ ⊆ e.target ∧
      MapsTo e.symm
        (Metric.ball (F p) δ ∩ (Ioo α β ×ˢ (univ : Set ℝ)))
        (Ioo a b ×ˢ (univ : Set ℝ)) ∧
      EqOn G e.symm
        (Metric.ball (F p) δ ∩ (Ioo α β ×ˢ (univ : Set ℝ))) := by
  obtain ⟨δ, hδ, htarget, hlocal⟩ :=
    exists_localInverse_mapsTo_openStrip hab hmap hboundary e heF hpe hp
  refine ⟨δ, hδ, htarget, hlocal, ?_⟩
  intro q hq
  apply hinj (hG hq.2) (hlocal hq)
  calc
    F (G q) = q := hright q hq.2
    _ = F (e.symm q) := by
      rw [← heF]
      exact (e.right_inv (htarget hq.1)).symm

/-- In particular the actual chosen `invFunOn` has this interior agreement;
no boundary value of `invFunOn` is used. -/
theorem exists_invFunOn_eq_localInverse_on_openStrip
    {a b α β : ℝ} (hab : a < b) {F : PolarPoint → PolarPoint}
    (hbij : BijOn F (Ioo a b ×ˢ (univ : Set ℝ))
      (Ioo α β ×ˢ (univ : Set ℝ)))
    (hboundary : ∀ x : PolarPoint, x.1 = a ∨ x.1 = b →
      (F x).1 ∉ Ioo α β)
    (e : OpenPartialHomeomorph PolarPoint PolarPoint)
    (heF : (e : PolarPoint → PolarPoint) = F)
    {p : PolarPoint} (hpe : p ∈ e.source) (hp : p.1 ∈ Icc a b) :
    ∃ δ > 0, Metric.ball (F p) δ ⊆ e.target ∧
      MapsTo e.symm
        (Metric.ball (F p) δ ∩ (Ioo α β ×ˢ (univ : Set ℝ)))
        (Ioo a b ×ˢ (univ : Set ℝ)) ∧
      EqOn (Function.invFunOn F (Ioo a b ×ˢ (univ : Set ℝ))) e.symm
        (Metric.ball (F p) δ ∩ (Ioo α β ×ˢ (univ : Set ℝ))) :=
  exists_rightInverse_eq_localInverse_on_openStrip hab hbij.mapsTo hboundary hbij.injOn
    hbij.surjOn.mapsTo_invFunOn hbij.surjOn.rightInvOn_invFunOn e heF hpe hp

/-- Continuity and the true base inverse value identify a local inverse
on a nearby target interior for arbitrary physical and target domains. -/
theorem exists_rightInverse_eq_localInverse_on_openDomain
    {U V : Set PolarPoint} {F G : PolarPoint → PolarPoint}
    (hmapG : MapsTo G V U) (hright : ∀ q ∈ V, F (G q) = q)
    (e : OpenPartialHomeomorph PolarPoint PolarPoint)
    (heF : (e : PolarPoint → PolarPoint) = F)
    {p : PolarPoint} (hpe : p ∈ e.source)
    (hG : ContinuousAt G (F p)) (hGF : G (F p) = p) :
    ∃ δ > 0, Metric.ball (F p) δ ⊆ e.target ∧
      MapsTo e.symm (Metric.ball (F p) δ ∩ V) U ∧
      EqOn G e.symm (Metric.ball (F p) δ ∩ V) := by
  have hFp : F p ∈ e.target := by
    rw [← heF]
    exact e.map_source hpe
  have hGp : G (F p) ∈ e.source := by
    rw [hGF]
    exact hpe
  have hnear : e.target ∩ G ⁻¹' e.source ∈ 𝓝 (F p) :=
    inter_mem (e.open_target.mem_nhds hFp)
      (hG.eventually (e.open_source.mem_nhds hGp))
  obtain ⟨δ, hδ, hδset⟩ := Metric.mem_nhds_iff.mp hnear
  have heq : EqOn G e.symm (Metric.ball (F p) δ ∩ V) := by
    intro q hq
    have hqt := (hδset hq.1).1
    apply e.injOn (hδset hq.1).2 (e.map_target hqt)
    calc
      e (G q) = F (G q) := congrFun heF (G q)
      _ = q := hright q hq.2
      _ = e (e.symm q) := (e.right_inv hqt).symm
  refine ⟨δ, hδ, fun q hq => (hδset hq).1, ?_, heq⟩
  intro q hq
  rw [← heq hq]
  exact hmapG hq.2

/-- At every point of the actual physical closure the stored inverse
agrees with a genuine smooth local inverse on a whole nearby canonical
interior. Closed inverse regularity comes from the boundary-germ contract. -/
theorem canonicalChart_exists_smooth_interiorInverse
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (p : PolarPoint)
    (hp : p ∈ physicalPieceClosed S K z m) :
    ∃ (e : OpenPartialHomeomorph PolarPoint PolarPoint) (δ : ℝ),
      (e : PolarPoint → PolarPoint) = K.chart z m ∧ p ∈ e.source ∧
      ContDiffAt ℝ ∞ e.symm (K.chart z m p) ∧ 0 < δ ∧
      Metric.ball (K.chart z m p) δ ⊆ e.target ∧
      MapsTo e.symm (Metric.ball (K.chart z m p) δ ∩ canonicalOpen S K m)
        (physicalPieceOpen S K z m) ∧
      EqOn (K.inverseChart z m) e.symm
        (Metric.ball (K.chart z m p) δ ∩ canonicalOpen S K m) := by
  have hcharts := hK.charts z hz hsector m
  have hclosed := hK.boundary z hz hsector m
  obtain ⟨e, heF, hpe, hsmooth, _⟩ :=
    canonicalChart_exists_smooth_endpointInverse hK hz hsector m p hp
  have hG : ContinuousAt (K.inverseChart z m) (K.chart z m p) :=
    (n04b_inverseChart_contDiffAt_closed hK hz hsector m (hclosed.1 hp)).continuousAt
  obtain ⟨δ, hδ, htarget, hlocal, heq⟩ :=
    exists_rightInverse_eq_localInverse_on_openDomain hcharts.2.1 hcharts.2.2.2.1
      e heF hpe hG (hclosed.2.2.1 p hp)
  exact ⟨e, δ, heF, hpe, hsmooth, hδ, htarget, hlocal, heq⟩

end ContinuousFlexibility.Analysis
