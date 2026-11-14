module

public import ContinuousFlexibility.Analysis.N04bBoundaryInverseRegularity
public import ContinuousFlexibility.Analysis.CoordinatePrincipalDeterminant

/-!
# Actual inverse germs and derivatives on the closed canonical strip

The boundary contract supplies a genuine local inverse germ. The existing
closed-strip regularity theorem supplies the actual smoothness of the stored
inverse. Together they give both inverse identities on full neighborhoods,
and hence the ordinary derivative and Jacobian identities at boundary points.
Only pointwise smoothness is used; no common open smoothness collar is inferred.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A true boundary inverse germ supplies both actual inverse equations
near the physical and canonical base points. -/
theorem canonicalBoundaryInverseGerm_inverse_germs
    {F G : PolarPoint → PolarPoint} {p : PolarPoint}
    (h : CanonicalBoundaryInverseGerm F G p) :
    G ∘ F =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) ∧
      F ∘ G =ᶠ[𝓝 (F p)] (id : PolarPoint → PolarPoint) := by
  obtain ⟨e, he, hp, _, hG⟩ := h
  have hF : ContinuousAt F p := by
    rw [← he]
    exact e.continuousAt hp
  have htarget : F p ∈ e.target := by
    rw [← he]
    exact e.map_source hp
  constructor
  · filter_upwards [hG.comp_tendsto hF.tendsto, e.open_source.mem_nhds hp] with q hq hqe
    change G (F q) = q
    change G (F q) = e.symm (F q) at hq
    rw [hq, ← he]
    exact e.left_inv hqe
  · filter_upwards [hG, e.open_target.mem_nhds htarget] with q hq hqe
    change F (G q) = q
    rw [hq, ← he]
    exact e.right_inv hqe

/-- The stored chart and inverse satisfy true two-sided inverse germs
at every point of the closed canonical rectangle, also for curved current
physical domains. -/
theorem canonicalClosed_inverse_germs
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {q : PolarPoint}
    (hq : q ∈ canonicalClosed S K m) :
    K.inverseChart z m ∘ K.chart z m =ᶠ[𝓝 (K.inverseChart z m q)]
        (id : PolarPoint → PolarPoint) ∧
      K.chart z m ∘ K.inverseChart z m =ᶠ[𝓝 q]
        (id : PolarPoint → PolarPoint) := by
  have hcharts := hA.charts z hz hs m
  have hclosed := hA.boundary z hz hs m
  have hx : K.inverseChart z m q ∈ physicalPieceClosed S K z m :=
    hclosed.2.1 hq
  have hFx : K.chart z m (K.inverseChart z m q) = q :=
    hclosed.2.2.2.1 q hq
  by_cases hi : K.inverseChart z m q ∈ physicalPieceOpen S K z m
  · have hqopen : q ∈ canonicalOpen S K m := by
      rw [← hFx]
      exact hcharts.1 hi
    constructor
    · filter_upwards [(hA.domains z hz hs m).1.mem_nhds hi] with p hp
      exact hcharts.2.2.1 p hp
    · filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hqopen] with p hp
      exact hcharts.2.2.2.1 p hp
  · have hfront :
        K.inverseChart z m q ∈ frontier (physicalPieceOpen S K z m) := by
      rw [(hA.domains z hz hs m).1.frontier_eq]
      exact ⟨hx, hi⟩
    have hg := canonicalBoundaryInverseGerm_inverse_germs
      (hclosed.2.2.2.2.2 _ hfront)
    simpa only [hFx] using hg

/-- Both ordinary derivative compositions are identities. The stored
inverse derivative is identified through its genuine local inverse germ. -/
theorem canonicalClosed_inverse_fderiv
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {q : PolarPoint}
    (hq : q ∈ canonicalClosed S K m) :
    (fderiv ℝ (K.inverseChart z m) q).comp
        (fderiv ℝ (K.chart z m) (K.inverseChart z m q)) =
          ContinuousLinearMap.id ℝ PolarPoint ∧
      (fderiv ℝ (K.chart z m) (K.inverseChart z m q)).comp
        (fderiv ℝ (K.inverseChart z m) q) =
          ContinuousLinearMap.id ℝ PolarPoint := by
  have hclosed := hA.boundary z hz hs m
  have hx := hclosed.2.1 hq
  have hFx := hclosed.2.2.2.1 q hq
  have hF : DifferentiableAt ℝ (K.chart z m) (K.inverseChart z m q) :=
    (hclosed.2.2.2.2.1 _ hx).1.differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (K.inverseChart z m) q :=
    (n04b_inverseChart_contDiffAt_closed hA hz hs m hq).differentiableAt (by simp)
  have hG' : DifferentiableAt ℝ (K.inverseChart z m)
      (K.chart z m (K.inverseChart z m q)) := by
    simpa only [hFx] using hG
  have hg := canonicalClosed_inverse_germs hA hz hs m hq
  have hleft := hG'.hasFDerivAt.comp (K.inverseChart z m q) hF.hasFDerivAt
  have hright := hF.hasFDerivAt.comp q hG.hasFDerivAt
  constructor
  · simpa only [hFx] using
      (hleft.congr_of_eventuallyEq hg.1.symm).unique
        (hasFDerivAt_id (K.inverseChart z m q))
  · exact (hright.congr_of_eventuallyEq hg.2.symm).unique (hasFDerivAt_id q)

/-- The actual closed-strip inverse Jacobian is reciprocal to the forward
Jacobian, including ordinary boundary derivatives. -/
theorem canonicalClosed_inverse_planeJacobian
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {q : PolarPoint}
    (hq : q ∈ canonicalClosed S K m) :
    planeJacobian (K.inverseChart z m) q =
      (planeJacobian (K.chart z m) (K.inverseChart z m q))⁻¹ := by
  have hclosed := hA.boundary z hz hs m
  have hx := hclosed.2.1 hq
  have hregular := hclosed.2.2.2.2.1 _ hx
  have hF : DifferentiableAt ℝ (K.chart z m) (K.inverseChart z m q) :=
    hregular.1.differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (K.inverseChart z m) q :=
    (n04b_inverseChart_contDiffAt_closed hA hz hs m hq).differentiableAt (by simp)
  have hmul := planeJacobian_inverse_mul_of_germ hG hF
    (canonicalClosed_inverse_germs hA hz hs m hq).2
  have he : planeJacobian (K.inverseChart z m) q =
      1 / planeJacobian (K.chart z m) (K.inverseChart z m q) :=
    (eq_div_iff hregular.2.2.1).2 (by simpa only [mul_comm] using hmul)
  simpa only [one_div] using he

end ContinuousFlexibility.Analysis
