module

public import ContinuousFlexibility.Analysis.N06NuSpatialDifference
public import ContinuousFlexibility.Analysis.N06NuPhysicalRegularity
public import ContinuousFlexibility.Analysis.N06SourceSpatialTransport
public import ContinuousFlexibility.Analysis.N06FiniteSourceNormalization

/-!
# Actual current nu source jets from primitive spatial geometry

The reference nu column is already fixed by the original N04
normalization clause. Its current-reference source difference is
therefore the current chart applied to the physical difference
nu_z - nu_ref. The latter has a proved order n+4 state-seminorm bound in
all physical spatial derivatives. The only remaining input below is a
uniform bound for actual forward-chart weight and adjugate spatial jets
on the fixed chi support. It is stated explicitly and is not claimed as
a consequence of N04's separate, fixed-state smoothness assertions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology

theorem n06PhysicalSourceAngularJet_zero_of_germ
    (F : PolarPoint → PolarPoint) (H : PolarPoint → ℝ)
    {f : PolarPoint → ℝ} {x : PolarPoint}
    (hf : f =ᶠ[𝓝 x] (fun _ => 0)) (j : ℕ) :
    n06PhysicalSourceAngularJet F H f j =ᶠ[𝓝 x] (fun _ => 0) := by
  induction j with
  | zero =>
    filter_upwards [hf] with y hy
    simp only [n06PhysicalSourceAngularJet, hy, mul_zero, zero_div]
  | succ j ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    change fderiv ℝ (n06PhysicalSourceAngularJet F H f j) y
      (n06InverseChartVector F (0, 1) y) = 0
    rw [hy]
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n06_canonicalNuDifference_eq_currentDifference
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (nuColumnField D S C z) p -
      canonicalSource S K (C.referenceState, 0) m
        (nuColumnField D S C (C.referenceState, 0)) p =
      canonicalSource S K z m (fun q => nuColumnField D S C z q -
        nuColumnField D S C (C.referenceState, 0) q) p := by
  have hb : RadialTrueBorder D := h01.1.2.2.2.1
  have hgeom : RadialProfileGeometry D := h01.1.1.choose_spec.1
  have hx := (h04.1.charts z hz hs m).2.1 hp
  have hxD := ((h04.1.domains z hz hs m).2.2.1 hx).1
  have hν := n06_nuColumn_reference
    (p := K.inverseChart z m p) hgeom.2.2.1.1 hb.1 hgeom.2.2.2.1.1 h01.2.2.1
    (hgeom.1.trans hxD.1).ne'
  have he := n06_canonicalNuDifference_eq_physicalDifference h04 h01.1.1 hb h01.2.2.1
    (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1) hz hs m hp
  refine he.trans ?_
  dsimp only [canonicalSource]
  rw [hν]
  rfl

theorem n06_currentNuDifference_angularJet_eq_physical
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m j : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    mixedDerivative 0 j (fun q => canonicalSource S K z m (nuColumnField D S C z) q -
      canonicalSource S K (C.referenceState, 0) m
        (nuColumnField D S C (C.referenceState, 0)) q) p =
      n06PhysicalSourceAngularJet (K.chart z m) (K.height z m)
        (fun q => nuColumnField D S C z q - nuColumnField D S C (C.referenceState, 0) q)
        j (K.inverseChart z m p) := by
  have he : (fun θ => canonicalSource S K z m (nuColumnField D S C z) (p.1, θ) -
      canonicalSource S K (C.referenceState, 0) m
        (nuColumnField D S C (C.referenceState, 0)) (p.1, θ)) =
      (fun θ => canonicalSource S K z m (fun q => nuColumnField D S C z q -
        nuColumnField D S C (C.referenceState, 0) q) (p.1, θ)) := by
    funext θ
    exact n06_canonicalNuDifference_eq_currentDifference h01 h04 hz hs m ⟨hp.1, mem_univ _⟩
  have hf := (n06_nuColumn_contDiff hT hS h01 hz hs).sub
    (n06_nuColumn_contDiff hT hS h01
      (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1))
  exact (congrArg (fun f : ℝ → ℝ => iteratedDeriv j f p.2) he).trans
    (n06_current_canonicalSource_angularJet h04 hz hs hf m j hp)

/-- A primitive geometric interface only on the common compact radial
support. Its bound is uniform before z and m. Actual forward-chart and
height jets and a Jacobian lower bound can supply it; it is not a source
norm or an assumption of the desired relative operator estimate. -/
def N06CurrentNuSpatialGeometryBound (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) (n : ℕ) (B : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
    z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ m x, x ∈ physicalPieceOpen S K z m → x.1 ∈ tsupport D.chi →
    ∀ k, k ≤ n →
      ‖iteratedFDeriv ℝ k
        (fun y => K.height z m y / |planeJacobian (K.chart z m) y|) x‖ ≤ B ∧
      ‖iteratedFDeriv ℝ k (n06InverseChartVector (K.chart z m) (0, 1)) x‖ ≤ B

def N06CurrentNuAngularDifferenceBound (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) (n : ℕ) (Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
    z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ m j, j ≤ n → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 j (fun q => canonicalSource S K z m (nuColumnField D S C z) q -
        canonicalSource S K (C.referenceState, 0) m
          (nuColumnField D S C (C.referenceState, 0)) q) p| ≤
        Q * (stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2|)

/-- The actual current source difference is uniformly small once the
displayed primitive geometric spatial jets are supplied. The physical
source smallness itself is proved from the original N01/state data. -/
theorem n06_currentNuDifference_angularJets_bound_of_spatial_geometry
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hgeometry : N06CurrentNuSpatialGeometryBound D S C K base ε n B) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06CurrentNuAngularDifferenceBound D S C K base ε n Q := by
  obtain ⟨Q, hQ, hphysical⟩ := n06_nuColumn_spatialDifference_bound hT hS h01 n
  have hcost := n06SpatialSourceTransportCost_nonneg n hB
  refine ⟨n06SpatialSourceTransportCost n B * Q, mul_nonneg hcost hQ, ?_⟩
  intro z hz hs hsmall m j hj p hp
  let f : PolarPoint → ℝ := fun q => nuColumnField D S C z q -
    nuColumnField D S C (C.referenceState, 0) q
  let x : PolarPoint := K.inverseChart z m p
  let δ : ℝ := stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2|
  have hδ : 0 ≤ δ := add_nonneg (apply_nonneg _ _) (abs_nonneg _)
  have hc := h04.1.charts z hz hs m
  have hd := h04.1.domains z hz hs m
  have hx : x ∈ physicalPieceOpen S K z m := hc.2.1 hp
  have hxp : x ∈ annularOpen D := hd.2.2.1 hx
  have hid := n06_currentNuDifference_angularJet_eq_physical hT hS h01 h04 hz hs m j hp
  by_cases hborder : x.1 ∈ tsupport D.chi
  · have hF : ContDiffOn ℝ ∞ (K.chart z m) (physicalPieceOpen S K z m) :=
      hc.2.2.2.2.1
    have hH : ContDiffOn ℝ ∞ (K.height z m) (physicalPieceOpen S K z m) :=
      hc.2.2.2.2.2.2.1
    have hJ : ∀ y ∈ physicalPieceOpen S K z m, planeJacobian (K.chart z m) y ≠ 0 :=
      fun y hy => (hc.2.2.2.2.2.2.2 y hy).2.1
    have hf : ContDiff ℝ ∞ f :=
      (n06_nuColumn_contDiff hT hS h01 hz hs).sub
        (n06_nuColumn_contDiff hT hS h01
          (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1))
    have hg := hgeometry z hz hs hsmall m x hx hborder
    have h := n06PhysicalSourceAngularJet_spatial_bound hd.1
      hF hH hJ hf.contDiffOn n hx hB (mul_nonneg hQ hδ)
      (fun k hk => (hg k hk).1) (fun k hk => (hg k hk).2)
      (fun k hk => hphysical z hz hs hsmall k hk x hxp) j hj
    exact (congrArg abs hid).trans_le
      (h.trans_eq (mul_assoc (n06SpatialSourceTransportCost n B) Q δ).symm)
  · have hb : RadialTrueBorder D := h01.1.2.2.2.1
    have hzfield : f =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(hb.2.1.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hborder]
        with y hy
      change nuColumnField D S C z y - nuColumnField D S C (C.referenceState, 0) y = 0
      rw [n06_nuColumn_zero_off_tsupport hT hS h01 z hy,
        n06_nuColumn_zero_off_tsupport hT hS h01 (C.referenceState, 0) hy, sub_self]
    have hzjet := (n06PhysicalSourceAngularJet_zero_of_germ
      (K.chart z m) (K.height z m) hzfield j).eq_of_nhds
    have hzero := (congrArg abs hid).trans (by rw [hzjet, abs_zero])
    exact hzero.trans_le (mul_nonneg (mul_nonneg hcost hQ) hδ)

end ContinuousFlexibility.Statements
