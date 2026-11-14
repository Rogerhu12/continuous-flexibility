module

public import ContinuousFlexibility.Analysis.CanonicalRootTransportBoundary
public import ContinuousFlexibility.Analysis.CanonicalNegativeTravelSymmetries
public import ContinuousFlexibility.Analysis.N04bActualAtlasCuts

/-!
# Actual one-sided endpoint fields of the constructed atlas

The open-component formulas are the genuine common travel transition.
The ordinary root germs, inverse, Jacobian and height positivity come
from the constructed closed atlas. No derivative estimate or future
positive-component transport is an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

structure OneSidedTransportEndpoint
    (F : PolarPoint → PolarPoint) (q : PolarPoint → ℝ) (a b c : ℝ) : Prop where
  interval : a < b
  endpoint : c ∈ Icc a b
  smooth_on : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ (univ : Set ℝ))
  root_smooth : ∀ θ, ContDiffAt ℝ ∞ F (c, θ)
  root_radial : ∀ θ, (F (c, θ)).1 = c
  root_jacobian : ∀ θ, 0 < planeJacobian F (c, θ)
  root_diagonal : ∀ θ,
    0 < radialPartial (fun p => (F p).1) (c, θ) ∧
      0 < angularPartial (fun p => (F p).2) (c, θ)
  root_inverse : ∀ θ, ∃ G : PolarPoint → PolarPoint,
    ContDiffAt ℝ ∞ G (F (c, θ)) ∧
      G ∘ F =ᶠ[𝓝 (c, θ)] (id : PolarPoint → PolarPoint) ∧
      F ∘ G =ᶠ[𝓝 (F (c, θ))] (id : PolarPoint → PolarPoint)
  height_smooth_on : ContDiffOn ℝ ∞ q (Ioo a b ×ˢ (univ : Set ℝ))
  height_positive : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), 0 < q p
  height_root : ∀ θ, ContDiffAt ℝ ∞ q (c, θ) ∧ 0 < q (c, θ)
  period_add : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
    F (p + (0, Real.pi)) = F p + (0, Real.pi)
  reflect : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
    F (p.1, -p.2) = ((F p).1, -(F p).2)
  height_period : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), q (p + (0, Real.pi)) = q p
  height_even : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), q (p.1, -p.2) = q p

theorem oneSidedTransportEndpoint_identity {a b c : ℝ}
    (hab : a < b) (hc : c ∈ Icc a b) :
    OneSidedTransportEndpoint (id : PolarPoint → PolarPoint) (fun _ => 1) a b c := by
  refine {
    interval := hab
    endpoint := hc
    smooth_on := contDiff_id.contDiffOn
    root_smooth := fun _ => contDiff_id.contDiffAt
    root_radial := fun _ => rfl
    root_jacobian := ?_
    root_diagonal := ?_
    root_inverse := ?_
    height_smooth_on := contDiff_const.contDiffOn
    height_positive := fun _ _ => zero_lt_one
    height_root := fun _ => ⟨contDiff_const.contDiffAt, zero_lt_one⟩
    period_add := fun _ _ => rfl
    reflect := fun _ _ => rfl
    height_period := fun _ _ => rfl
    height_even := fun _ _ => rfl }
  · intro θ
    simp only [planeJacobian, fderiv_id, ContinuousLinearMap.id_apply,
      one_mul, zero_mul, sub_zero, zero_lt_one]
  · intro θ
    simpa only [id_eq, radialPartial_fst, angularPartial_snd] using
      And.intro (zero_lt_one : (0 : ℝ) < 1) (zero_lt_one : (0 : ℝ) < 1)
  · intro θ
    exact ⟨id, contDiff_id.contDiffAt, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩

/-- Both true inverse germs for the stored reference-to-current map. -/
theorem canonicalCurrentPoint_closed_inverse_data
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs₀ : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (k : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) k) :
    ContDiffAt ℝ ∞ (canonicalReferencePoint C K z k)
        (canonicalCurrentPoint C K z k p) ∧
      canonicalReferencePoint C K z k ∘ canonicalCurrentPoint C K z k =ᶠ[𝓝 p]
        (id : PolarPoint → PolarPoint) ∧
      canonicalCurrentPoint C K z k ∘ canonicalReferencePoint C K z k
        =ᶠ[𝓝 (canonicalCurrentPoint C K z k p)] (id : PolarPoint → PolarPoint) := by
  let q := K.chart (C.referenceState, 0) k p
  let x := canonicalCurrentPoint C K z k p
  have hq : q ∈ canonicalClosed S K k := (hA.boundary _ hz₀ hs₀ k).1 hp
  have hx : x ∈ physicalPieceClosed S K z k :=
    n04Coordinates_currentPoint_mapsTo_closed hA hz₀ hs₀ hz hs k hp
  have hFx : K.chart z k x = q := (hA.boundary z hz hs k).2.2.2.1 q hq
  have hF : ContDiffAt ℝ ∞ (K.chart z k) x :=
    ((hA.boundary z hz hs k).2.2.2.2.1 x hx).1
  have hG : ContDiffAt ℝ ∞ (K.inverseChart (C.referenceState, 0) k)
      (K.chart z k x) := by
    rw [hFx]
    exact n04b_inverseChart_contDiffAt_closed hA hz₀ hs₀ k hq
  refine ⟨ContDiffAt.fun_comp (f := K.chart z k)
      (g := K.inverseChart (C.referenceState, 0) k) x hG hF,
    n04Coordinates_referencePoint_currentPoint_germ hA hz₀ hs₀ hz hs k hp, ?_⟩
  have hto : Tendsto (K.chart z k) (𝓝 x) (𝓝 q) := by
    rw [← hFx]
    exact hF.continuousAt.tendsto
  have href := (canonicalClosed_inverse_germs hA hz₀ hs₀ k hq).2.comp_tendsto hto
  have hcur := (canonicalClosed_inverse_germs hA hz hs k hq).1
  filter_upwards [href, hcur] with y hy hr
  change K.chart (C.referenceState, 0) k
      (K.inverseChart (C.referenceState, 0) k (K.chart z k y)) = K.chart z k y at hy
  change K.inverseChart z k (K.chart (C.referenceState, 0) k
      (K.inverseChart (C.referenceState, 0) k (K.chart z k y))) = y
  rw [hy]
  exact hr

theorem n04Coordinates_actualAtlas_endpoint_fields
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let k := if side then (K.cutPair m).2 else (K.cutPair m).1
    OneSidedTransportEndpoint (canonicalCurrentPoint C K z k)
      (n04CoordinatesCurrentHeightRatio C K z k)
      (C.left m) (C.right m) (if side then C.right m else C.left m) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := if side then (K.cutPair m).2 else (K.cutPair m).1
  let c := if side then C.right m else C.left m
  let U : Set PolarPoint := Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hA : CanonicalGeometry D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hcut : CanonicalCutGeometry S C K base ε :=
    n04bActualTypedAtlas_cutGeometry hT hS hN hfield e
  have hz₀ := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ := hN.1.1.2.2.1.stateSector
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  have hi : e k = .inl (m, side) := by
    have hp : K.cutPair m = (e.symm (.inl (m, false)), e.symm (.inl (m, true))) := rfl
    change e (if side then (K.cutPair m).2 else (K.cutPair m).1) = _
    rw [hp]
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, Equiv.apply_symm_apply]
  have hτeq : EqOn (canonicalCurrentPoint C K z k)
      (n04CoordinatesNegativeTravelTransition S C L z m) U :=
    n04Coordinates_actualAtlas_currentPoint_eq_travel hT hS hN hfield hz hs m e k side hi
  have hqeq : EqOn (n04CoordinatesCurrentHeightRatio C K z k)
      (n04CoordinatesNegativeTravelHeightRatio S C L z m) U := by
    intro p hp
    unfold n04CoordinatesCurrentHeightRatio
    rw [hτeq hp]
    exact n04Coordinates_actualAtlas_height_ratio_eq_travel
      hT hS hN hfield hz hs m e k side hi hp
  have hτ := n04CoordinatesNegativeTravelTransition_smooth hT hS hN hfield hz hs m
  have hq := n04CoordinatesNegativeTravelHeightRatio_smooth_pos hT hS hN hfield hz hs m
  have hroot (θ : ℝ) : (c, θ) ∈ physicalPieceClosed S K (C.referenceState, 0) k :=
    (canonicalCutRoot_mem_closed_and_zero hA hcut hz₀ hs₀ m side θ).1
  refine {
    interval := hab
    endpoint := ?_
    smooth_on := ?_
    root_smooth := fun θ =>
      n04Coordinates_currentPoint_contDiffAt_closed hA hz₀ hs₀ hz hs k (hroot θ)
    root_radial := canonicalCurrentPoint_root_radial hA hcut hz₀ hs₀ hz hs m side
    root_jacobian := canonicalCurrentPoint_root_jacobian_pos hA hcut hz₀ hs₀ hz hs m side
    root_diagonal := canonicalCurrentPoint_root_positive_diagonal hA hcut hz₀ hs₀ hz hs m side
    root_inverse := fun θ => ⟨canonicalReferencePoint C K z k,
      canonicalCurrentPoint_closed_inverse_data hA hz₀ hs₀ hz hs k (hroot θ)⟩
    height_smooth_on := ?_
    height_positive := ?_
    height_root := fun θ =>
      n04Coordinates_currentHeightRatio_contDiffAt_pos_closed hA hz₀ hs₀ hz hs k (hroot θ)
    period_add := ?_
    reflect := ?_
    height_period := ?_
    height_even := ?_ }
  · cases side
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
  · intro p hp
    have he : canonicalCurrentPoint C K z k =ᶠ[𝓝 p]
        n04CoordinatesNegativeTravelTransition S C L z m := by
      filter_upwards [hU.mem_nhds hp] with y hy
      exact hτeq hy
    exact ((hτ.contDiffAt (hU.mem_nhds hp)).congr_of_eventuallyEq he).contDiffWithinAt
  · intro p hp
    have he : n04CoordinatesCurrentHeightRatio C K z k =ᶠ[𝓝 p]
        n04CoordinatesNegativeTravelHeightRatio S C L z m := by
      filter_upwards [hU.mem_nhds hp] with y hy
      exact hqeq hy
    exact ((hq.1.contDiffAt (hU.mem_nhds hp)).congr_of_eventuallyEq he).contDiffWithinAt
  · intro p hp
    rw [hqeq hp]
    exact hq.2 p hp
  · intro p hp
    have hp' : p + (0, Real.pi) ∈ U :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
    rw [hτeq hp', hτeq hp]
    exact (n04CoordinatesNegativeTravelTransition_symmetries hT hS hN hfield hz hs m hp).1
  · intro p hp
    have hp' : (p.1, -p.2) ∈ U := ⟨hp.1, mem_univ _⟩
    rw [hτeq hp', hτeq hp]
    exact (n04CoordinatesNegativeTravelTransition_symmetries hT hS hN hfield hz hs m hp).2
  · intro p hp
    have hp' : p + (0, Real.pi) ∈ U :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
    rw [hqeq hp', hqeq hp]
    exact (n04CoordinatesNegativeTravelHeightRatio_symmetries hT hS hN hfield hz hs m hp).1
  · intro p hp
    have hp' : (p.1, -p.2) ∈ U := ⟨hp.1, mem_univ _⟩
    rw [hqeq hp', hqeq hp]
    exact (n04CoordinatesNegativeTravelHeightRatio_symmetries hT hS hN hfield hz hs m hp).2

end ContinuousFlexibility.Analysis
