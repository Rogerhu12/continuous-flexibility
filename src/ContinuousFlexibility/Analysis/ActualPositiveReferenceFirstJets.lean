module

public import ContinuousFlexibility.Analysis.ActualPositiveReferenceInterpolation
public import ContinuousFlexibility.Analysis.FiniteFirstJetInverse
public import ContinuousFlexibility.Analysis.CanonicalWholePositiveRootMatching

/-!
# Fixed aligned first jets of the actual positive reference chart

The selected radial reference interpolation matches the same certified
negative source. The negative reference angular identity on the open
component reaches its genuine root jets by ordinary continuity. Thus
the two scalar interpolation outputs give the full aligned chart and
height first jets. Both normal alignments are fixed before the state.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04Coordinates_actual_positive_reference_firstJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (i : N04PositiveComponent D.a D.b (deriv D.w))
    (j : ∀ side, N04PositiveEndpointSource C i side) {Y H : ℝ → ℝ}
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hYjets : ∀ side θ a, a ≤ 1 →
      iteratedFDeriv ℝ a (fun p : PolarPoint => Y p.1)
          (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ a (n04PositiveReferenceSourceCoordinate (j side)
          (n04bActualTypedAtlas hT hS hN hfield e)) (n04PositiveEndpoint i side, θ))
    (hHjets : ∀ side θ a, a ≤ 1 →
      iteratedFDeriv ℝ a (fun p : PolarPoint => H p.1)
          (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ a (n04PositiveReferenceSourceHeight (j side)
          (n04bActualTypedAtlas hT hS hN hfield e)) (n04PositiveEndpoint i side, θ))
    (m : ℕ) (side : Bool)
    (hadj : n04PositiveEndpoint i (!side) = (if side then C.right m else C.left m)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let k := if side then (K.cutPair m).2 else (K.cutPair m).1
    let c := if side then C.right m else C.left m
    let v : ℝ := if !side then 1 else 0
    let s : ℝ := if !side then 1 else -1
    let A : PolarPoint → PolarPoint := fun p => (p.1 - v, p.2)
    let B : PolarPoint → PolarPoint := fun p => (s * p.1, p.2)
    ∀ θ, (A (positiveReferenceCylinderChart Y (c, θ))).1 = 0 ∧
      FiniteFullJetMatch 1 (c, θ) (A ∘ positiveReferenceCylinderChart Y)
        (B ∘ K.chart (C.referenceState, 0) k) ∧
      FiniteFullJetMatch 1 (c, θ) (fun p : PolarPoint => H p.1)
        (K.height (C.referenceState, 0) k) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := if side then (K.cutPair m).2 else (K.cutPair m).1
  let c := if side then C.right m else C.left m
  let v : ℝ := if !side then 1 else 0
  let s : ℝ := if !side then 1 else -1
  let A : PolarPoint → PolarPoint := fun p => (p.1 - v, p.2)
  let B : PolarPoint → PolarPoint := fun p => (s * p.1, p.2)
  have hrootEq : n04PositiveEndpoint i (!side) =
      (if !side then C.left m else C.right m) := by
    cases side <;> exact hadj
  have hj := n04PositiveEndpointSource_eq_some_of_negative_endpoint hN.1.1 (j (!side)) m hrootEq
  have hsource :
      n04PositiveReferenceSourceCoordinate (j (!side)) K =
        (fun p => v + s * (K.chart (C.referenceState, 0) k p).1) ∧
      n04PositiveReferenceSourceHeight (j (!side)) K = K.height (C.referenceState, 0) k := by
    simp only [n04PositiveReferenceSourceCoordinate, n04PositiveReferenceSourceHeight, hj]
    cases side <;> exact ⟨rfl, rfl⟩
  have hk : e.symm (.inl (m, side)) = k := by
    cases side <;> rfl
  have hopen := n04Coordinates_actual_reference_negative_radial_fields hT hS hN hfield e m side
  have hroot := n04Coordinates_actual_reference_negative_endpoint_data hT hS hN hfield e m side
  simp only [hk] at hopen hroot
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  have hc : c ∈ Icc (C.left m) (C.right m) := by
    cases side
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
  dsimp only
  intro θ
  have hcl : (c, θ) ∈ closure (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_univ]
    exact ⟨hc, mem_univ _⟩
  have hangle : FiniteFullJetMatch 1 (c, θ)
      (fun p => (K.chart (C.referenceState, 0) k p).2) (Prod.snd : PolarPoint → ℝ) :=
    finiteFullJetMatch_of_eqOn_closure (isOpen_Ioo.prod isOpen_univ)
      (hroot.1 θ).1.snd contDiffAt_snd
      (fun p hp => by
        have he := congrArg (fun q : PolarPoint => q.2) (hopen.2.2.1 p hp)
        exact he) hcl
  have hy : FiniteFullJetMatch 1 (c, θ) (fun p : PolarPoint => Y p.1)
      (fun p => v + s * (K.chart (C.referenceState, 0) k p).1) := by
    refine ⟨hgeometry.chart_smooth.fst.contDiffAt,
      contDiffAt_const.add (contDiffAt_const.mul (hroot.1 θ).1.fst), ?_⟩
    intro a ha
    have he := hYjets (!side) θ a ha
    rw [hadj, hsource.1] at he
    exact he
  have hh : FiniteFullJetMatch 1 (c, θ) (fun p : PolarPoint => H p.1)
      (K.height (C.referenceState, 0) k) := by
    refine ⟨hgeometry.height_smooth.contDiffAt, (hroot.1 θ).2.1, ?_⟩
    intro a ha
    have he := hHjets (!side) θ a ha
    rw [hadj, hsource.2] at he
    exact he
  have hA : ContDiff ℝ ∞ A :=
    (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  have hchart : FiniteFullJetMatch 1 (c, θ)
      (A ∘ positiveReferenceCylinderChart Y) (B ∘ K.chart (C.referenceState, 0) k) := by
    simpa only [A, B, positiveReferenceCylinderChart, Function.comp_def, add_sub_cancel_left]
      using (hy.prodMk hangle.symm).comp hA.contDiffAt
  have hzero : (K.chart (C.referenceState, 0) k (c, θ)).1 = 0 :=
    congrArg Prod.fst (hroot.1 θ).2.2.1
  have hz : (A (positiveReferenceCylinderChart Y (c, θ))).1 = 0 := by
    simpa only [A, B, Function.comp_apply, hzero, mul_zero] using
      congrArg Prod.fst hchart.value
  exact ⟨hz, hchart, hh⟩

end ContinuousFlexibility.Analysis
