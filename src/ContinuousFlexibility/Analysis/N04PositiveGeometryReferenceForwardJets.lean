import ContinuousFlexibility.Analysis.N04PositiveGeometryStoredForwardSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFixedState
import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryPoint

/-!
# Original forward jets at the reference state

The reference chart is the retained atlas chart at the original
reference state. Its positive spatial jets come from the actual joint
forward tower by fixing the state to zero. Their sampled bounds are
independent of every later parameter order and shift.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04PositiveGeometry_sector_zero
    (S : PhysicalSpacesData) (base : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε := by
  constructor
  · change sectorGrading S base 0 < ε
    exact (sectorGrading S base).map_zero'.trans_lt hε
  · change |(0 : ℝ)| < ε
    simpa only [abs_zero] using hε

theorem n04PositiveGeometry_sector_lift_zero
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) :
    liftSectorParameter S C 0 = (C.referenceState, 0) := by
  exact (liftSectorParameter_eq_affine S C 0).trans
    ((congrArg (fun v : AnnularState S × ℝ => (C.referenceState, 0) + v)
      (ContinuousLinearMap.map_zero (sectorParameterInclusion S))).trans (add_zero _))

def n04PositiveGeometry_referenceForwardJet
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (m : ℕ) (side : Bool) (n : ℕ) (y : (StateDirections S × ℝ) × ℝ) :
    PolarPoint [×n]→L[ℝ] PolarPoint :=
  iteratedFDeriv ℝ n (K.chart (C.referenceState, 0)
    (if side then (K.cutPair m).2 else (K.cutPair m).1))
    (n01ComponentRoot C m side, y.2)

theorem n04PositiveGeometry_referenceForwardJet_eq
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (m : ℕ) (side : Bool) (n : ℕ) (y : (StateDirections S × ℝ) × ℝ) :
    n04PositiveGeometry_referenceForwardJet S C K m side n y =
      n04PositiveGeometry_storedForwardJet S C K m side n (0, y.2) := by
  exact congrArg (fun z : AnnularState S × ℝ => iteratedFDeriv ℝ n
    (K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1))
      (n01ComponentRoot C m side, y.2))
    (n04PositiveGeometry_sector_lift_zero S C).symm

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {Kcur : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {side : Bool}

def n04PositiveGeometry_referenceForwardJet_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_referenceForwardJet S C Kcur m side n) :=
  (n04PositiveGeometry_fixedState_joint
    (n04PositiveGeometry_storedForwardJet_joint hT hS hN hεone hflow hctx hr hroot n hn hn4)
    (n04PositiveGeometry_sector_zero S base hε)).congrOn
      (fun y _ => (n04PositiveGeometry_referenceForwardJet_eq S C Kcur m side n y).symm)

/-- The fixed reference root label is exactly the original angle. -/
theorem n04PositiveGeometry_referenceRoot_chart_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side) (θ : ℝ) :
    Kcur.chart (C.referenceState, 0)
      (if side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1)
      (n01ComponentRoot C m side, θ) = (0, θ) := by
  let g : ℝ → ℝ := hctx.choose
  let R : ℝ := hctx.choose_spec.choose
  let hR : 0 < R := hctx.choose_spec.choose_spec.choose
  let δ : ℝ := hctx.choose_spec.choose_spec.choose_spec.choose
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  let data := hc.2.2.2.2 (C.referenceState, 0)
    hN.reference_mem_stateNeighborhood hN.2.2.1.stateSector
  let Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ := data.2.choose
  have P := n04PositiveGeometry_actual_unitRootCoordinate_properties hT hS hN hflow
    hN.reference_mem_stateNeighborhood hN.2.2.1.stateSector m side g hc.1 hR
    data.1 hc.2.2.2.1.ne' Θ data.2.choose_spec.1
  let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
    (n01RootLabel S C (C.referenceState, 0) m side)
  have hv : Kcur.chart (C.referenceState, 0)
      (if side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1)
      (n01ComponentRoot C m side, θ) = extendedRootEvenOddChart G (0, θ) := by
    have h := congrArg (fun A : PolarPoint [×0]→L[ℝ] PolarPoint => A Fin.elim0)
      ((data.2.choose_spec.2 θ).2.2.2.2.1 0)
    simpa only [iteratedFDeriv_zero_apply, rootProfileShift, mul_zero, add_zero] using h
  exact (hv.trans (P.extended_chart_zero θ)).trans
    (congrArg (fun η : ℝ => ((0 : ℝ), η))
      (n04Realization_rootLabel_reference_eq hT hS hN m side θ))

/-- No parameter ball or derivative order enters the fixed reference
constant. Later compositions may use any common shift and sampling
scale without spending the angular reserve. -/
theorem n04PositiveGeometry_referenceForwardJet_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀)
        base ε m (!side), ∀ n : ℕ, 1 ≤ n → n ≤ 4 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_referenceForwardJet W.S W.C (W.A X.e₀) m (!side) n),
      ∀ K shift : ℕ, ∀ z ∈ sectorNeighborhood W.S base ε ε, ∀ θ : ℝ,
      ∀ P : (StateDirections W.S × ℝ) → Prop, ∀ t : ℝ, 1 ≤ t →
      N04BoundaryWordBounds Q K s 1 z θ P
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) t shift := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let data := n04PositiveGeometry_storedForwardJet_sample_prefix W X hb hε hεW hεone hflow
  let low : ℕ := data.choose
  let pref := data.choose_spec.2 0
  let c : ℕ := pref.choose
  let p := pairGrading (sectorGrading W.S) realGrading
  have hzero (j : ℕ) : p j 0 ≤ 1 := ((p j).map_zero').trans_le zero_le_one
  have h0 := n04PositiveGeometry_sector_zero W.S base hε
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  intro s
  let orderData := pref.choose_spec s
  let A : ℝ := orderData.choose
  refine ⟨A, orderData.choose_spec.1, ?_⟩
  intro i side m hm hctx n hn hn4 Q K shift z hz θ P t ht
  have hrad : n01ComponentRoot W.C m (!side) = n04PositiveEndpoint i side := by
    have he : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    cases side <;> exact he.symm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D :=
    hrad.symm ▸ (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 :=
    hrad.symm ▸ (W.roots i side).2.1
  let J := n04PositiveGeometry_storedForwardJet_joint W.hT W.hS hN hεone hflow
    hctx hr hroot n hn hn4
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  let H : ℝ := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let P₀ : (StateDirections W.S × ℝ) → Prop := fun v =>
    p low v ≤ 1 ∧ p (low + s + c * 0 + 1) v ≤ 1
  have hraw := orderData.choose_spec.2 i side m hm hctx n hn hn4 J
    0 h0 (hzero low) θ 1 le_rfl (hzero _)
  have hJ : N04BoundaryWordBounds J 0 s 1 0 θ P₀ (A * E ^ A) H 1 c := by
    simpa only [Real.one_rpow] using hraw
  let Q' := Q.congrOn (fun y _ =>
    n04PositiveGeometry_referenceForwardJet_eq W.S W.C (W.A X.e₀) m (!side) n y)
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hM : 0 ≤ A * E ^ A := mul_nonneg (zero_le_one.trans orderData.choose_spec.1)
    (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have hfixed := hJ.fixedState h0 ⟨hzero _, hzero _⟩ Q' hz hM
    (heightData.choose_spec.2 i).1 ht K shift P
  exact hfixed.congr hz (fun y _ =>
    (n04PositiveGeometry_referenceForwardJet_eq W.S W.C (W.A X.e₀) m (!side) n y).symm)

end ContinuousFlexibility.Analysis
