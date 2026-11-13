import ContinuousFlexibility.Analysis.N04PositiveGeometryStoredHeightSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryReferenceForwardJets

/-! # The actual reference height powers at the root circles -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

def n04PositiveGeometry_referenceHeightPowerJet
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (m : ℕ) (side : Bool) (γ : ℝ) (n : ℕ) (y : (StateDirections S × ℝ) × ℝ) :
    PolarPoint [×n]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ n (fun p => K.height (C.referenceState, 0)
    (if side then (K.cutPair m).2 else (K.cutPair m).1) p ^ γ)
    (n01ComponentRoot C m side, y.2)

theorem n04PositiveGeometry_referenceHeightPowerJet_eq
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (m : ℕ) (side : Bool) (γ : ℝ) (n : ℕ) (y : (StateDirections S × ℝ) × ℝ) :
    n04PositiveGeometry_referenceHeightPowerJet S C K m side γ n y =
      n04PositiveGeometry_storedHeightPowerJet S C K m side γ n (0, y.2) := by
  exact congrArg (fun z : AnnularState S × ℝ => iteratedFDeriv ℝ n
    (fun p => K.height z (if side then (K.cutPair m).2 else (K.cutPair m).1) p ^ γ)
      (n01ComponentRoot C m side, y.2))
    (n04PositiveGeometry_sector_lift_zero S C).symm

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {Kcur : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {side : Bool}

def n04PositiveGeometry_referenceHeightPowerJet_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (γ : ℝ) (n : ℕ) (hn : n ≤ 3) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_referenceHeightPowerJet S C Kcur m side γ n) :=
  (n04PositiveGeometry_fixedState_joint
    (n04PositiveGeometry_storedHeightPowerJet_joint hT hS hN hεone hflow hctx hr hroot γ n hn)
    (n04PositiveGeometry_sector_zero S base hε)).congrOn
      (fun y _ => (n04PositiveGeometry_referenceHeightPowerJet_eq S C Kcur m side γ n y).symm)

/-- Reference values are sampled with radius one. Every state slot of
the fixed reference tower vanishes, so any later shift is permitted. -/
theorem n04PositiveGeometry_referenceHeightPowerJet_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∀ γ : ℝ, ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀)
        base ε m (!side), ∀ n : ℕ, n ≤ 3 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_referenceHeightPowerJet W.S W.C (W.A X.e₀) m (!side) γ n),
      ∀ K shift : ℕ, ∀ z ∈ sectorNeighborhood W.S base ε ε, ∀ θ : ℝ,
      ∀ P : (StateDirections W.S × ℝ) → Prop, ∀ t : ℝ, 1 ≤ t →
      N04BoundaryWordBounds Q K s 1 z θ P
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) t shift := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let data := n04PositiveGeometry_storedHeightPowerJet_sample_prefix W X hb hε hεW hεone hflow
  let low : ℕ := data.choose
  let p := pairGrading (sectorGrading W.S) realGrading
  have hzero (j : ℕ) : p j 0 ≤ 1 := ((p j).map_zero').trans_le zero_le_one
  have h0 := n04PositiveGeometry_sector_zero W.S base hε
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  intro γ s
  let pref := data.choose_spec.2 γ 0
  let c : ℕ := pref.choose
  let orderData := pref.choose_spec s
  let A : ℝ := orderData.choose
  refine ⟨A, orderData.choose_spec.1, ?_⟩
  intro i side m hm hctx n hn Q K shift z hz θ P t ht
  have hrad : n01ComponentRoot W.C m (!side) = n04PositiveEndpoint i side := by
    have he : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    cases side <;> exact he.symm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D :=
    hrad.symm ▸ (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 :=
    hrad.symm ▸ (W.roots i side).2.1
  let J := n04PositiveGeometry_storedHeightPowerJet_joint W.hT W.hS hN hεone hflow
    hctx hr hroot γ n hn
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  let H : ℝ := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let P₀ : (StateDirections W.S × ℝ) → Prop := fun v =>
    p low v ≤ 1 ∧ p (low + s + c * 0 + 1) v ≤ 1
  have hraw := orderData.choose_spec.2 i side m hm (W.A X.e₀) hctx n hn J
    0 h0 (hzero low) θ 1 le_rfl (hzero _)
  have hJ : N04BoundaryWordBounds J 0 s 1 0 θ P₀ (A * E ^ A) H 1 c := by
    simpa only [Real.one_rpow] using hraw
  let Q' := Q.congrOn (fun y _ =>
    n04PositiveGeometry_referenceHeightPowerJet_eq W.S W.C (W.A X.e₀) m (!side) γ n y)
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hM : 0 ≤ A * E ^ A := mul_nonneg (zero_le_one.trans orderData.choose_spec.1)
    (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have hfixed := hJ.fixedState h0 ⟨hzero _, hzero _⟩ Q' hz hM
    (heightData.choose_spec.2 i).1 ht K shift P
  exact hfixed.congr hz (fun y _ =>
    (n04PositiveGeometry_referenceHeightPowerJet_eq W.S W.C (W.A X.e₀) m (!side) γ n y).symm)

end ContinuousFlexibility.Analysis
