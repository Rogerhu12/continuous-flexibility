module

public import ContinuousFlexibility.Analysis.N04PulledFieldsStripAngularPower
public import ContinuousFlexibility.Analysis.N04PulledFieldsActualDisplacementFixedBase

/-!
# Fixed-base angular powers of the actual transport fields

Closed-radius selectors cover the original physical strips. Their
retained circle decoders identify any supplied genuine spatial tower
with the strong circle families. The actual residual is already
substituted in the displacement, on the original sector parameter space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance n04PulledFieldsActualAngularStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

private theorem n04PulledFields_actualAngular_parameterInterpolation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) :
    HasInterpolation (pairGrading (sectorGrading S) realGrading) :=
  hasInterpolation_of_hasSmoothing (sectorPairGrading_monotone S)
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)

include hN hl hh in
private theorem n04PulledFields_actualAngular_selectorCover
    (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (l m) (h m)) :
    ∃ i : {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)}, i.val m = r :=
  hN.closedRadiusSelector_cover m r
    ⟨((hl m).trans hr.1).le, (hr.2.trans (hh m)).le⟩

include hN hS hT in
private theorem n04PulledFields_actualAngular_inverseSlope_decode
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    returnFlowInverseSlope S C (liftSectorParameter S C x) m (rsel m, θ) =
      1 + (S.circle (3 / 4 : ℝ)).decode
        (hN.selectorInverseSlopeCircle hS hT rsel hrsel x) m θ :=
  (eq_add_of_sub_eq
    (hN.selectorInverseSlopeCircle_decode hS hT rsel hrsel x hx m θ).symm).trans
    (add_comm _ _)

include hN hS hT hflow in
private theorem n04PulledFields_actualAngular_inverseSlope_family :
    ∃ g : {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)} →
        (StateDirections S × ℝ) → CircleSpace S,
      N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε) g ∧
      ∀ i x, x ∈ sectorNeighborhood S base ε ε → ∀ m θ,
        returnFlowInverseSlope S C (liftSectorParameter S C x) m (i.val m, θ) =
          1 + (S.circle (3 / 4 : ℝ)).decode (g i x) m θ := by
  refine ⟨fun i => hN.selectorInverseSlopeCircle hS hT i.val i.property, ?_, ?_⟩
  · exact hN.n04PulledFields_fixedBase_selectorInverseSlopeCircle
      (I := {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)})
      hS hT hflow (fun i => i.val) (fun i => i.property)
  · exact fun i x hx m θ => n04PulledFields_actualAngular_inverseSlope_decode
      hN hS hT i.val i.property x hx m θ

include hN hS hT hflow hl hh in
/-- The old inverse slope has a common low order before all parameter
prefixes. Its affine constant and bounded sample height are absorbed
only in the numerical coefficient. -/
theorem N01Properties.n04PulledFields_returnFlowInverseSlope_angular_growth
    (KH : ℝ) (hKH : 0 ≤ KH)
    (hheight : ∀ m, T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ KH) (W : ℕ → ℝ)
    (J : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnFlowInverseSlope S C (liftSectorParameter S C x.1) m x.2)) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      N04PulledFieldsAngularPowerGrowth (pairGrading (sectorGrading S) realGrading)
        W (fun _ => 1) J K B highLoss shift := by
  let family := n04PulledFields_actualAngular_inverseSlope_family hN hS hT hflow
  exact N04PulledFieldsFixedBaseFamily.realized_strip_angular_power_add_const
    (I := {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)})
    (E := StateDirections S × ℝ) (T := T) (γ := (3 / 4 : ℝ))
    (H := S.circle (3 / 4 : ℝ))
    (U := sectorNeighborhood S base ε ε)
    (p := pairGrading (sectorGrading S) realGrading)
    (g := family.choose)
    (f := fun m (x : (StateDirections S × ℝ) × PolarPoint) =>
      returnFlowInverseSlope S C (liftSectorParameter S C x.1) m x.2)
    family.choose_spec.1 (sectorPairGrading_monotone S)
    (n04PulledFields_actualAngular_parameterInterpolation hS) (hS.2.1 (3 / 4 : ℝ))
    ((material_circle_sample_weights_pos hT hN.1.1).2)
    KH hKH hheight l h (fun i => i.val)
    (n04PulledFields_actualAngular_selectorCover hN l h hl hh) J 1
    (fun i m _hr x hx θ => family.choose_spec.2 i x hx m θ) W

include hN hS hT hflow hl hh in
/-- The actual residual-substituted displacement retains its full
sample-height factor on the original sector parameter neighborhood. -/
theorem N01Properties.n04PulledFields_actualPulledDisplacement_angular_growth
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hR : N02Properties D T S C R base ε) (W : ℕ → ℝ)
    (J : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1)
          m x.2 (R.residual (liftSectorParameter S C x.1)))) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      N04PulledFieldsAngularPowerGrowth (pairGrading (sectorGrading S) realGrading)
        W (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) J K B highLoss shift := by
  let H := S.circle (3 / 4 : ℝ)
  let I := {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)}
  let rsel : I → ℕ → ℝ := Subtype.val
  have hrsel (i : I) (m : ℕ) : rsel i m ∈ Icc (C.left m) (C.right m) := i.property m
  have hcover (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (l m) (h m)) : ∃ i : I, rsel i m = r :=
    hN.closedRadiusSelector_cover m r ⟨((hl m).trans hr.1).le, (hr.2.trans (hh m)).le⟩
  let g : I → (StateDirections S × ℝ) → H.Space := fun i z =>
    hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
      (rsel i) (hrsel i) z (R.residual (liftSectorParameter S C z))
  have hg : N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      H.grading (sectorNeighborhood S base ε ε) g :=
    hN.n04PulledFields_fixedBase_actualReturnCorrectionPulledDisplacement
      hS hT hflow χ hχrange hR rsel hrsel
  apply hg.realized_strip_angular_power (sectorPairGrading_monotone S)
    (n04PulledFields_actualAngular_parameterInterpolation hS) (hS.2.1 (3 / 4 : ℝ))
    ((material_circle_sample_weights_pos hT hN.1.1).2) l h rsel hcover J _ W
  intro i m _hr x hx θ
  exact (hN.returnCorrectionPulledDisplacementCircleLinear_decode hS hT χ hχrange
    (rsel i) (hrsel i) x hx (R.residual (liftSectorParameter S C x)) m θ).symm

end ContinuousFlexibility.Statements
