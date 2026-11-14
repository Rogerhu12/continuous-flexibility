module

public import ContinuousFlexibility.Analysis.N03ControlledRootUnitIdentification
public import ContinuousFlexibility.Analysis.N04RealizationLeadAssembly

/-!
# One common neighborhood for the original root models

The completed atlas changes only its divided field. Its chart and height
jets identify the original atlas with one unit model at each state, using
the same flow for every angle and every spatial order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

def N04PositiveGeometryRootUnitModel
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (side : Bool)
    (g : ℝ → ℝ) (δ : ℝ) (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) : Prop :=
  ∀ θ : ℝ,
    let r := n01ComponentRoot C m side
    let σ := n01ComponentRootOrientation side
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let arg := rootProfileShift r σ
    let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
      (n01RootLabel S C z m side)
    let V := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ
    (r, θ) ∈ physicalPieceClosed S K z i ∧
      ContDiffAt ℝ ∞ (fun p => K.chart z i (arg p)) (0, θ) ∧
      ContDiffAt ℝ ∞ (fun p => K.height z i (arg p)) (0, θ) ∧
      0 < K.height z i (r, θ) ∧
      (∀ n : ℕ, iteratedFDeriv ℝ n (fun p => K.chart z i (arg p)) (0, θ) =
        iteratedFDeriv ℝ n (extendedRootEvenOddChart G) (0, θ)) ∧
      ∀ γ : ℝ, ∀ n : ℕ,
        iteratedFDeriv ℝ n (fun p => K.height z i (arg p) ^ γ) (0, θ) =
          iteratedFDeriv ℝ n (fun p => rootDividedHeight 1 V G p ^ γ) (0, θ)

def N04PositiveGeometryRootContext
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (base : ℕ) (ε : ℝ) (m : ℕ) (side : Bool) : Prop :=
  ∃ g : ℝ → ℝ, ∃ R : ℝ, ∃ hR : 0 < R, ∃ δ : ℝ,
    ContDiff ℝ ∞ g ∧ 0 < g 0 ∧
    (∀ t, -deriv D.w (n01ComponentRoot C m side +
      n01ComponentRootOrientation side * t) = t * g t) ∧ 0 < δ ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) R ∧
      ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
        N04FlowEquations (rootRescaledField
          (localizedRootDrift D S C (n01ComponentRoot C m side)
            (n01ComponentRootOrientation side) hR z)
          (localizedRootSpeed D S C g (n01ComponentRoot C m side)
            (n01ComponentRootOrientation side) hR z) δ) Θ ∧
        N04PositiveGeometryRootUnitModel D S C K z m side g δ Θ

private theorem rootContext_interiorDivision
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (base : ℕ) (ε : ℝ) (m : ℕ) (side : Bool) :
    N04PositiveGeometryRootContext D S C (n04bWithInteriorDivision C K) base ε m side ↔
      N04PositiveGeometryRootContext D S C K base ε m side := Iff.rfl

private theorem rootContext_of_input
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base low loss flowLoss : ℕ} {ε η : ℝ} {m : ℕ} {side : Bool}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hinput : N01ControlledRootInputData D S C base flowLoss ε m side)
    (hsub : stateNeighborhood S C low η ⊆ stateNeighborhood S C base ε) :
    N04PositiveGeometryRootContext D S C K low η m side := by
  let g : ℝ → ℝ := hinput.choose
  let R : ℝ := hinput.choose_spec.choose
  let hR : 0 < R := hinput.choose_spec.choose_spec.choose
  let κ : ℝ := hinput.choose_spec.choose_spec.choose_spec.choose
  have hroot := hinput.choose_spec.choose_spec.choose_spec.choose_spec
  have hκ : 0 < κ := hroot.2.2.1
  let flowData := hroot.2.2.2.2.2 1 zero_lt_one
  let δ : ℝ := flowData.choose
  let A : ℕ → ℝ := flowData.choose_spec.choose
  have hchosen := flowData.choose_spec.choose_spec
  have hApos : ∀ n, 0 < A n := hchosen.2.2.2.1
  refine ⟨g, R, hR, δ, hroot.1, hroot.2.1, hroot.2.2.2.1, hchosen.1, ?_⟩
  intro z hz hs
  have hz' : z ∈ stateNeighborhood S C base ε := hsub hz
  have hstrip := (hroot.2.2.2.2.1.1 z hz' hs).1
  refine ⟨hstrip, ?_⟩
  exact n03_controlledRootInput_unit_identification hS hT hN hfield hA hB hz' hs m side
    hroot.1 hR hκ hchosen.1 hApos hstrip
    (hchosen.2.2.2.2 z hz' hs)

/-- The low neighborhood precedes every power, finite jet prefix and
angular order. The original chosen chart, inverse, height and cut pair
are retained; only their geometric certificates are restricted. -/
theorem n04PositiveGeometry_common_root_context
    (W : N04RealizationStart) (X : N04RealizationChoice W) :
    ∃ base : ℕ, ∃ ε : ℝ, W.base ≤ base ∧ 0 < ε ∧ ε ≤ W.ε ∧ ε ≤ 1 ∧
      OrdinaryFlowJacobianBounds W.S W.C base ε ∧
      ∀ m side, N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side := by
  let data := n01_exists_common_root_inputs n04FlowJetsTarget_proof
    W.hS W.hT W.through03.1.1
  let base : ℕ := data.choose
  let flowLoss : ℕ := data.choose_spec.choose
  let η : ℝ := data.choose_spec.choose_spec.choose
  have hdata := data.choose_spec.choose_spec.choose_spec
  have hb : W.base ≤ base := hdata.1
  have hη : 0 < η := hdata.2.1
  have hηW : η ≤ W.ε := hdata.2.2.1
  have hinputs : ∀ m side,
      N01ControlledRootInputData W.D W.S W.C base flowLoss η m side := hdata.2.2.2.2
  have hsub : stateNeighborhood W.S W.C base η ⊆
      stateNeighborhood W.S W.C W.base W.ε := stateNeighborhood_mono W.S W.C hb hηW
  have hN : NonlinearPropertiesThrough03 W.D W.T W.S W.C W.R W.L base W.loss η :=
    nonlinearPropertiesThrough03_restrict W.hT W.through03 hb le_rfl hη hηW
  have hfield : N04bFieldRegularity W.D W.S W.C W.L base η :=
    { smooth_coefficients := fun z hz => W.field.smooth_coefficients z (hsub hz)
      periodic_coefficients := fun z hz => W.field.periodic_coefficients z (hsub hz)
      positive_a := fun z hz => W.field.positive_a z (hsub hz)
      reference_flow := W.field.reference_flow
      negative_discriminant := fun z hz => W.field.negative_discriminant z (hsub hz) }
  let K : CanonicalData W.S := W.A X.e₀
  let K' : CanonicalData W.S := n04bWithInteriorDivision W.C K
  have hA : N04PartA W.D W.S W.C K' base η :=
    n04PartA_restrict (n04bWithInteriorDivision_partA
      (n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field X.e₀)) hb hηW
  have hB : N04PartB W.S W.C W.L K' base η :=
    n04PartB_restrict (n04bActualTypedAtlas_interiorCompletion_partB
      W.hT W.hS W.through03 W.field X.e₀) hb hηW
  let ε : ℝ := min η 1
  have hsmall : stateNeighborhood W.S W.C base ε ⊆
      stateNeighborhood W.S W.C base η :=
    stateNeighborhood_mono W.S W.C le_rfl (min_le_left _ _)
  refine ⟨base, ε, hb, lt_min hη zero_lt_one, (min_le_left _ _).trans hηW,
    min_le_right _ _, (fun z hz => hdata.2.2.2.1 z (hsmall hz)), ?_⟩
  intro m side
  exact (rootContext_interiorDivision W.D W.S W.C K base ε m side).mp
    (rootContext_of_input W.hS W.hT hN hfield hA hB (hinputs m side) hsmall)

end ContinuousFlexibility.Analysis
