import ContinuousFlexibility.Analysis.N03StateRootBandIdentification
import ContinuousFlexibility.Analysis.N01ControlledRootModel
import ContinuousFlexibility.Analysis.RootPhysicalJetTransfer
import ContinuousFlexibility.Analysis.N04FlowJetsProof

/-!
# Uniform ordinary jets at the actual stored root circles

The same controlled N01 model has uniform bounds before the state is
chosen. Actual N03 coefficient germs identify that model with the stored
chart and height on a band which may depend on the state. Only the root
point is used below, so the identification radius does not enter any
constant. No fixed-cutoff representation of the correction is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def N03RootEndpointFieldFamily
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (rightEnd : Bool)
    (κJ : ℝ) (B : ℕ → ℝ) : Prop :=
  let r := n01ComponentRoot C m rightEnd
  let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ θ : ℝ,
    (r, θ) ∈ physicalPieceClosed S K z i ∧
      κJ ≤ |planeJacobian (K.chart z i) (r, θ)| ∧
      RootPhysicalFieldJetBound (pairGrading (stateGrading S) realGrading)
        loss B (z - (C.referenceState, 0)) (K.chart z i) (K.height z i) (r, θ)

private theorem n03_rootEndpoint_fields_at_state
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss flowLoss outLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {R δ ρ Λ J₀ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hρ : 0 < ρ)
    {A B : ℕ → ℝ} (hApos : ∀ n, 0 < A n) (hBpos : ∀ n, 0 < B n)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    (hmodel : N01ControlledRootModelAtState D S C m rightEnd g hR δ ρ Λ J₀
      flowLoss outLoss A B z) :
    let r := n01ComponentRoot C m rightEnd
    let σ := n01ComponentRootOrientation rightEnd
    let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
    ∀ θ : ℝ, (r, θ) ∈ physicalPieceClosed S K z i ∧
      J₀ / δ ≤ |planeJacobian (K.chart z i) (r, θ)| ∧
      RootPhysicalFieldJetBound (pairGrading (stateGrading S) realGrading)
        outLoss (rootAffineJetEnvelope (σ * δ) B) (z - (C.referenceState, 0))
        (K.chart z i) (K.height z i) (r, θ) := by
  obtain ⟨_hcontrol, Θ, hΘ, hG, hperiod, hCS, hvalues, hjets⟩ := hmodel
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
  let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
  let V := rootScaledDividedDiscriminant D S C z g r σ δ
  let M := A 1 * (1 + pairGrading (stateGrading S) realGrading (1 + flowLoss)
    (z - (C.referenceState, 0)))
  have hM : 0 ≤ M :=
    mul_nonneg (hApos 1).le (add_nonneg zero_le_one (apply_nonneg _ _))
  obtain ⟨η, hη, _hηone, hηR, hband, hcoeff⟩ :=
    n03_exists_state_controlledRoot_band hS hT hN hfield hA hB hz hs m rightEnd
      hg hR hδ hM hstrip Θ hΘ hG hperiod (hCS 1)
  have hσne : σ ≠ 0 := by
    rcases n01ComponentRootOrientation_eq rightEnd with h | h <;>
      rw [show σ = _ from h] <;> norm_num
  have hscaleNe : σ * δ ≠ 0 := mul_ne_zero hσne hδ.ne'
  have hscaleAbs : |σ * δ| = δ := by
    rcases n01ComponentRootOrientation_eq rightEnd with h | h
    · rw [show σ = 1 from h]
      simp only [one_mul, abs_of_pos hδ]
    · rw [show σ = -1 from h]
      simp only [neg_one_mul, abs_neg, abs_of_pos hδ]
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) ρ := ⟨le_rfl, hρ.le⟩
  have hmodelRoot : ∀ θ : ℝ,
      RootPhysicalFieldJetBound (pairGrading (stateGrading S) realGrading)
        outLoss B (z - (C.referenceState, 0))
        (extendedRootEvenOddChart G) (rootDividedHeight δ V G) (0, θ) :=
    rootDividedModel_jetBound_allAngles hδ hG hperiod
      (rootScaledDividedDiscriminant_period_add hS C z g r σ δ)
      (fun θ => ⟨(hvalues (0, θ) hzero).1, (hvalues (0, θ) hzero).2.1,
        (hvalues (0, θ) hzero).2.2.1⟩)
      (fun θ hθ => hjets (0, θ) hzero hθ)
  intro θ
  have hclosed : (r, θ) ∈ physicalPieceClosed S K z i := by
    simpa only [r, i, n01ComponentRoot] using
      (canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m rightEnd θ).1
  have hregular := (hA.boundary z hz hs i).2.2.2.2.1 (r, θ) hclosed
  have hident := n03_fixedRoot_chart_height_ordinaryJets hS hT hN.1.1 hN.2 hA hB
    hz hs m rightEnd hR hδ hη hηR hstrip Θ hband hcoeff hG hperiod
    (q := (0, θ)) ⟨le_rfl, hη.le⟩
    (hvalues (0, θ) hzero).1 (hvalues (0, θ) hzero).2.1
    (hvalues (0, θ) hzero).2.2.1
  have hpoint : rootProfileShift r (σ * δ) (0, θ) = (r, θ) := by
    simp only [rootProfileShift, mul_zero, add_zero]
  have hFjet (n : ℕ) :
      iteratedFDeriv ℝ n (fun y => K.chart z i (rootProfileShift r (σ * δ) y)) (0, θ) =
        iteratedFDeriv ℝ n (extendedRootEvenOddChart G) (0, θ) := by
    simpa only [rootProfileShift, mul_assoc] using hident.2.2.1 n
  have hHjet (a : ℝ) (n : ℕ) :
      iteratedFDeriv ℝ n (fun y => K.height z i (rootProfileShift r (σ * δ) y) ^ a) (0, θ) =
        iteratedFDeriv ℝ n (fun y => rootDividedHeight δ V G y ^ a) (0, θ) := by
    simpa only [rootProfileShift, mul_assoc] using hident.2.2.2 a n
  have htransfer := rootPhysicalFields_of_scaled_jet_model
    (E := AnnularState S × ℝ) (p := pairGrading (stateGrading S) realGrading)
    (loss := outLoss) (B := B) (z := z - (C.referenceState, 0))
    r (σ * δ) hscaleNe (fun n => (hBpos n).le)
    (F := K.chart z i) (M := extendedRootEvenOddChart G)
    (H := K.height z i) (h := rootDividedHeight δ V G) (q := (0, θ))
    (by simpa only [hpoint] using hregular.1)
    (by simpa only [hpoint] using hregular.2.1)
    (by simpa only [hpoint] using hregular.2.2.2)
    (hmodelRoot θ) hFjet hHjet (hvalues (0, θ) hzero).2.2.2
  exact ⟨hclosed, by simpa only [hpoint, hscaleAbs] using htransfer.2,
    by simpa only [hpoint] using htransfer.1⟩

/-- Common low order and loss are chosen before the component. For each
component and side, all actual root-field constants are chosen before
the state. Only endpoint jets are asserted: no state-uniform physical
collar is inferred from the original N03 germ statement. -/
theorem n03_controlledRoot_endpoint_physicalJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) (flowLoss : ℕ) :
    ∃ low outLoss : ℕ, outLoss ≤ low ∧
      ∀ m : ℕ, ∀ rightEnd : Bool, ∀ g : ℝ → ℝ,
      ∀ R : ℝ, ∀ hR : 0 < R, ContDiff ℝ ∞ g →
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) R) →
      ∀ κ δ Λ : ℝ, 0 < κ → 0 < δ → δ ≤ 1 →
      ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      N01ControlledRootInputFamily D S C base flowLoss ε m rightEnd g hR κ δ Λ A →
      ∃ κJ : ℝ, ∃ B : ℕ → ℝ, 0 < κJ ∧ (∀ n, 0 < B n) ∧
        N03RootEndpointFieldFamily S C K (max base low) outLoss
          (min ε (1 / 2 : ℝ)) m rightEnd κJ B := by
  obtain ⟨lowM, outLoss, hmodel⟩ :=
    n01_controlledRootInput_uniform_model hS hT hN.1.1 hflow flowLoss
  let low := max lowM outLoss
  refine ⟨low, outLoss, le_max_right _ _, ?_⟩
  intro m rightEnd g R hR hg hstrip κ δ Λ hκ hδ hδone A hApos hinput
  obtain ⟨ρ, J₀, B, hρ, _hρone, _hρR, hJ₀, hBpos, hmodels⟩ :=
    hmodel m rightEnd g R hR hg hstrip κ δ Λ 1 hκ hδ hδone
      zero_lt_one le_rfl A hApos hinput
  let σ := n01ComponentRootOrientation rightEnd
  refine ⟨J₀ / δ, rootAffineJetEnvelope (σ * δ) B, div_pos hJ₀ hδ,
    rootAffineJetEnvelope_pos hBpos (σ * δ), ?_⟩
  dsimp only [N03RootEndpointFieldFamily]
  intro z hz hs
  have hzold : z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C (le_max_left _ _) (min_le_left _ _) hz
  have hzmodel : z ∈ stateNeighborhood S C (max base lowM) (min ε (1 / 2 : ℝ)) :=
    stateNeighborhood_mono S C (max_le_max le_rfl (le_max_left _ _)) le_rfl hz
  exact n03_rootEndpoint_fields_at_state hS hT hN hfield hA hB hzold hs m rightEnd
    hg hR hδ hρ hApos hBpos (hstrip z hzold hs) (hmodels z hzmodel hs)

/-- The genuine N01 chosen-flow factory supplies every input of the
endpoint theorem on one smaller common neighborhood. All original
D/T/S/C/E/L/K data remain; the component constants precede every state. -/
theorem n04b_exists_common_root_endpoint_fields
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ outLoss ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∀ rightEnd : Bool,
        ∃ κJ : ℝ, ∃ B : ℕ → ℝ, 0 < κJ ∧ (∀ n, 0 < B n) ∧
          N03RootEndpointFieldFamily S C K newBase outLoss ε' m rightEnd κJ B := by
  obtain ⟨rootBase, flowLoss, η, hb, hη, hηε, hflow, hinputs⟩ :=
    n01_exists_common_root_inputs n04FlowJetsTarget_proof hS hT hN.1.1
  have hsub := stateNeighborhood_mono S C hb hηε
  have hN' := nonlinearPropertiesThrough03_restrict hT hN hb le_rfl hη hηε
  have hA' := n04PartA_restrict hA hb hηε
  have hB' := n04PartB_restrict hB hb hηε
  have hfield' : N04bFieldRegularity D S C L rootBase η :=
    { smooth_coefficients := fun z hz => hfield.smooth_coefficients z (hsub hz)
      periodic_coefficients := fun z hz => hfield.periodic_coefficients z (hsub hz)
      positive_a := fun z hz => hfield.positive_a z (hsub hz)
      negative_discriminant := fun z hz => hfield.negative_discriminant z (hsub hz) }
  obtain ⟨low, outLoss, hout, hbound⟩ :=
    n03_controlledRoot_endpoint_physicalJets hS hT hN' hfield' hA' hB' hflow flowLoss
  refine ⟨max rootBase low, outLoss, min η (1 / 2 : ℝ),
    hb.trans (le_max_left _ _), hout.trans (le_max_right _ _),
    lt_min hη (by norm_num), (min_le_left _ _).trans hηε, ?_⟩
  intro m rightEnd
  obtain ⟨g, R, hR, κ, hg, _hg0, hκ, _hfactor, hgeometry, hflows⟩ :=
    hinputs m rightEnd
  obtain ⟨δ, A, hδ, _hδR, hδone, hApos, hfamily⟩ := hflows 1 zero_lt_one
  exact hbound m rightEnd g R hR hg (fun z hz hs => (hgeometry.1 z hz hs).1)
    κ δ 1 hκ hδ hδone A hApos hfamily

end ContinuousFlexibility.Analysis
