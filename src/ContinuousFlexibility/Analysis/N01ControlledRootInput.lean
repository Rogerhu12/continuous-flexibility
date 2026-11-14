module

public import ContinuousFlexibility.Analysis.N01ActualControlledRootFlow
public import ContinuousFlexibility.Analysis.N01RootLabels
public import ContinuousFlexibility.Analysis.RootNormalizedFlowCircleJets
public import ContinuousFlexibility.Analysis.RootScaledInverseCoordinate

/-!
# The two actual root inverse inputs on one common neighborhood

The Boolean endpoint selects the actual root, its inward radial
orientation, and the actual left or right angular label. Both ends use
the same controlled flow construction and the positive sqrt(δ) parameter
scaling. The common low order and derivative loss precede every endpoint;
the collar scale and numerical constants precede every state.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

local notation "rootInputBox" =>
  Set.prod (Icc (0 : ℝ) 1) (Set.prod (Icc (-1 : ℝ) 1) (Icc (-Real.pi) Real.pi))

def N01ControlledRootInputAtState
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (m : ℕ) (rightEnd : Bool) (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (κ δ Λ : ℝ) (loss : ℕ) (B : ℕ → ℝ) (z : AnnularState S × ℝ) : Prop :=
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let d := localizedRootDrift D S C r σ hR z
  let c := localizedRootSpeed D S C g r σ hR z
  N04FlowAngularControl (rootRescaledField d c δ) Λ ∧
    ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (rootRescaledField d c δ) Θ ∧
      let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
      ContDiff ℝ ∞ G ∧
        (∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi) ∧
        (∀ θ, G (0, 0, θ) = n01RootLabel S C z m rightEnd θ) ∧
        (∀ θ, δ * Real.sqrt δ * κ / (if rightEnd then (6 : ℝ) else 3) ≤
          rootOddCoefficient G (0, θ)) ∧
        ∀ s : ℕ, CSBound s rootInputBox G
          (B s * (1 + pairGrading (stateGrading S) realGrading (s + loss)
            (z - (C.referenceState, 0))))

def N01ControlledRootInputFamily
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (rightEnd : Bool) (g : ℝ → ℝ)
    {R : ℝ} (hR : 0 < R) (κ δ Λ : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    N01ControlledRootInputAtState D S C m rightEnd g hR κ δ Λ loss B z

def N01ControlledRootInputData
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (rightEnd : Bool) : Prop :=
  ∃ g : ℝ → ℝ, ∃ R : ℝ, ∃ hR : 0 < R, ∃ κ : ℝ,
    ContDiff ℝ ∞ g ∧ 0 < g 0 ∧ 0 < κ ∧
    (∀ t : ℝ, -deriv D.w (n01ComponentRoot C m rightEnd +
      n01ComponentRootOrientation rightEnd * t) = t * g t) ∧
    N01ActualRootFieldGeometry D S C base ε
      (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) g hR ∧
    ∀ Λ : ℝ, 0 < Λ → ∃ δ : ℝ, ∃ B : ℕ → ℝ,
      0 < δ ∧ δ ≤ R / 4 ∧ δ ≤ 1 ∧ (∀ s, 0 < B s) ∧
      N01ControlledRootInputFamily D S C base loss ε m rightEnd g hR κ δ Λ B

private theorem rootInput_odd_lower_formula (rightEnd : Bool) (δ κ : ℝ) :
    δ * Real.sqrt δ * κ / (if rightEnd then (6 : ℝ) else 3) =
      ((2 : ℝ) / 3) * δ * Real.sqrt δ * κ *
        (if rightEnd then (1 / 4 : ℝ) else 1 / 2) := by
  cases rightEnd <;> norm_num <;> ring

private theorem n01_rootInput_of_actual_flow
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss low flowLoss labelLoss outLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {m : ℕ} {rightEnd : Bool} {g : ℝ → ℝ} {R κ δ Λ : ℝ} (hR : 0 < R)
    (hκ : 0 < κ) (hδ : 0 < δ) (hδone : δ ≤ 1) {A K B : ℕ → ℝ}
    (hbound : N04NormalizedFlowCircleBound (pairGrading (stateGrading S) realGrading)
      flowLoss labelLoss low outLoss A K Λ B)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (hlabel : RootLabelPointwiseJets (pairGrading (stateGrading S) realGrading)
      labelLoss K (z - (C.referenceState, 0)) (n01RootLabel S C z m rightEnd))
    (hlow : pairGrading (stateGrading S) realGrading low
      (z - (C.referenceState, 0)) ≤ 1)
    (hregular : ContDiff ℝ ∞ (localizedRootDrift D S C
        (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) hR z) ∧
      ContDiff ℝ ∞ (localizedRootSpeed D S C g
        (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) hR z))
    (hlower : ∀ q : PolarPoint, κ ≤ localizedRootSpeed D S C g
      (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) hR z q)
    (hcontrolled : RootControlledFlowAtState (pairGrading (stateGrading S) realGrading)
      flowLoss A (z - (C.referenceState, 0)) δ Λ
      (localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
        (n01ComponentRootOrientation rightEnd) hR z)
      (localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
        (n01ComponentRootOrientation rightEnd) hR z)) :
    N01ControlledRootInputAtState D S C m rightEnd g hR κ δ Λ outLoss B z := by
  let d := localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
    (n01ComponentRootOrientation rightEnd) hR z
  let c := localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
    (n01ComponentRootOrientation rightEnd) hR z
  obtain ⟨hcontrol, Θ, hΘ, hforward⟩ := hcontrolled
  have hp := periodic_localizedRootFields hS C g (n01ComponentRoot C m rightEnd)
    (n01ComponentRootOrientation rightEnd) hR z
  have hh := n01RootLabel_contDiff hS hT hN hz hs m rightEnd
  have hperiod := n01RootLabel_period_add hN hz hs m rightEnd
  have hG := rootScaledInverseCoordinate_regular hregular.1 hregular.2
    hp.1 hp.2 hΘ hh hperiod (Real.sqrt δ)
  refine ⟨hcontrol, Θ, hΘ, hG.1, hG.2, ?_, ?_, ?_⟩
  · intro θ
    exact (rootScaledInverseCoordinate_zero_and_odd hregular.1 hregular.2
      hp.1 hp.2 hΘ hh (Real.sqrt δ) θ).1
  · intro θ
    have hlabelLower := (n01RootLabel_deriv_bounds hN hflow hz hs m rightEnd θ).1
    have hℓ : (0 : ℝ) ≤ if rightEnd then (1 / 4 : ℝ) else 1 / 2 := by
      cases rightEnd <;> norm_num
    exact (rootInput_odd_lower_formula rightEnd δ κ).trans_le
      (rootScaledInverseCoordinate_odd_lower hregular.1 hregular.2 hp.1 hp.2
        hΘ hh hδ.le hκ.le hℓ θ (hlower (0, θ)) hlabelLower)
  · intro s
    have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
    have hτ : |Real.sqrt δ| ≤ 1 := by
      simpa only [one_mul] using
        abs_signed_sqrt_le_one (η := (1 : ℝ)) hδ.le hδone (Or.inl rfl)
    exact csBound_rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd)
      (Real.sqrt δ)
      (hbound (z - (C.referenceState, 0)) hlow (rootRescaledField d c δ)
        (contDiff_rootRescaledField hregular.1 hregular.2 δ)
        (rootRescaledField_periodic hp.1 hp.2 δ) Θ hΘ hforward
        (n01RootLabel S C z m rightEnd) hh hlabel 1 ht (Real.sqrt δ) hτ s)

private theorem n01_exists_common_root_inputs_of_flowBound
    (hFlow : N04FlowJetsTarget)
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ, base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      OrdinaryFlowJacobianBounds S C newBase ε' ∧
      ∀ m : ℕ, ∀ rightEnd : Bool,
        N01ControlledRootInputData D S C newBase outLoss ε' m rightEnd := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨rootBase, flowLoss, η, hb, hη, hηε, hroots⟩ :=
    n01_exists_common_neighborhood_controlled_root_flows hFlow hS hT hN
  obtain ⟨labelLow, labelLoss, hlabels⟩ :=
    n01_rootLabels_displacement_fixed_loss hS hT hN hflow
  obtain ⟨inverseLow, outLoss, hnormalized⟩ :=
    n04FlowInverse_normalizedCircle_fixed_loss hp hI flowLoss labelLoss
  let low := max labelLow inverseLow
  let ε' : ℝ := min η (1 / 2)
  have hε' : 0 < ε' := lt_min hη (by norm_num)
  have hsmall : ε' ≤ η := min_le_left _ _
  have hεhalf : ε' ≤ 1 / 2 := min_le_right _ _
  have hU : stateNeighborhood S C (max rootBase low) ε' ⊆
      stateNeighborhood S C rootBase η :=
    stateNeighborhood_mono S C (Nat.le_max_left rootBase low) hsmall
  have hUold : stateNeighborhood S C (max rootBase low) ε' ⊆
      stateNeighborhood S C base ε :=
    hU.trans (stateNeighborhood_mono S C hb hηε)
  have hlow (z : AnnularState S × ℝ)
      (hz : z ∈ stateNeighborhood S C (max rootBase low) ε') :
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 := by
    have hz' := stateNeighborhood_mono S C (Nat.le_max_right rootBase low) le_rfl hz
    exact (pairGrading_displacement_le_two_mul_radius hz').trans (by linarith)
  refine ⟨max rootBase low, outLoss, ε', hb.trans (le_max_left _ _),
    hε', hsmall.trans hηε, (fun z hz => hflow z (hUold hz)), ?_⟩
  intro m rightEnd
  obtain ⟨K, hK, hlabel⟩ := hlabels m
  obtain ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, hgeometry, hlower, hcontrolled⟩ :=
    hroots m rightEnd
  refine ⟨g, R, hR, κ, hg, hg0, hκ, hdivide,
    ⟨fun z hz hs => hgeometry.1 z (hU hz) hs, hgeometry.2⟩, ?_⟩
  intro Λ hΛ
  obtain ⟨δ, A, hδ, hδR, hδone, hA, hcontrolled⟩ := hcontrolled Λ hΛ
  obtain ⟨B, hB, hbound⟩ := hnormalized A K hA hK Λ
  refine ⟨δ, B, hδ, hδR, hδone, hB, ?_⟩
  intro z hz hs
  have hlabelLow := (hp (le_max_left labelLow inverseLow)
    (z - (C.referenceState, 0))).trans (hlow z hz)
  have hinverseLow := (hp (le_max_right labelLow inverseLow)
    (z - (C.referenceState, 0))).trans (hlow z hz)
  exact n01_rootInput_of_actual_flow hS hT hN hflow hR hκ hδ hδone hbound
    (hUold hz) hs (hlabel z (hUold hz) hs hlabelLow rightEnd) hinverseLow
    (hgeometry.1 z (hU hz) hs).2 (hlower z (hU hz) hs) (hcontrolled z (hU hz) hs)

/-- Both actual endpoint inputs follow from N01 on one common smaller
neighborhood. The ordinary-return Jacobian bound is proved before it is used. -/
theorem n01_exists_common_root_inputs
    (hFlow : N04FlowJetsTarget)
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ, base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      OrdinaryFlowJacobianBounds S C newBase ε' ∧
      ∀ m : ℕ, ∀ rightEnd : Bool,
        N01ControlledRootInputData D S C newBase outLoss ε' m rightEnd := by
  obtain ⟨flowBase, η, hb, hη, hηε, hflow⟩ := exists_ordinaryFlowJacobianBounds_of_n01 hT hN
  have hN' := n01Properties_restrict hT hN hb le_rfl hη hηε
  obtain ⟨newBase, outLoss, ε', hb', hε', hsmall, hflow', hroots⟩ :=
    n01_exists_common_root_inputs_of_flowBound hFlow hS hT hN' hflow
  exact ⟨newBase, outLoss, ε', hb.trans hb', hε', hsmall.trans hηε, hflow', hroots⟩

end ContinuousFlexibility.Analysis
