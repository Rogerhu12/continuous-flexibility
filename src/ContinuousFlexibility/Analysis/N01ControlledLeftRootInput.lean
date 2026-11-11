import ContinuousFlexibility.Analysis.N01ActualControlledRootFlow
import ContinuousFlexibility.Analysis.N01LeftChartJets
import ContinuousFlexibility.Analysis.RootNormalizedFlowCircleJets
import ContinuousFlexibility.Analysis.RootScaledInverseCoordinate

/-!
# The actual left root inverse on one common neighborhood

The root coefficients and the flow are the genuinely constructed N01
objects. The angular normalization is the actual stateLeftChart. Its
linear circle estimate and the actual inverse-flow estimate give all
ordinary input jets before the root substitution. The positive root
coefficient is computed from the same flow, with the exact sqrt(δ)
normalization. Identification with a global negative atlas is separate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

local notation "rootInputBox" =>
  Set.prod (Icc (0 : ℝ) 1) (Set.prod (Icc (-1 : ℝ) 1) (Icc (-Real.pi) Real.pi))

def N01ControlledLeftRootInputAtState
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (m : ℕ) (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (κ δ Λ : ℝ) (loss : ℕ) (B : ℕ → ℝ) (z : AnnularState S × ℝ) : Prop :=
  let d := localizedRootDrift D S C (C.left m) 1 hR z
  let c := localizedRootSpeed D S C g (C.left m) 1 hR z
  N04FlowAngularControl (rootRescaledField d c δ) Λ ∧
    ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (rootRescaledField d c δ) Θ ∧
      let G := rootScaledInverseCoordinate Θ (stateLeftChart S z.1 m) (Real.sqrt δ)
      ContDiff ℝ ∞ G ∧
        (∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi) ∧
        (∀ θ, G (0, 0, θ) = stateLeftChart S z.1 m θ) ∧
        (∀ θ, δ * Real.sqrt δ * κ / 3 ≤ rootOddCoefficient G (0, θ)) ∧
        ∀ s : ℕ, CSBound s rootInputBox G
          (B s * (1 + pairGrading (stateGrading S) realGrading (s + loss)
            (z - (C.referenceState, 0))))

def N01ControlledLeftRootInputFamily
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (g : ℝ → ℝ)
    {R : ℝ} (hR : 0 < R) (κ δ Λ : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    N01ControlledLeftRootInputAtState D S C m g hR κ δ Λ loss B z

private theorem n01_leftRootInput_of_actual_flow
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss low flowLoss outLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    {m : ℕ} {g : ℝ → ℝ} {R κ δ Λ L : ℝ} (hR : 0 < R)
    (hκ : 0 < κ) (hδ : 0 < δ) (hδone : δ ≤ 1) {A B : ℕ → ℝ}
    (hleft : N01LeftChartPairJetBound S C L)
    (hbound : N04NormalizedFlowCircleBound (pairGrading (stateGrading S) realGrading)
      flowLoss 1 low outLoss A (fun _ => L) Λ B)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (hlow : pairGrading (stateGrading S) realGrading low
      (z - (C.referenceState, 0)) ≤ 1)
    (hregular : ContDiff ℝ ∞ (localizedRootDrift D S C (C.left m) 1 hR z) ∧
      ContDiff ℝ ∞ (localizedRootSpeed D S C g (C.left m) 1 hR z))
    (hlower : ∀ q : PolarPoint, κ ≤ localizedRootSpeed D S C g (C.left m) 1 hR z q)
    (hcontrol : N04FlowAngularControl
      (rootRescaledField (localizedRootDrift D S C (C.left m) 1 hR z)
        (localizedRootSpeed D S C g (C.left m) 1 hR z) δ) Λ)
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hΘ : N04FlowEquations
      (rootRescaledField (localizedRootDrift D S C (C.left m) 1 hR z)
        (localizedRootSpeed D S C g (C.left m) 1 hR z) δ) Θ)
    (hforward : N04FlowJetBounds (pairGrading (stateGrading S) realGrading)
      flowLoss A (z - (C.referenceState, 0)) 1 Λ Θ) :
    N01ControlledLeftRootInputAtState D S C m g hR κ δ Λ outLoss B z := by
  let d := localizedRootDrift D S C (C.left m) 1 hR z
  let c := localizedRootSpeed D S C g (C.left m) 1 hR z
  have hp := periodic_localizedRootFields hS C g (C.left m) 1 hR z
  have hh := contDiff_stateLeftChart hS z.1 m
  have hperiod := stateLeftChart_period_add hS z.1 m
  have hG := rootScaledInverseCoordinate_regular hregular.1 hregular.2
    hp.1 hp.2 hΘ hh hperiod (Real.sqrt δ)
  refine ⟨hcontrol, Θ, hΘ, hG.1, hG.2, ?_, ?_, ?_⟩
  · intro θ
    exact (rootScaledInverseCoordinate_zero_and_odd hregular.1 hregular.2
      hp.1 hp.2 hΘ hh (Real.sqrt δ) θ).1
  · intro θ
    have hLθ : (1 / 2 : ℝ) ≤ deriv (stateLeftChart S z.1 m) θ :=
      (hN.2.2.2.2.2.2.2.1 z hz hs m θ).1
    have hb := rootScaledInverseCoordinate_odd_lower hregular.1 hregular.2 hp.1 hp.2
      hΘ hh hδ.le hκ.le (by norm_num : (0 : ℝ) ≤ 1 / 2) θ (hlower (0, θ)) hLθ
    have he : δ * Real.sqrt δ * κ / 3 =
        ((2 : ℝ) / 3) * δ * Real.sqrt δ * κ * (1 / 2) := by ring
    exact he.trans_le hb
  · intro s
    have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
    have hτ : |Real.sqrt δ| ≤ 1 := by
      simpa only [one_mul] using
        abs_signed_sqrt_le_one (η := (1 : ℝ)) hδ.le hδone (Or.inl rfl)
    exact csBound_rootScaledInverseCoordinate Θ (stateLeftChart S z.1 m) (Real.sqrt δ)
      (hbound (z - (C.referenceState, 0)) hlow (rootRescaledField d c δ)
        (contDiff_rootRescaledField hregular.1 hregular.2 δ)
        (rootRescaledField_periodic hp.1 hp.2 δ) Θ hΘ hforward
        (stateLeftChart S z.1 m) hh (fun n θ => hleft n m z θ) 1 ht (Real.sqrt δ) hτ s)

/-- The actual normalized inverse inputs at every left component root
have one common state neighborhood and one fixed loss. The collar and
all order constants may depend on the component but precede the state. -/
theorem n01_exists_common_left_root_inputs
    (hFlow : N04FlowJetsTarget)
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ, base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∃ g : ℝ → ℝ, ∃ R : ℝ, ∃ hR : 0 < R, ∃ κ : ℝ,
        ContDiff ℝ ∞ g ∧ 0 < g 0 ∧ 0 < κ ∧
        (∀ t : ℝ, -deriv D.w (C.left m + t) = t * g t) ∧
        N01ActualRootFieldGeometry D S C newBase ε' (C.left m) 1 g hR ∧
        ∀ Λ : ℝ, 0 < Λ → ∃ δ : ℝ, ∃ B : ℕ → ℝ,
          0 < δ ∧ δ ≤ R / 4 ∧ δ ≤ 1 ∧ (∀ s, 0 < B s) ∧
          N01ControlledLeftRootInputFamily D S C newBase outLoss ε'
            m g hR κ δ Λ B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨rootBase, flowLoss, η, hb, hη, hηε, hroots⟩ :=
    n01_exists_common_neighborhood_controlled_root_flows hFlow hS hT hN
  obtain ⟨low, outLoss, hnormalized⟩ :=
    n04FlowInverse_normalizedCircle_fixed_loss hp hI flowLoss 1
  obtain ⟨L, hL, hleft⟩ := n01_stateLeftChart_pairJets hS hT hN
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
    have hz' : z ∈ stateNeighborhood S C low ε' :=
      stateNeighborhood_mono S C (Nat.le_max_right rootBase low) le_rfl hz
    exact (pairGrading_displacement_le_two_mul_radius hz').trans (by linarith)
  refine ⟨max rootBase low, outLoss, ε', hb.trans (Nat.le_max_left rootBase low),
    hε', hsmall.trans hηε, ?_⟩
  intro m
  obtain ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, hgeometry, hlower, hcontrolled⟩ := hroots m false
  refine ⟨g, R, hR, κ, hg, hg0, hκ, ?_, ?_, ?_⟩
  · intro t
    simpa only [n01ComponentRoot, n01ComponentRootOrientation, Bool.false_eq_true,
      ↓reduceIte, one_mul] using hdivide t
  · exact ⟨fun z hz hs => hgeometry.1 z (hU hz) hs, hgeometry.2⟩
  · intro Λ hΛ
    obtain ⟨δ, A, hδ, hδR, hδone, hA, hflow⟩ := hcontrolled Λ hΛ
    obtain ⟨B, hB, hbound⟩ := hnormalized A (fun _ => L) hA (fun _ => hL) Λ
    refine ⟨δ, B, hδ, hδR, hδone, hB, ?_⟩
    intro z hz hs
    obtain ⟨hcontrol, Θ, hΘ, hforward⟩ := hflow z (hU hz) hs
    exact n01_leftRootInput_of_actual_flow hS hN hR hκ hδ hδone hleft hbound
      (hUold hz) hs (hlow z hz) (hgeometry.1 z (hU hz) hs).2
      (hlower z (hU hz) hs) hcontrol Θ hΘ hforward

end ContinuousFlexibility.Analysis
