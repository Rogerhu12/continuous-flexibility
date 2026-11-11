import ContinuousFlexibility.Analysis.N01ActualRootStrip
import ContinuousFlexibility.Analysis.N01ControlledRootFlow
import ContinuousFlexibility.Analysis.CanonicalVariationBounds

/-!
# A controlled actual root flow at both ends of every negative component

The common root strip and the actual cell are now constructed from the
frozen N01 and physical-space hypotheses. A single low order and loss
work for every component and both endpoint orientations. Each component
may have its own positive collar and numerical constants; their later
material-envelope absorption is separate from this construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The same fields chosen by the actual root construction retain their
proved common strip, global smoothness, and angular period. These facts
allow the genuine inverse-flow theorem to be applied outside the box
where quantitative bounds are requested. -/
def N01ActualRootFieldGeometry
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε r σ : ℝ) (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R) : Prop :=
  (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ R ∧
    ContDiff ℝ ∞ (localizedRootDrift D S C r σ hR z) ∧
    ContDiff ℝ ∞ (localizedRootSpeed D S C g r σ hR z)) ∧
  ∀ z : AnnularState S × ℝ,
    (∀ x, Function.Periodic
      (fun θ => localizedRootDrift D S C r σ hR z (x, θ)) Real.pi) ∧
    (∀ x, Function.Periodic
      (fun θ => localizedRootSpeed D S C g r σ hR z (x, θ)) Real.pi)

/-- The preceding quantitative construction, with its full root-choice
body named before any concrete existential is eliminated. -/
private def N01ControlledRootChoice
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low outLoss : ℕ) (ε : ℝ) : Prop :=
  ∀ r σ : ℝ, ∀ g : ℝ → ℝ, ∀ R : ℝ,
    (σ = 1 ∨ σ = -1) → ∀ hR : 0 < R, ContDiff ℝ ∞ g →
    Ioo ((r - R) - R) ((r + R) + R) ⊆ Ioo D.a D.b →
    ∀ m : ℕ, Ioo (r - R) (r + R) ⊆ D.cells m →
    (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R) →
    ∀ Λ : ℝ, 0 < Λ → ∃ δ : ℝ, ∃ B : ℕ → ℝ,
      0 < δ ∧ δ ≤ R / 4 ∧ δ ≤ 1 ∧ (∀ n, 0 < B n) ∧
      N01ControlledRootFlowBound D S C base low outLoss ε r σ g hR δ Λ B

private theorem n01_controlledRootChoice_of_properties
    (hFlow : N04FlowJetsTarget)
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, N01ControlledRootChoice D S C base low outLoss ε :=
  n01_exists_controlled_root_flow hFlow hS hT hN

private theorem n01_actualRootFieldGeometry_of_strip
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε r σ R : ℝ} {g : ℝ → ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hR : 0 < R) (hg : ContDiff ℝ ∞ g)
    (hstrip : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R) :
    N01ActualRootFieldGeometry D S C base ε r σ g hR := by
  refine ⟨?_, fun z => periodic_localizedRootFields hS C g r σ hR z⟩
  intro z hz hs
  exact ⟨hstrip z hz hs,
    contDiff_localizedRootFields_of_n01 hS hT hN hg hR (hstrip z hz hs)⟩

/-- The original full actual-root conclusion, including the common strip,
its positive speed and the actual flow. No geometric condition is added. -/
def N01ActualControlledRootData
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low outLoss : ℕ) (ε r σ : ℝ) : Prop :=
  ∃ g : ℝ → ℝ, ∃ R : ℝ, ∃ hR : 0 < R, ∃ κ : ℝ,
    ContDiff ℝ ∞ g ∧ 0 < g 0 ∧ 0 < κ ∧
    (∀ t : ℝ, -deriv D.w (r + σ * t) = t * g t) ∧
    N01ActualRootFieldGeometry D S C base ε r σ g hR ∧
    (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ q : PolarPoint, κ ≤ localizedRootSpeed D S C g r σ hR z q) ∧
    ∀ Λ : ℝ, 0 < Λ → ∃ δ : ℝ, ∃ B : ℕ → ℝ,
      0 < δ ∧ δ ≤ R / 4 ∧ δ ≤ 1 ∧ (∀ n, 0 < B n) ∧
      N01ControlledRootFlowBound D S C base low outLoss ε r σ g hR δ Λ B

private theorem n01_actualControlledRootData_of_choice
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss low outLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hcontrolled : N01ControlledRootChoice D S C base low outLoss ε)
    (m : ℕ) (rightEnd : Bool) :
    N01ActualControlledRootData D S C base low outLoss ε
      (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) := by
  obtain ⟨hr, hzero, hsign⟩ := n01_component_root_data hN m rightEnd
  have hσ := n01ComponentRootOrientation_eq rightEnd
  obtain ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, hphysical, ⟨j, hcell⟩, hstrip, hlower⟩ :=
    n01_exists_actual_root_coefficient_strip hS hT hN hr hzero hsign hσ
  exact ⟨g, R, hR, κ, hg, hg0, hκ, hdivide,
    n01_actualRootFieldGeometry_of_strip hS hT hN hR hg hstrip, hlower,
    fun Λ hΛ => hcontrolled (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) g R hσ hR hg hphysical j hcell hstrip Λ hΛ⟩

theorem n01_exists_actual_controlled_root_flows
    (hFlow : N04FlowJetsTarget)
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∀ m : ℕ, ∀ rightEnd : Bool,
      N01ActualControlledRootData D S C base low outLoss ε
        (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) := by
  obtain ⟨low, outLoss, hcontrolled⟩ := n01_controlledRootChoice_of_properties hFlow hS hT hN
  exact ⟨low, outLoss, fun m rightEnd =>
    n01_actualControlledRootData_of_choice hS hT hN hcontrolled m rightEnd⟩

/-- The actual controlled-flow body after the low norm has been absorbed
into a single state neighborhood. -/
def N01CommonControlledRootFlowBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base outLoss : ℕ) (ε r σ : ℝ) (g : ℝ → ℝ)
    {R : ℝ} (hR : 0 < R) (δ Λ : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    RootControlledFlowAtState (pairGrading (stateGrading S) realGrading) outLoss B
      (z - (C.referenceState, 0)) δ Λ
      (localizedRootDrift D S C r σ hR z) (localizedRootSpeed D S C g r σ hR z)

def N01CommonControlledRootData
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base outLoss : ℕ) (ε r σ : ℝ) : Prop :=
  ∃ g : ℝ → ℝ, ∃ R : ℝ, ∃ hR : 0 < R, ∃ κ : ℝ,
    ContDiff ℝ ∞ g ∧ 0 < g 0 ∧ 0 < κ ∧
    (∀ t : ℝ, -deriv D.w (r + σ * t) = t * g t) ∧
    N01ActualRootFieldGeometry D S C base ε r σ g hR ∧
    (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ q : PolarPoint, κ ≤ localizedRootSpeed D S C g r σ hR z q) ∧
    ∀ Λ : ℝ, 0 < Λ → ∃ δ : ℝ, ∃ B : ℕ → ℝ,
      0 < δ ∧ δ ≤ R / 4 ∧ δ ≤ 1 ∧ (∀ n, 0 < B n) ∧
      N01CommonControlledRootFlowBound D S C base outLoss ε r σ g hR δ Λ B

private theorem n01_actualRootFieldGeometry_restrict
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base newBase : ℕ} {ε η r σ R : ℝ} {g : ℝ → ℝ} (hR : 0 < R)
    (hU : stateNeighborhood S C newBase η ⊆ stateNeighborhood S C base ε)
    (hg : N01ActualRootFieldGeometry D S C base ε r σ g hR) :
    N01ActualRootFieldGeometry D S C newBase η r σ g hR :=
  ⟨fun z hz hs => hg.1 z (hU hz) hs, hg.2⟩

private theorem n01_commonControlledRootFlowBound_of_restrict
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base newBase low outLoss : ℕ} {ε η r σ R δ Λ : ℝ} {g : ℝ → ℝ} {B : ℕ → ℝ}
    (hR : 0 < R)
    (hU : stateNeighborhood S C newBase η ⊆ stateNeighborhood S C base ε)
    (hlow : ∀ z ∈ stateNeighborhood S C newBase η,
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1)
    (hflow : N01ControlledRootFlowBound D S C base low outLoss ε r σ g hR δ Λ B) :
    N01CommonControlledRootFlowBound D S C newBase outLoss η r σ g hR δ Λ B :=
  fun z hz hs => hflow z (hU hz) hs (hlow z hz)

private theorem n01_actualControlledRootData_restrict
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base newBase low outLoss : ℕ} {ε η r σ : ℝ}
    (hU : stateNeighborhood S C newBase η ⊆ stateNeighborhood S C base ε)
    (hlow : ∀ z ∈ stateNeighborhood S C newBase η,
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1)
    (hdata : N01ActualControlledRootData D S C base low outLoss ε r σ) :
    N01CommonControlledRootData D S C newBase outLoss η r σ := by
  obtain ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, hgeometry, hlower, hcontrolled⟩ := hdata
  refine ⟨g, R, hR, κ, hg, hg0, hκ, hdivide,
    n01_actualRootFieldGeometry_restrict hR hU hgeometry,
    fun z hz hs => hlower z (hU hz) hs, ?_⟩
  intro Λ hΛ
  obtain ⟨δ, B, hδ, hδR, hδone, hB, hflow⟩ := hcontrolled Λ hΛ
  exact ⟨δ, B, hδ, hδR, hδone, hB,
    n01_commonControlledRootFlowBound_of_restrict hR hU hlow hflow⟩

private theorem two_mul_le_one_of_le_half {η : ℝ} (hη : η ≤ 1 / 2) :
    2 * η ≤ 1 := by linarith

private theorem n01_actualRoot_common_neighborhood
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base low : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ newBase : ℕ, ∃ η : ℝ, base ≤ newBase ∧ 0 < η ∧ η ≤ ε ∧
      stateNeighborhood S C newBase η ⊆ stateNeighborhood S C base ε ∧
      ∀ z ∈ stateNeighborhood S C newBase η,
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 := by
  let η : ℝ := min ε (1 / 2)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hηhalf : 2 * η ≤ 1 := two_mul_le_one_of_le_half (min_le_right ε (1 / 2))
  have hU : stateNeighborhood S C (max base low) η ⊆ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C (Nat.le_max_left base low) hηε
  refine ⟨max base low, η, Nat.le_max_left base low, hη, hηε, hU, ?_⟩
  intro z hz
  have hzlow : z ∈ stateNeighborhood S C low η :=
    stateNeighborhood_mono S C (Nat.le_max_right base low) le_rfl hz
  exact (pairGrading_displacement_le_two_mul_radius hzlow).trans hηhalf

/-- One genuine state neighborhood suffices for every actual root.
Its base order and radius are chosen before the component and endpoint. -/
theorem n01_exists_common_neighborhood_controlled_root_flows
    (hFlow : N04FlowJetsTarget)
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ, base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∀ rightEnd : Bool,
        N01CommonControlledRootData D S C newBase outLoss ε'
          (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) := by
  obtain ⟨low, outLoss, hroots⟩ := n01_exists_actual_controlled_root_flows hFlow hS hT hN
  obtain ⟨newBase, η, hb, hη, hηε, hU, hlow⟩ :=
    n01_actualRoot_common_neighborhood S C base low hN.2.1
  exact ⟨newBase, outLoss, η, hb, hη, hηε, fun m rightEnd =>
    n01_actualControlledRootData_restrict hU hlow (hroots m rightEnd)⟩

end ContinuousFlexibility.Analysis
