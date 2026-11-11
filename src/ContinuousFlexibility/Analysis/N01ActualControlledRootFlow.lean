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

theorem n01_exists_actual_controlled_root_flows
    (hFlow : N04FlowJetsTarget)
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∀ m : ℕ, ∀ rightEnd : Bool,
      let r := n01ComponentRoot C m rightEnd
      let σ := n01ComponentRootOrientation rightEnd
      ∃ g : ℝ → ℝ, ∃ R : ℝ, ∃ hR : 0 < R, ∃ κ : ℝ,
        ContDiff ℝ ∞ g ∧ 0 < g 0 ∧ 0 < κ ∧
        (∀ t : ℝ, -deriv D.w (r + σ * t) = t * g t) ∧
        N01ActualRootFieldGeometry D S C base ε r σ g hR ∧
        (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
          ∀ q : PolarPoint, κ ≤ localizedRootSpeed D S C g r σ hR z q) ∧
        ∀ Λ : ℝ, 0 < Λ → ∃ δ : ℝ, ∃ B : ℕ → ℝ,
          0 < δ ∧ δ ≤ R / 4 ∧ δ ≤ 1 ∧ (∀ n, 0 < B n) ∧
          ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
          pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
          N04FlowAngularControl
            (rootRescaledField (localizedRootDrift D S C r σ hR z)
              (localizedRootSpeed D S C g r σ hR z) δ) Λ ∧
          ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
            N04FlowEquations
              (rootRescaledField (localizedRootDrift D S C r σ hR z)
                (localizedRootSpeed D S C g r σ hR z) δ) Θ ∧
            N04FlowJetBounds (pairGrading (stateGrading S) realGrading)
              outLoss B (z - (C.referenceState, 0)) 1 Λ Θ := by
  obtain ⟨low, outLoss, hcontrolled⟩ := n01_exists_controlled_root_flow hFlow hS hT hN
  refine ⟨low, outLoss, ?_⟩
  intro m rightEnd
  dsimp only
  obtain ⟨hr, hzero, hsign⟩ := n01_component_root_data hN m rightEnd
  have hσ := n01ComponentRootOrientation_eq rightEnd
  obtain ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, hphysical, ⟨j, hcell⟩, hstrip, hlower⟩ :=
    n01_exists_actual_root_coefficient_strip hS hT hN hr hzero hsign hσ
  have hgeometry : N01ActualRootFieldGeometry D S C base ε
      (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) g hR := by
    refine ⟨?_, fun z => periodic_localizedRootFields hS C g _ _ hR z⟩
    intro z hz hs
    exact ⟨hstrip z hz hs,
      contDiff_localizedRootFields_of_n01 hS hT hN hg hR (hstrip z hz hs)⟩
  refine ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, hgeometry, hlower, ?_⟩
  intro Λ hΛ
  exact hcontrolled (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd)
    g R hσ hR hg hphysical j hcell hstrip Λ hΛ

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
      let r := n01ComponentRoot C m rightEnd
      let σ := n01ComponentRootOrientation rightEnd
      ∃ g : ℝ → ℝ, ∃ R : ℝ, ∃ hR : 0 < R, ∃ κ : ℝ,
        ContDiff ℝ ∞ g ∧ 0 < g 0 ∧ 0 < κ ∧
        (∀ t : ℝ, -deriv D.w (r + σ * t) = t * g t) ∧
        N01ActualRootFieldGeometry D S C newBase ε' r σ g hR ∧
        (∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
          ∀ q : PolarPoint, κ ≤ localizedRootSpeed D S C g r σ hR z q) ∧
        ∀ Λ : ℝ, 0 < Λ → ∃ δ : ℝ, ∃ B : ℕ → ℝ,
          0 < δ ∧ δ ≤ R / 4 ∧ δ ≤ 1 ∧ (∀ n, 0 < B n) ∧
          ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
          N04FlowAngularControl
            (rootRescaledField (localizedRootDrift D S C r σ hR z)
              (localizedRootSpeed D S C g r σ hR z) δ) Λ ∧
          ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
            N04FlowEquations
              (rootRescaledField (localizedRootDrift D S C r σ hR z)
                (localizedRootSpeed D S C g r σ hR z) δ) Θ ∧
            N04FlowJetBounds (pairGrading (stateGrading S) realGrading)
              outLoss B (z - (C.referenceState, 0)) 1 Λ Θ := by
  obtain ⟨low, outLoss, hroots⟩ := n01_exists_actual_controlled_root_flows hFlow hS hT hN
  let ε' : ℝ := min ε (1 / 2)
  have hε' : 0 < ε' := lt_min hN.2.1 (by norm_num)
  have hεε : ε' ≤ ε := min_le_left _ _
  have hεhalf : ε' ≤ 1 / 2 := min_le_right _ _
  have hU : stateNeighborhood S C (max base low) ε' ⊆ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C (Nat.le_max_left base low) hεε
  have hlow (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C (max base low) ε') :
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 := by
    have hzlow : z ∈ stateNeighborhood S C low ε' :=
      stateNeighborhood_mono S C (Nat.le_max_right base low) le_rfl hz
    exact (pairGrading_displacement_le_two_mul_radius hzlow).trans (by linarith)
  refine ⟨max base low, outLoss, ε', Nat.le_max_left base low, hε', hεε, ?_⟩
  intro m rightEnd
  dsimp only
  obtain ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, hgeometry, hlower, hcontrolled⟩ :=
    hroots m rightEnd
  refine ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, ?_, ?_, ?_⟩
  · exact ⟨fun z hz hs => hgeometry.1 z (hU hz) hs, hgeometry.2⟩
  · intro z hz hsector
    exact hlower z (hU hz) hsector
  · intro Λ hΛ
    obtain ⟨δ, B, hδ, hδR, hδone, hB, hflow⟩ := hcontrolled Λ hΛ
    refine ⟨δ, B, hδ, hδR, hδone, hB, ?_⟩
    intro z hz hsector
    exact hflow z (hU hz) hsector (hlow z hz)

end ContinuousFlexibility.Analysis
