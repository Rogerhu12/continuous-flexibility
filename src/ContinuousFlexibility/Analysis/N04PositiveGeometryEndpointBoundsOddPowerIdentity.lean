module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsOddTraces

/-!
# Positive powers of the actual unit odd trace

At a fixed state one flow is used for every angle. Its first four odd
radial traces agree with the literal boundary formulas, so every real
power through radial order three has the already constructed actual
trace. No parameter regularity of the chosen flow is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04OddPowerIdentityStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PositiveGeometry_rootPowerTrace_congr_of_le
    (γ : ℝ) (n : ℕ) {v w : ℕ → ℝ} (h : ∀ j, j ≤ n → v j = w j) :
    n04PositiveGeometry_rootPowerTrace γ n v =
      n04PositiveGeometry_rootPowerTrace γ n w := by
  unfold n04PositiveGeometry_rootPowerTrace
  apply Finset.sum_congr rfl
  intro c _
  have hp : (∏ i, v (c.partSize i)) = ∏ i, w (c.partSize i) := by
    apply Finset.prod_congr rfl
    intro i _
    exact h (c.partSize i) (c.partSize_le i)
  rw [h 0 (Nat.zero_le n), hp]

theorem n04PositiveGeometry_rootUnitTrace_odd
    (G : ℝ × ℝ × ℝ → ℝ) (n : ℕ) (hn : n ≤ 3) :
    n04PositiveGeometry_rootUnitTrace G ⟨4 + n, by omega⟩ =
      radialBoundaryJet (extendedRootOddCoefficient G) 0 n := by
  have h (j : Fin 4) :
      n04PositiveGeometry_rootUnitTrace G ⟨4 + j.val, by omega⟩ =
        radialBoundaryJet (extendedRootOddCoefficient G) 0 j.val := by
    fin_cases j <;> rfl
  exact h ⟨n, by omega⟩

/-- All eight model traces are the actual state formulas as functions
of the angle, with a single fixed flow at that state. -/
theorem n04PositiveGeometry_actual_unitRootTrace_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (side : Bool) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    {R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g
      (stateProfile D S C (liftSectorParameter S C z).1)
      (stateHeight D S C (liftSectorParameter S C z))
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) R)
    {δ : ℝ} (hδ : δ ≠ 0) (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hΘ : N04FlowEquations (rootRescaledField
      (localizedRootDrift D S C (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C z))
      (localizedRootSpeed D S C g (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C z)) δ) Θ)
    (j : Fin 8) :
    n04PositiveGeometry_rootUnitTrace
      (rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
        (n01RootLabel S C (liftSectorParameter S C z) m side)) j =
      fun θ => n04PositiveGeometry_rootBoundaryFormula D S C g m side j (z, θ) := by
  have hmodel := n04PositiveGeometry_actual_unitRootTrace_formula hT hS hN hflow
    (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z) m side g hg hR hstrip hδ Θ hΘ j
  have hinputs := congrArg
    (fun v : N06RootBoundaryInputs => n04PositiveGeometry_boundaryFormula j v)
    (n04PositiveGeometry_rootBoundaryInput_eq D S C g m side z)
  exact hmodel.trans hinputs.symm

theorem n04PositiveGeometry_actual_oddTrace_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (side : Bool) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    {R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g
      (stateProfile D S C (liftSectorParameter S C z).1)
      (stateHeight D S C (liftSectorParameter S C z))
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) R)
    {δ : ℝ} (hδ : δ ≠ 0) (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hΘ : N04FlowEquations (rootRescaledField
      (localizedRootDrift D S C (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C z))
      (localizedRootSpeed D S C g (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C z)) δ) Θ)
    (n : ℕ) (hn : n ≤ 3) :
    radialBoundaryJet (extendedRootOddCoefficient
      (rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
        (n01RootLabel S C (liftSectorParameter S C z) m side))) 0 n =
      fun θ => n04PositiveGeometry_rootOddTrace D S C g m side n (z, θ) := by
  have hunit := n04PositiveGeometry_actual_unitRootTrace_eq hT hS hN hflow hz
    m side g hg hR hstrip hδ Θ hΘ ⟨4 + n, by omega⟩
  have hodd := congrArg (fun f : ((StateDirections S × ℝ) × ℝ) → ℝ =>
    fun θ => f (z, θ)) (n04PositiveGeometry_rootOddTrace_eq D S C g m side n hn)
  exact (n04PositiveGeometry_rootUnitTrace_odd _ n hn).symm.trans
    (hunit.trans hodd.symm)

/-- The identity is a function equality before any angular derivative
is taken. The exponent is arbitrary and the radial budget is three. -/
theorem n04PositiveGeometry_actual_oddPowerTrace_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (side : Bool) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    {R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g
      (stateProfile D S C (liftSectorParameter S C z).1)
      (stateHeight D S C (liftSectorParameter S C z))
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) R)
    {δ : ℝ} (hδ : δ ≠ 0) (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hΘ : N04FlowEquations (rootRescaledField
      (localizedRootDrift D S C (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C z))
      (localizedRootSpeed D S C g (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C z)) δ) Θ)
    (γ : ℝ) (n : ℕ) (hn : n ≤ 3) :
    radialBoundaryJet (fun p => extendedRootOddCoefficient
      (rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
        (n01RootLabel S C (liftSectorParameter S C z) m side)) p ^ γ) 0 n =
      fun θ => n04PositiveGeometry_rootOddPowerTrace D S C g m side γ n (z, θ) := by
  have P := n04PositiveGeometry_actual_unitRootCoordinate_properties hT hS hN hflow
    (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z) m side g hg hR hstrip hδ Θ hΘ
  have htrace (j : ℕ) (hj : j ≤ n) :=
    n04PositiveGeometry_actual_oddTrace_eq hT hS hN hflow hz m side g hg hR hstrip
      hδ Θ hΘ j (hj.trans hn)
  funext θ
  have hpos : 0 < extendedRootOddCoefficient
      (rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
        (n01RootLabel S C (liftSectorParameter S C z) m side)) (0, θ) := by
    rw [extendedRootOddCoefficient_of_nonneg _ (le_refl (0 : ℝ))]
    exact P.odd_positive θ
  have hpower := n04PositiveGeometry_radialBoundaryJet_rpow
    P.n06_extendedOdd_smooth hpos γ n
  exact hpower.trans (n04PositiveGeometry_rootPowerTrace_congr_of_le γ n
    (fun j hj => congrFun (htrace j hj) θ))

end ContinuousFlexibility.Analysis
