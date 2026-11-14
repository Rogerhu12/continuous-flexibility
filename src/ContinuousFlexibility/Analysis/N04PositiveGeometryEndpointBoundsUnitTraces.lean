import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsUnitModel
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFormulaAlgebra

/-!
# Literal finite traces of the same unit model

The original even traces through order four and odd traces through
order three are precisely the eight differential formulas. The equality
uses the actual flow at the current state and removes only the harmless
coefficient localization at its zero axis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

def n04PositiveGeometry_rootUnitTrace (G : ℝ × ℝ × ℝ → ℝ) : Fin 8 → ℝ → ℝ :=
  ![radialBoundaryJet (extendedRootEven G) 0 1,
    radialBoundaryJet (extendedRootEven G) 0 2,
    radialBoundaryJet (extendedRootEven G) 0 3,
    radialBoundaryJet (extendedRootEven G) 0 4,
    radialBoundaryJet (extendedRootOddCoefficient G) 0 0,
    radialBoundaryJet (extendedRootOddCoefficient G) 0 1,
    radialBoundaryJet (extendedRootOddCoefficient G) 0 2,
    radialBoundaryJet (extendedRootOddCoefficient G) 0 3]

theorem N04bRootCoordinateProperties.n04PositiveGeometry_unitTraces_eq
    {d c : PolarPoint → ℝ} {β : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (P : N04bRootCoordinateProperties d c β Φ R σ G)
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c) (j : Fin 8) :
    n04PositiveGeometry_rootUnitTrace G j =
      n04PositiveGeometry_boundaryFormula j (n06RootBoundaryInputs d c β) := by
  have h := P.n06_boundary_finite_formulas hd hc
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2

theorem n04PositiveGeometry_actual_unitRootTrace_formula
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) {R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m side)
      (n01ComponentRootOrientation side) R)
    {δ : ℝ} (hδ : δ ≠ 0) (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hΘ : N04FlowEquations (rootRescaledField
      (localizedRootDrift D S C (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR z)
      (localizedRootSpeed D S C g (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR z) δ) Θ) (j : Fin 8) :
    n04PositiveGeometry_rootUnitTrace
      (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) (n01RootLabel S C z m side)) j =
    n04PositiveGeometry_boundaryFormula j (n06RootBoundaryInputs
      (orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z)
        (n01ComponentRoot C m side) (n01ComponentRootOrientation side))
      (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side)) (n01RootLabel S C z m side)) := by
  have P := n04PositiveGeometry_actual_unitRootCoordinate_properties hT hS hN hflow
    hz hs m side g hg hR hstrip hδ Θ hΘ
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN hg hR hstrip
  have h := P.n04PositiveGeometry_unitTraces_eq hregular.1 hregular.2 j
  rw [n04PositiveGeometry_localizedRoot_boundaryInputs_eq] at h
  exact h

end ContinuousFlexibility.Analysis
