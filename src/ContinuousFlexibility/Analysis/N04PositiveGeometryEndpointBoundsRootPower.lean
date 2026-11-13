import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsRootShiftPower

/-!
# Distributed angular powers for the actual finite radial root inputs

The finite radial prefix is absorbed into one fixed interpolation loss.
Consequently its angular orders, and not the number of radial factors,
determine the spatial scale in each product. The same base is selected
before every parameter prefix. The input maps are the literal four
normalized height fields multiplied by the original scalar parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04PositiveRootPowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- One base and one loss suffice for every parameter order of a fixed
finite radial prefix. The original `H^(3/4)` gain is kept even at zero
parameter order. -/
theorem n04PositiveGeometry_rootHeightInputs_finiteRadial_power
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (hE : ∀ r ∈ radialCore D, 1 ≤ T.E0 r)
    (x0 : AnnularState S) (N requestedBase : ℕ) :
    ∃ B loss : ℕ, requestedBase ≤ B ∧ ∀ K s : ℕ,
      ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ i : Fin 4, ∀ a : ℕ, a ≤ N → ∀ b : ℕ, b ≤ s →
      ∀ p ∈ annularOpen D, ∀ U : Set (AnnularState S × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 *
        mixedDerivative a b (n06RootNormalizedHeightFields D S z.1.1 i) p),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ U, |z.2| ≤ 1 →
      pairGrading (stateGrading S) realGrading B (z - (x0, 0)) ≤ 1 →
      ∀ v : Fin k → (AnnularState S × ℝ),
      (∀ j, pairGrading (stateGrading S) realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (stateGrading S) realGrading (s + loss) (z - (x0, 0)) ≤ R →
      (∀ j, pairGrading (stateGrading S) realGrading (s + loss) (v j) ≤ R) →
        |J.D k z v| ≤ C * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
  obtain ⟨B, loss, hB, hb⟩ :=
    n04PositiveGeometry_rootHeightInputs_finiteShift_power hD hT hS hE x0 N requestedBase
  refine ⟨B, loss, hB, fun K s => ?_⟩
  obtain ⟨C, A, hC, hA, hbound⟩ := hb K s
  refine ⟨C, A, hC, hA, ?_⟩
  intro i a ha b hbs q hq U J k hk z hz hzq hzlow v hv R hR hzR hvR
  exact hbound i a 0 (by omega) b hbs q hq U J k hk z hz hzq hzlow v hv R hR hzR hvR

end ContinuousFlexibility.Analysis
