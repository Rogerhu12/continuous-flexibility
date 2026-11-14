module

public import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData

/-!
# The actual divided coefficients at the reference

The stored divided field is the literal quotient of a coefficient minus
its reference value. At the reference its numerator vanishes identically,
including outside the open piece. Thus all three reference divided atoms
have genuine zero spatial jets, without any endpoint or final-estimate
hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

theorem n04bWithInteriorDivision_reference_dividedAtom_zero
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (K : CanonicalData S) (m : ℕ) (v : Atom)
    (hv : v = .dividedA ∨ v = .dividedB ∨ v = .dividedC) :
    atom D T S C L (n04bWithInteriorDivision C K) (C.referenceState, 0) m v =
      fun _ => (0 : ℝ) := by
  rcases hv with rfl | rfl | rfl <;> funext p <;>
    simp only [atom, n04bWithInteriorDivision, n04bInteriorDividedDifference,
      sub_self, zero_div, ite_self]

/-- One constant bounds all three actual reference divided atoms at all
orders. The material assumption is only positivity of the fixed samples. -/
theorem n04bWithInteriorDivision_reference_dividedJets
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (K : CanonicalData S) (hE0 : ∀ j, 0 ≤ T.E0 (T.sample j)) :
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (v : Atom), (v = .dividedA ∨ v = .dividedB ∨ v = .dividedC) →
      let V := n04bWithInteriorDivision C K
      ContDiffOn ℝ ∞ (atom D T S C L V (C.referenceState, 0) m v) unitStrip ∧
      (∀ p ∈ unitStrip, atom D T S C L V (C.referenceState, 0) m v
        (p + (0, Real.pi)) = atom D T S C L V (C.referenceState, 0) m v p) ∧
      ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (atom D T S C L V (C.referenceState, 0) m v) p| ≤
          B * T.E0 (T.sample (V.cell m)) ^ B := by
  intro s
  refine ⟨1, zero_lt_one, ?_⟩
  intro m v hv
  dsimp only
  rw [n04bWithInteriorDivision_reference_dividedAtom_zero D T S C L K m v hv]
  refine ⟨contDiffOn_const, (fun _ _ => rfl), ?_⟩
  intro p hp a b hab
  simp only [mixedDerivative, iteratedDeriv_const, ite_self, abs_zero]
  exact mul_nonneg zero_le_one
    (Real.rpow_nonneg (hE0 ((n04bWithInteriorDivision C K).cell m)) _)

/-- The actual whole reference gauge already stores that quotient; no
field is replaced in applying the zero reference estimates. -/
theorem n04WholeReferenceGauge_reference_dividedJets
    {D : ReferenceData} (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) (hE0 : ∀ j, 0 ≤ T.E0 (T.sample j)) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (v : Atom), (v = .dividedA ∨ v = .dividedB ∨ v = .dividedC) →
      ContDiffOn ℝ ∞ (atom D T S C L V (C.referenceState, 0) m v) unitStrip ∧
      (∀ p ∈ unitStrip, atom D T S C L V (C.referenceState, 0) m v
        (p + (0, Real.pi)) = atom D T S C L V (C.referenceState, 0) m v p) ∧
      ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (atom D T S C L V (C.referenceState, 0) m v) p| ≤
          B * T.E0 (T.sample (V.cell m)) ^ B := by
  dsimp only [n04WholeReferenceGaugeAtlasData]
  exact n04bWithInteriorDivision_reference_dividedJets D T S C L _ hE0

end ContinuousFlexibility.Analysis
