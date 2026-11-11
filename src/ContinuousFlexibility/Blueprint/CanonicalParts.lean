import ContinuousFlexibility.Statements.Nonlinear

/-!
# Qualitative canonical coordinate properties

These are the unchanged coordinate and operator parts of the frozen N04
statements. Keeping them separate lets analytic coordinate proofs import
only the nonlinear definitions, without the unrelated global sphere goals.
`Blueprint.Statements` reexports this module.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The conjuncts of `N04Properties` about the pieces and their charts. -/
def N04PartA (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
  IsOpen K.normalizationRegion ∧
  Function.support (referenceColumn D) ⊆ K.normalizationRegion ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m, ∀ p ∈ physicalPieceOpen S K m, p.1 ∈ K.normalizationRegion →
    K.chart z m p = K.chart (C.referenceState, 0) m p ∧
    K.height z m p = K.height (C.referenceState, 0) m p) ∧
  (∀ m, K.physicalLeft m < K.physicalRight m ∧ K.left m < K.right m ∧
    Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ Ioo D.a D.b) ∧
  (∀ m, K.positive m = true → ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m),
    0 < deriv D.w r) ∧
  (∀ m, K.positive m = false → ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m),
    deriv D.w r < 0) ∧
  (∃ E : Set ℝ, volume E = 0 ∧ ∀ r ∈ Ioo D.a D.b \ E,
    ∃! m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m,
    MapsTo (K.chart z m) (physicalPieceOpen S K m) (canonicalOpen S K m) ∧
    MapsTo (K.inverseChart z m) (canonicalOpen S K m) (physicalPieceOpen S K m) ∧
    (∀ p ∈ physicalPieceOpen S K m, K.inverseChart z m (K.chart z m p) = p) ∧
    (∀ p ∈ canonicalOpen S K m, K.chart z m (K.inverseChart z m p) = p) ∧
    ContDiffOn ℝ ∞ (K.chart z m) (physicalPieceOpen S K m) ∧
    ContDiffOn ℝ ∞ (K.inverseChart z m) (canonicalOpen S K m) ∧
    ContDiffOn ℝ ∞ (K.height z m) (physicalPieceOpen S K m) ∧
    (∀ p ∈ physicalPieceOpen S K m,
      0 < K.height z m p ∧ planeJacobian (K.chart z m) p ≠ 0 ∧
      K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) ∧
      K.height z m (p + (0, Real.pi)) = K.height z m p)) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m p, p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) →
    ContDiffAt ℝ ∞ (K.chart z m) p ∧ ContDiffAt ℝ ∞ (K.height z m) p ∧
    planeJacobian (K.chart z m) p ≠ 0 ∧ 0 < K.height z m p) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m, ∀ p ∈ physicalPieceOpen S K m,
    K.chart z m (p.1, -p.2) = ((K.chart z m p).1, -(K.chart z m p).2) ∧
    K.height z m (p.1, -p.2) = K.height z m p ∧
    planeJacobian (K.chart z m) (p.1, -p.2) = planeJacobian (K.chart z m) p) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m, ∀ p ∈ canonicalOpen S K m,
    K.inverseChart z m (p.1, -p.2) =
      ((K.inverseChart z m p).1, -(K.inverseChart z m p).2))

/-- The conjuncts of `N04Properties` about the cut pairs and the canonical operator. -/
def N04PartB (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
  (∀ m,
    K.positive (K.cutPair m).1 = false ∧ K.positive (K.cutPair m).2 = false ∧
    K.physicalLeft (K.cutPair m).1 = C.left m ∧
    K.physicalRight (K.cutPair m).2 = C.right m ∧
    K.physicalRight (K.cutPair m).1 = K.physicalLeft (K.cutPair m).2 ∧
    0 < K.cutRadius m ∧ K.left (K.cutPair m).1 = 0 ∧ K.left (K.cutPair m).2 = 0 ∧
    K.right (K.cutPair m).1 = K.cutRadius m ∧ K.right (K.cutPair m).2 = K.cutRadius m) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u → ∀ m θ,
    let Wl := canonicalHeight S K z (K.cutPair m).1 u
    let Wr := canonicalHeight S K z (K.cutPair m).2 u
    Wr (K.cutRadius m, θ) = Wl (K.cutRadius m, θ) ∧
    radialPartial Wr (K.cutRadius m, θ) =
      -radialPartial Wl (K.cutRadius m, θ) - Wl (K.cutRadius m, θ) / (2 * K.cutRadius m)) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m W, ContDiff ℝ ∞ W → ∀ p ∈ canonicalOpen S K m,
    canonicalOperator S K L z m W p =
      (if K.positive m then -1 else (1 : ℝ)) *
        divergenceOperator (K.coefficients z m) W p + K.potential z m p * W p) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m, K.positive m = false → ∀ p ∈ canonicalOpen S K m,
    (K.coefficients z m).a p = 1 ∧ (K.coefficients z m).b p = 0 ∧
    (K.coefficients z m).c p = -p.1) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ m, K.positive m = true → ∀ p ∈ canonicalOpen S K m,
    let d := (p.1 - K.left m) * (K.right m - p.1)
    (K.coefficients z m).a p - (K.coefficients (C.referenceState, 0) m).a p =
      d ^ 3 * (K.dividedDifference z m).a p ∧
    (K.coefficients z m).b p - (K.coefficients (C.referenceState, 0) m).b p =
      d ^ 3 * (K.dividedDifference z m).b p ∧
    (K.coefficients z m).c p - (K.coefficients (C.referenceState, 0) m).c p =
      d ^ 3 * (K.dividedDifference z m).c p)

end ContinuousFlexibility.Blueprint
