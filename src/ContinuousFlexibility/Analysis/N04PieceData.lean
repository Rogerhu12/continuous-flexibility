module

public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Physical pieces for the coordinate stage

These are actual intervals and their orientation. Their geometry is proved
from the profile and the negative components, before any chart is chosen.
The two halves of each negative component retain a named cut pair.
-/

@[expose] public section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements

structure N04PieceData where
  left : ℕ → ℝ
  right : ℕ → ℝ
  cell : ℕ → ℕ
  positive : ℕ → Bool
  reversed : ℕ → Bool
  cutPair : ℕ → ℕ × ℕ

def N04PieceGeometry (D : ReferenceData) (P : N04PieceData) : Prop :=
  (∀ m, D.a < P.left m ∧ P.left m < P.right m ∧ P.right m < D.b) ∧
  (∀ m, P.positive m = true → ∀ r ∈ Ioo (P.left m) (P.right m),
    0 < deriv D.w r) ∧
  (∀ m, P.positive m = false → ∀ r ∈ Ioo (P.left m) (P.right m),
    deriv D.w r < 0) ∧
  ∃ E : Set ℝ, E.Countable ∧ ∀ r ∈ radialCore D \ E,
    ∃! m, r ∈ Ioo (P.left m) (P.right m)

def N04NegativeCutPairs {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (P : N04PieceData) : Prop :=
  ∀ m,
    P.positive (P.cutPair m).1 = false ∧
    P.positive (P.cutPair m).2 = false ∧
    P.reversed (P.cutPair m).1 = false ∧
    P.reversed (P.cutPair m).2 = true ∧
    P.left (P.cutPair m).1 = C.left m ∧
    P.right (P.cutPair m).2 = C.right m ∧
    P.right (P.cutPair m).1 = (C.left m + C.right m) / 2 ∧
    P.left (P.cutPair m).2 = (C.left m + C.right m) / 2

end ContinuousFlexibility.Analysis
