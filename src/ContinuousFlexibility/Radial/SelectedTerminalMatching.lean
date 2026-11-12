import ContinuousFlexibility.Radial.SelectedBoundaryRadiusScale
import ContinuousFlexibility.Radial.ModeRegionSources
import ContinuousFlexibility.Radial.R07DeepTailChange

/-!
# Matching data at the actual two selected cuts

The common constructor fixes the physical cuts, source restrictions,
boundary scales and diagonal boundary rows before installing the two
regional inverses. Both frequency cases use this same record.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

def selectedTerminalSide (i : Fin 2) : Bool := if i = 0 then false else true

theorem selectedTerminalSide_sign (i : Fin 2) :
    bufferSign i = r07OutwardSign (selectedTerminalSide i) := by
  fin_cases i <;> norm_num [selectedTerminalSide, bufferSign, r07OutwardSign]

def selectedTerminalMatching (D : ReferenceData) (j n : ℕ) (margin : ℝ)
    (cut slope : Bool → ℝ) (boundary : Bool → ℝ × ℝ) : RadialMatchingData D where
  frequency := j
  transitionIndex := n
  margin := margin
  D0 := fun i => slope (selectedTerminalSide i)
  innerLeft := cut false
  innerRight := cut true
  boundaryScale := fun i => standInBoundaryScale ((j : ℝ) ^ 2)
    (D.w (cut (selectedTerminalSide i))) (cut (selectedTerminalSide i))
  sourceInner := modeInnerSource D (cut false) (cut true)
  sourceOuter := modeOuterSource D (cut false) (cut true)
  innerInverse := 0
  outerInverse := 0
  innerRepresentative := fun _ _ => 0
  outerRepresentative := fun _ _ => 0
  innerPoisson := fun _ => 0
  outerPoisson := fun _ => 0
  innerFunction := fun _ _ => 0
  outerFunction := fun _ _ => 0
  A := Matrix.diagonal (fun i => (boundary (selectedTerminalSide i)).1)
  B := Matrix.diagonal (fun i => (boundary (selectedTerminalSide i)).2)
  Db := 0
  Kinv := 0

theorem selectedTerminalMatching_cut (D : ReferenceData) (j n : ℕ) (margin : ℝ)
    (cut slope : Bool → ℝ) (boundary : Bool → ℝ × ℝ) (i : Fin 2) :
    matchingCut D (selectedTerminalMatching D j n margin cut slope boundary) i =
      cut (selectedTerminalSide i) := by
  fin_cases i <;> rfl

theorem selectedTerminalMatching_diagonal (D : ReferenceData) (j n : ℕ) (margin : ℝ)
    (cut slope : Bool → ℝ) (boundary : Bool → ℝ × ℝ) (i : Fin 2) :
    (selectedTerminalMatching D j n margin cut slope boundary).A i i =
        (boundary (selectedTerminalSide i)).1 ∧
      (selectedTerminalMatching D j n margin cut slope boundary).B i i =
        (boundary (selectedTerminalSide i)).2 := by
  simp only [selectedTerminalMatching, Matrix.diagonal_apply_eq, and_self]

theorem selectedTerminalMatching_offDiagonal (D : ReferenceData) (j n : ℕ) (margin : ℝ)
    (cut slope : Bool → ℝ) (boundary : Bool → ℝ × ℝ) (i k : Fin 2) (hik : i ≠ k) :
    (selectedTerminalMatching D j n margin cut slope boundary).A i k = 0 ∧
      (selectedTerminalMatching D j n margin cut slope boundary).B i k = 0 := by
  simp only [selectedTerminalMatching, Matrix.diagonal_apply_ne _ hik, and_self]

end ContinuousFlexibility.Radial
