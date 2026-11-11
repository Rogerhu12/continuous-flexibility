import ContinuousFlexibility.Radial.InnerActualModelChain
import ContinuousFlexibility.Radial.InnerRadialInterfaceWeights

/-!
# The full reference has blocks of size at most two

Every internal cut has exactly one adjacent gap. The gap label below
partitions the actual cut variables, including the two terminal half-gaps.
The complete reference matrix vanishes between different labels. Its
blocks therefore have at most two variables; no gap off-diagonal is
discarded to obtain this statement.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

/-- The unique gap incident to an internal cut of an alternating chain. -/
def innerModelChainGapOfCut {m : ℕ} (i : Fin (2 * m)) : Fin (m + 1) :=
  ⟨(i.val + 1) / 2, by omega⟩

theorem innerModelChainGapOfCut_fiber {m : ℕ} (g : Fin (m + 1)) :
    Finset.univ.filter (fun i : Fin (2 * m) => innerModelChainGapOfCut i = g) =
      innerChainPieceCuts (2 * m) (innerModelChainGap g) := by
  ext i
  simp only [innerChainPieceCuts, Finset.mem_filter, Finset.mem_univ, true_and,
    innerModelChainGapOfCut, innerModelChainGap, Fin.ext_iff]
  omega

/-- This counts the actual cut variables in each reference block. -/
theorem innerModelChainGapOfCut_card_le_two {m : ℕ} (g : Fin (m + 1)) :
    (Finset.univ.filter
      (fun i : Fin (2 * m) => innerModelChainGapOfCut i = g)).card ≤ 2 := by
  rw [innerModelChainGapOfCut_fiber]
  exact innerChainPieceCuts_card_le_two (2 * m) (innerModelChainGap g)

theorem innerModelChainGapOfCut_restriction {m : ℕ} (g : Fin (m + 1))
    (i : Fin 2)
    (hactive : if i = 0 then 0 < (innerModelChainGap g).val
      else (innerModelChainGap g).val < 2 * m) :
    innerChainScalarRestriction (2 * m) (innerModelChainGap g)
      (fun k => ((innerModelChainGapOfCut k).val : ℝ)) 1 i = (g.val : ℝ) := by
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · have hp : 0 < (innerModelChainGap g).val := by
      simpa only [ite_true] using hactive
    simp only [innerChainScalarRestriction, ite_true, dif_pos hp]
    apply congrArg (fun k : ℕ => (k : ℝ))
    dsimp only [innerModelChainGapOfCut, innerModelChainGap]
    dsimp only [innerModelChainGap] at hp
    omega
  · have hi : (1 : Fin 2) ≠ 0 := by decide
    have hp : (innerModelChainGap g).val < 2 * m := by
      simpa only [if_neg hi] using hactive
    simp only [innerChainScalarRestriction, if_neg hi, dif_pos hp]
    apply congrArg (fun k : ℕ => (k : ℝ))
    dsimp only [innerModelChainGapOfCut, innerModelChainGap]
    omega

/-- The same full reference used in the inverse is block diagonal for
the gap partition. Both endpoint variables of a short gap remain in
its block, with the entire original flux matrix. -/
theorem innerActualChainOfModelsAndGaps_reference_blocks
    {D : ReferenceData} {m : ℕ} (G : InnerRadialChainGeometry D (2 * m))
    (bordered : Bool) (j : ℝ) (center : Fin m) (column : RadialModeL2 D)
    (models : ∀ p : Fin m, InnerRadialModelChart D G bordered j
      (innerModelChainPiece center) column (innerModelChainPiece p))
    (gaps : ∀ g : Fin (m + 1), InnerRadialGapChart D G j
      (innerModelChainPiece center) (innerModelChainGap g))
    (i k : Fin (2 * m)) (hik : innerModelChainGapOfCut i ≠ innerModelChainGapOfCut k) :
    (innerActualChainOfModelsAndGaps G bordered j center column models gaps).referenceMatrix i k =
      0 := by
  let C := innerActualChainOfModelsAndGaps G bordered j center column models gaps
  let w : Fin (2 * m) → ℝ := fun c => (innerModelChainGapOfCut c).val
  have hcomm : Commute (Matrix.diagonal w) C.referenceMatrix := by
    apply C.referenceMatrix_commute w
    intro p Q hp
    rcases innerModelChainPiece_or_gap p with ⟨q, rfl⟩ | ⟨g, rfl⟩
    · have hmodel : C.piece (innerModelChainPiece q) = Sum.inl (models q) :=
        innerActualChainOfModelsAndGaps_model G bordered j center column models gaps q
      rw [hmodel] at hp
      cases hp
    · refine ⟨(g.val : ℝ), ?_, ?_⟩
      · intro hleft
        exact innerModelChainGapOfCut_restriction g 0
          (by simpa only [ite_true] using hleft)
      · intro hright
        exact innerModelChainGapOfCut_restriction g 1
          (by simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using hright)
  have heq := congrArg (fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ => A i k) hcomm.eq
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at heq
  have hwne : w i ≠ w k := by
    intro h
    apply hik
    apply Fin.ext
    dsimp only [w] at h
    exact_mod_cast h
  have hz : (w i - w k) * C.referenceMatrix i k = 0 := by
    calc
      _ = w i * C.referenceMatrix i k - C.referenceMatrix i k * w k := by ring
      _ = 0 := sub_eq_zero.mpr heq
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hwne)

end ContinuousFlexibility.Radial
