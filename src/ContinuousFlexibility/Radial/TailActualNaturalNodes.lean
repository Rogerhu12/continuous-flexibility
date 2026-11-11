import ContinuousFlexibility.Radial.TailActualNodeCoefficients
import ContinuousFlexibility.Radial.TailNaturalNodeBounds

/-!
# The natural node sequence for the actual tail coefficients

All recurrence coefficients come from the canonical Poisson edge pair.
The unused zeroth diagonal is set to `Λ μ₀` for the continued-fraction
bookkeeping; no condition is imposed on the solution at the entrance.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

def tailNaturalDiagonal (T : DeepTailData) (hT : DeepTailHypotheses T) : ℕ → ℝ
  | 0 => T.Λ * tailMass T 0
  | n + 1 => tailActualInteriorDiagonal T hT n

theorem tailNaturalDiagonal_pos {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) (n : ℕ) :
    0 < tailNaturalDiagonal T hT n := by
  cases n with
  | zero => exact mul_pos hT.2.2.1 (tailMass_pos hT 0)
  | succ n => exact tailActualInteriorDiagonal_pos hT hη hK n

theorem tailNaturalDiagonal_lower {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) (n : ℕ) :
    T.Λ * tailMass T n / 2 ≤ tailNaturalDiagonal T hT n := by
  cases n with
  | zero =>
      change T.Λ * tailMass T 0 / 2 ≤ T.Λ * tailMass T 0
      linarith only [mul_pos hT.2.2.1 (tailMass_pos hT 0)]
  | succ n => exact (tailActualInteriorDiagonal_bounds hT hη hK n).1

/-- Alternating signs convert the positive recurrence into the actual
physical flux-matching recurrence. -/
theorem tail_alternating_node_recurrence {b c y : ℕ → ℝ}
    (hrec : ∀ n, b n * y (n + 1) = c n * y n + c (n + 1) * y (n + 2)) :
    ∀ n, -b n * ((-1 : ℝ) ^ (n + 1) * y (n + 1)) =
      c n * ((-1 : ℝ) ^ n * y n) + c (n + 1) * ((-1 : ℝ) ^ (n + 2) * y (n + 2)) := by
  intro n
  have h := congrArg (fun z : ℝ => (-1 : ℝ) ^ n * z) (hrec n)
  simp only [pow_succ] at h ⊢
  nlinarith only [h]

/-- A nonzero physical node solution with the exact recurrence, the
required mass--resistance decay, and weighted L¹ and L² summability. -/
theorem exists_tailActualNaturalNodes {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) :
    ∃ a : ℕ → ℝ,
      a 0 = 1 ∧ (∀ n, a n ≠ 0) ∧
      (∀ n, -tailActualInteriorDiagonal T hT n * a (n + 1) =
        tailActualNodeCoupling T hT n * a n +
          tailActualNodeCoupling T hT (n + 1) * a (n + 2)) ∧
      Summable (fun n => tailMass T n * a n ^ 2) ∧
      Summable (fun n => tailMass T n * |a n|) ∧
      (∀ n, |a (n + 1)| ≤
        8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |a n|) ∧
      ∀ m n, m ≤ n → |a n| ≤ |a m| *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) := by
  obtain ⟨y, hy₀, hypos, hyrec, hysq, hstep, _, _, hyabs, hprod⟩ :=
    exists_tailNaturalNodeLine_bounds
      (tailNaturalDiagonal_pos hT hη hK) (tailActualNodeCoupling_pos hT)
      (tailMass_pos hT) (tailResistance_pos hT) hT.2.2.1 hK
      (tailNaturalDiagonal_lower hT hη hK) (tailActualNodeCoupling_upper hT hη)
      (fun n => (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.1)
      (fun n => (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.2.1)
  let a : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * y n
  have habs (n : ℕ) : |a n| = |y n| := by
    simp only [a, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hsq (n : ℕ) : a n ^ 2 = y n ^ 2 := by
    rw [← sq_abs (a n), habs n, sq_abs]
  have hr (n : ℕ) : tailActualInteriorDiagonal T hT n * y (n + 1) =
      tailActualNodeCoupling T hT n * y n + tailActualNodeCoupling T hT (n + 1) * y (n + 2) :=
    hyrec n
  refine ⟨a, ?_, ?_, tail_alternating_node_recurrence hr, ?_, ?_, ?_, ?_⟩
  · simp only [a, pow_zero, one_mul, hy₀]
  · intro n
    exact mul_ne_zero (pow_ne_zero n (by norm_num)) (hypos n).ne'
  · exact hysq.congr (fun n => congrArg (fun z => tailMass T n * z) (hsq n).symm)
  · exact hyabs.congr (fun n => congrArg (fun z => tailMass T n * z) (habs n).symm)
  · intro n
    simpa only [habs] using hstep n
  · intro m n hmn
    simpa only [habs] using hprod m n hmn

end ContinuousFlexibility.Radial
