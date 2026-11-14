import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Diagonal widths against component-uniform material costs

A component family indexed by a pair of natural numbers can make its
transition widths smaller than every proposed material power and every
fixed derivative loss. The first index tests an integer upper bound for
the real cost exponent; the second tests the loss. Each width is strictly
positive. No limiting argument or zero-width component is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Arbitrary positive componentwise widths cannot satisfy a uniform
material-power estimate merely because all costs are finite separately.
`K i loss` may be any nonnegative grading cost of a chosen direction. -/
theorem n04PositiveGeometry_exists_diagonal_width
    (E H : ℕ × ℕ → ℝ) (K : (ℕ × ℕ) → ℕ → ℝ)
    (hE : ∀ i, 1 ≤ E i) (hH : ∀ i, 0 ≤ H i)
    (hK : ∀ i loss, 0 ≤ K i loss) :
    ∃ δ : ℕ × ℕ → ℝ, (∀ i, 0 < δ i) ∧
      ∀ B : ℝ, 0 < B → ∀ loss : ℕ,
        ¬ ∀ i, 1 ≤ B * E i ^ B * H i ^ (3 / 4 : ℝ) * K i loss * δ i := by
  let A : ℕ × ℕ → ℝ := fun i =>
    ((i.1 : ℝ) + 1) * E i ^ ((i.1 : ℝ) + 1) * H i ^ (3 / 4 : ℝ) *
      (K i i.2 + 1)
  have hA (i : ℕ × ℕ) : 0 ≤ A i := by
    have he : 0 ≤ E i := zero_le_one.trans (hE i)
    have hh := hH i
    have hk := hK i i.2
    dsimp only [A]
    positivity
  let δ : ℕ × ℕ → ℝ := fun i => (A i + 1)⁻¹
  have hδ (i : ℕ × ℕ) : 0 < δ i := inv_pos.mpr (by linarith [hA i])
  have hsmall (i : ℕ × ℕ) : A i * δ i < 1 := by
    change A i / (A i + 1) < 1
    exact (div_lt_one (by linarith [hA i])).mpr (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro B hB loss hbound
  obtain ⟨n, hn⟩ := exists_nat_gt B
  let i : ℕ × ℕ := (n, loss)
  have hBn : B ≤ (n : ℝ) + 1 := by linarith
  have he : 0 ≤ E i := zero_le_one.trans (hE i)
  have hp : B * E i ^ B ≤ ((n : ℝ) + 1) * E i ^ ((n : ℝ) + 1) :=
    mul_le_mul hBn (Real.rpow_le_rpow_of_exponent_le (hE i) hBn)
      (Real.rpow_nonneg he _) (by positivity)
  have hh : 0 ≤ H i ^ (3 / 4 : ℝ) := Real.rpow_nonneg (hH i) _
  have hprod : B * E i ^ B * H i ^ (3 / 4 : ℝ) * K i loss ≤ A i := by
    change B * E i ^ B * H i ^ (3 / 4 : ℝ) * K i loss ≤
      ((n : ℝ) + 1) * E i ^ ((n : ℝ) + 1) * H i ^ (3 / 4 : ℝ) *
        (K i loss + 1)
    exact mul_le_mul (mul_le_mul_of_nonneg_right hp hh)
      (le_add_of_nonneg_right (by norm_num)) (hK i loss) (by positivity)
  have hle : 1 ≤ A i * δ i :=
    (hbound i).trans (mul_le_mul_of_nonneg_right hprod (hδ i).le)
  exact (not_lt_of_ge hle) (hsmall i)

end ContinuousFlexibility.Analysis
