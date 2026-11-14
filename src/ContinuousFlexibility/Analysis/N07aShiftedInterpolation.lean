module

public import ContinuousFlexibility.Analysis.SpacesInterpolationProducts
public import ContinuousFlexibility.Analysis.TameTransfer
public import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# Fixed offsets in the genuine interpolation grading

A fixed coefficient or source loss is absorbed into the low base once.
It is not charged separately for each factor in a normal expansion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem n07a_hasInterpolation_shift {p : ℕ → Seminorm ℝ E}
    (h : HasInterpolation p) (d : ℕ) : HasInterpolation (fun n => p (n + d)) := by
  obtain ⟨base, loss, h⟩ := h
  refine ⟨base, loss, fun a b c ha hab hbc => ?_⟩
  obtain ⟨C, hC, hCb⟩ := h (a + d) (b + d) (c + d) (by omega) (by omega) (by omega)
  refine ⟨C, hC, fun x => ?_⟩
  have he₀ : (((c + d : ℕ) : ℝ) - (b + d : ℕ) - loss) /
      (((c + d : ℕ) : ℝ) - ((a + d : ℕ) : ℝ)) = ((c : ℝ) - b - loss) / (c - a) := by
    push_cast
    congr 1 <;> ring
  have he₁ : (((b + d : ℕ) : ℝ) - (a + d : ℕ) + loss) /
      (((c + d : ℕ) : ℝ) - ((a + d : ℕ) : ℝ)) = ((b : ℝ) - a + loss) / (c - a) := by
    push_cast
    congr 1 <;> ring
  simpa only [he₀, he₁] using hCb x

theorem n07a_interpolation_product_offset
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p) (d : ℕ) :
    ∃ base loss : ℕ, ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι],
      ∀ (order : ι → ℕ) (s : ℕ), (∑ i, order i) ≤ s →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ι → E,
          (∏ i, p (order i + d) (x i)) ≤ C *
            ∑ i, p (s + loss) (x i) * ∏ j ∈ Finset.univ.erase i, p base (x j) := by
  have hshift : ∀ x, Monotone (fun n => p (n + d) x) :=
    fun x a b hab => hp (Nat.add_le_add_right hab d) x
  obtain ⟨base, loss, hb⟩ := spaces_interpolation_product_bound
    (fun n => p (n + d)) hshift (n07a_hasInterpolation_shift hI d)
  refine ⟨base + d, loss + d, ?_⟩
  intro ι _ _ _ order s hs
  obtain ⟨C, hC, hCb⟩ := hb order s hs
  refine ⟨C, hC, fun x => ?_⟩
  have hmono : (∏ i, p (order i + d) (x i)) ≤
      ∏ i, p (order i + 2 + d) (x i) := by
    apply Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _)
    exact fun i _ => hp (by omega) (x i)
  exact hmono.trans (by simpa only [Nat.add_assoc] using hCb x)

end ContinuousFlexibility.Analysis
