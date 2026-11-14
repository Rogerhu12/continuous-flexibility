import ContinuousFlexibility.Analysis.TameForwardJetSourceBounds
import ContinuousFlexibility.Analysis.TameInverseFamily

/-!
# Fixed-base value bounds for a continuous linear family

Finite seminorm comparison and normalization of the source are performed
on abstract spaces. The supplied family and its original low base are
unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem linearFamily_fixedBase_value_of_norm_growth
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (N : ℕ → E → ℝ)
    (hgrading : ∀ s w B, 0 ≤ B → (∀ j, j ≤ s → N j w ≤ B) → p s w ≤ B)
    {W : Set E} (P : E → E →ₗ[ℝ] E)
    (hcont : ContinuousOn (fun z : E × E => P z.1 z.2) (W ×ˢ univ))
    (allowed : E → Prop) (hmem : ∀ x, allowed x → x ∈ W)
    (base loss : ℕ)
    (hnorm : ∀ R : ℝ, 1 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, allowed x → p base x ≤ R → ∀ y, p base y ≤ 1 →
        N s (P x y) ≤ C * (1 + p (s + loss) x + p (s + loss) y)) :
    ∀ R : ℝ, 1 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, allowed x → p base x ≤ R → ∀ y,
        p s (P x y) ≤ C * ((1 + p (s + loss) x) * p base y +
          p (s + loss) y) := by
  classical
  intro R hR
  choose C hC hc using hnorm R hR
  intro s
  let B : ℝ := ∑ j ∈ Finset.range (s + 1), C j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hC j)
  refine ⟨B, hB, fun x hx hxR y => ?_⟩
  let L : E →L[ℝ] E := inverseFamilyContinuousLinearMap P hcont x
  have hL (v : E) : L v = P x v :=
    inverseFamilyContinuousLinearMap_apply P hcont (hmem x hx) v
  have hunit (v : E) (hv : p base v < 1) :
      p s (L v) ≤ B * (1 + p (s + loss) x + p (s + loss) v) := by
    have hsize : 0 ≤ 1 + p (s + loss) x + p (s + loss) v :=
      add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _)
    apply hgrading s (L v) _ (mul_nonneg hB hsize)
    intro j hj
    rw [hL v]
    have hjC : C j ≤ B := Finset.single_le_sum (f := C) (fun k _ => hC k)
      (Finset.mem_range.mpr (by omega))
    have hhigh : 1 + p (j + loss) x + p (j + loss) v ≤
        1 + p (s + loss) x + p (s + loss) v :=
      add_le_add (add_le_add le_rfl (hp (Nat.add_le_add_right hj loss) x))
        (hp (Nat.add_le_add_right hj loss) v)
    exact (hc j x hx hxR v hv.le).trans
      ((mul_le_mul_of_nonneg_left hhigh (hC j)).trans
        (mul_le_mul_of_nonneg_right hjC hsize))
  have h := linearMap_oneHigh_of_unitSourceBound L (p s) (p base)
    (p (s + loss)) hB hunit y
  simpa only [hL] using h

end ContinuousFlexibility.Analysis
