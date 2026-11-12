import ContinuousFlexibility.Analysis.TameInterpolationProducts
import ContinuousFlexibility.Analysis.CircleCompositionFaaBounds

/-!
# Fixed interpolation budget for the actual joint chain rule

The positive orders of the blocks of an ordered partition add to the
total order. A fixed low order absorbs the loss of every block before
interpolation. All remaining factors then share one affine high scale,
even when the number of spatial directions grows with the output order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem interpolation_affine_family_le_common_scale
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (base loss order high : ℕ) (hhigh : base < high)
    (horder : base < order → order + loss < high)
    (hinterp : ∀ b c : ℕ, base < b → b + loss < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        p b x ≤ C * (p base x) ^ (((c : ℝ) - b - loss) / (c - base)) *
          (p c x) ^ (((b : ℝ) - base + loss) / (c - base)))
    (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : E) (v : Fin n → E) (Q : ℝ),
      p base x ≤ R → (∀ i, p base (v i) ≤ 1) →
      p high x ≤ Q → (∀ i, p high (v i) ≤ Q) → 1 ≤ Q →
      1 + p order x + ∑ i, p order (v i) ≤ C * Q ^
        ((interpolationOrderCost base loss order : ℝ) / ((high : ℝ) - base)) := by
  let K : ℝ := max R 1
  have hK : 0 ≤ K := zero_le_one.trans (le_max_right _ _)
  obtain ⟨C, hC, hb⟩ := interpolation_le_rpow_scale p hp base loss order high
    hhigh horder hinterp K hK
  refine ⟨1 + ((n : ℝ) + 1) * C, by positivity, ?_⟩
  intro x v Q hx hv hxQ hvQ hQ
  let α : ℝ := (interpolationOrderCost base loss order : ℝ) / ((high : ℝ) - base)
  have hden : 0 < (high : ℝ) - base := sub_pos.mpr (by exact_mod_cast hhigh)
  have hα : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hden.le
  have hone : 1 ≤ Q ^ α := Real.one_le_rpow hQ hα
  have hxb : p order x ≤ C * Q ^ α :=
    hb x Q (hx.trans (le_max_left _ _)) hxQ hQ
  have hvb (i : Fin n) : p order (v i) ≤ C * Q ^ α :=
    hb (v i) Q ((hv i).trans (le_max_right _ _)) (hvQ i) hQ
  have hsum : (∑ i : Fin n, p order (v i)) ≤ (n : ℝ) * (C * Q ^ α) := by
    calc
      _ ≤ ∑ _i : Fin n, C * Q ^ α := Finset.sum_le_sum (fun i _ => hvb i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (add_le_add (add_le_add hone hxb) hsum).trans_eq (by dsimp only [α]; ring)

/-- Finite differential products retain their exact order budget. The
slots may repeat, and no bound on the number of factors is imposed. -/
theorem finite_affine_family_interpolation_bound
    {ι : Type*} [Fintype ι]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (base loss high N : ℕ) (order arity : ι → ℕ)
    (emb : ∀ i, Fin (arity i) → Fin N) (hhigh : base < high)
    (horder : ∀ i, base < order i → order i + loss < high)
    (hcost : (∑ i, interpolationOrderCost base loss (order i)) ≤ high - base)
    (hinterp : ∀ b c : ℕ, base < b → b + loss < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        p b x ≤ C * (p base x) ^ (((c : ℝ) - b - loss) / (c - base)) *
          (p c x) ^ (((b : ℝ) - base + loss) / (c - base)))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ∀ v : Fin N → E,
      p base x ≤ R → (∀ i, p base (v i) ≤ 1) →
      (∏ j, (1 + p (order j) x + ∑ i, p (order j) (v (emb j i)))) ≤
        C * (1 + p high x + ∑ i : Fin N, p high (v i)) := by
  classical
  choose C hC hbound using fun j => interpolation_affine_family_le_common_scale
    p hp base loss (order j) high hhigh (horder j) hinterp R hR (arity j)
  refine ⟨∏ j, C j, Finset.prod_nonneg (fun j _ => hC j), ?_⟩
  intro x v hx hv
  let Q : ℝ := 1 + p high x + ∑ i : Fin N, p high (v i)
  have hsum0 : 0 ≤ ∑ i : Fin N, p high (v i) :=
    Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
  have hx0 : 0 ≤ p high x := apply_nonneg _ _
  have hQ : 1 ≤ Q := by dsimp only [Q]; linarith only [hx0, hsum0]
  have hxQ : p high x ≤ Q := by dsimp only [Q]; linarith only [hsum0]
  have hvQ (i : Fin N) : p high (v i) ≤ Q := by
    have hi : p high (v i) ≤ ∑ j : Fin N, p high (v j) :=
      Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_univ i)
    dsimp only [Q]
    linarith only [hi, hx0]
  have hden : 0 < (high : ℝ) - base := sub_pos.mpr (by exact_mod_cast hhigh)
  have hexponents : (∑ j, (interpolationOrderCost base loss (order j) : ℝ) /
      ((high : ℝ) - base)) ≤ 1 := by
    calc
      _ = ((∑ j, interpolationOrderCost base loss (order j) : ℕ) : ℝ) /
          ((high : ℝ) - base) := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, Nat.cast_sum]
      _ ≤ ((high - base : ℕ) : ℝ) / ((high : ℝ) - base) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcost) hden.le
      _ = 1 := by rw [Nat.cast_sub hhigh.le, div_self hden.ne']
  apply prod_le_common_scale_of_rpow_bounds
    (fun j => 1 + p (order j) x + ∑ i, p (order j) (v (emb j i))) C
    (fun j => (interpolationOrderCost base loss (order j) : ℝ) /
      ((high : ℝ) - base)) Q (fun j => by positivity) hC hQ hexponents
  intro j
  exact hbound j x (v ∘ emb j) Q hx (fun i => hv (emb j i)) hxQ
    (fun i => hvQ (emb j i)) hQ

/-- A fixed low order and fixed shift work for every partition of every
total derivative order. Neither may depend on the low-ball radius. -/
theorem hasInterpolation_partition_affine_growth
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasInterpolation p)
    (oldBase oldLoss : ℕ) :
    ∃ B L : ℕ, oldBase ≤ B ∧
      ∀ R : ℝ, 0 ≤ R → ∀ N : ℕ, ∀ c : OrderedFinpartition N,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ∀ v : Fin N → E,
        p B x ≤ R → (∀ i, p B (v i) ≤ 1) →
        (∏ j : Fin c.length,
          (1 + p (c.partSize j + oldLoss) x +
            ∑ i : Fin (c.partSize j), p (c.partSize j + oldLoss) (v (c.emb j i)))) ≤
          C * (1 + p (N + L) x + ∑ i : Fin N, p (N + L) (v i)) := by
  classical
  obtain ⟨b, l, hinterp⟩ := hIp
  let B : ℕ := max oldBase (max b (oldLoss + l + 1))
  let L : ℕ := B + oldLoss + l + 1
  have hb : b ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hloss : oldLoss + l + 1 ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, L, le_max_left _ _, ?_⟩
  intro R hR N c
  have hhigh : B < N + L := by dsimp only [L]; omega
  have horder (j : Fin c.length) :
      B < c.partSize j + oldLoss → c.partSize j + oldLoss + l < N + L := by
    intro _
    have hj := c.partSize_le j
    dsimp only [L]
    omega
  have hsingle (j : Fin c.length) := interpolation_affine_family_le_common_scale
    p hp B l (c.partSize j + oldLoss) (N + L) hhigh (horder j)
    (fun a d ha had => hinterp B a d hb ha had) R hR (c.partSize j)
  choose C hC hbound using hsingle
  refine ⟨∏ j, C j, Finset.prod_nonneg (fun j _ => hC j), ?_⟩
  intro x v hx hv
  let Q : ℝ := 1 + p (N + L) x + ∑ i : Fin N, p (N + L) (v i)
  have hsum0 : 0 ≤ ∑ i : Fin N, p (N + L) (v i) :=
    Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
  have hx0 : 0 ≤ p (N + L) x := apply_nonneg _ _
  have hQ : 1 ≤ Q := by dsimp only [Q]; linarith only [hx0, hsum0]
  have hxQ : p (N + L) x ≤ Q := by dsimp only [Q]; linarith only [hsum0]
  have hvQ (i : Fin N) : p (N + L) (v i) ≤ Q := by
    have hi : p (N + L) (v i) ≤ ∑ j : Fin N, p (N + L) (v j) :=
      Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_univ i)
    dsimp only [Q]
    linarith only [hi, hx0]
  have hcost (j : Fin c.length) :
      interpolationOrderCost B l (c.partSize j + oldLoss) ≤ c.partSize j := by
    unfold interpolationOrderCost
    split_ifs <;> omega
  have hcostsum : (∑ j : Fin c.length,
      interpolationOrderCost B l (c.partSize j + oldLoss)) ≤ (N + L) - B := by
    have hs : (∑ j : Fin c.length,
        interpolationOrderCost B l (c.partSize j + oldLoss)) ≤ N :=
      (Finset.sum_le_sum (fun j _ => hcost j)).trans_eq (orderedFinpartition_sum_partSize c)
    dsimp only [L]
    omega
  have hden : 0 < ((N + L : ℕ) : ℝ) - B := sub_pos.mpr (by exact_mod_cast hhigh)
  have hexponents : (∑ j : Fin c.length,
      (interpolationOrderCost B l (c.partSize j + oldLoss) : ℝ) /
        (((N + L : ℕ) : ℝ) - B)) ≤ 1 := by
    calc
      _ = ((∑ j : Fin c.length,
          interpolationOrderCost B l (c.partSize j + oldLoss) : ℕ) : ℝ) /
            (((N + L : ℕ) : ℝ) - B) := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, Nat.cast_sum]
      _ ≤ (((N + L) - B : ℕ) : ℝ) / (((N + L : ℕ) : ℝ) - B) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcostsum) hden.le
      _ = 1 := by rw [Nat.cast_sub hhigh.le, div_self hden.ne']
  apply prod_le_common_scale_of_rpow_bounds
    (fun j : Fin c.length => 1 + p (c.partSize j + oldLoss) x +
      ∑ i : Fin (c.partSize j), p (c.partSize j + oldLoss) (v (c.emb j i))) C
    (fun j => (interpolationOrderCost B l (c.partSize j + oldLoss) : ℝ) /
      (((N + L : ℕ) : ℝ) - B)) Q (fun j => by positivity) hC hQ hexponents
  intro j
  exact hbound j x (v ∘ c.emb j) Q hx (fun i => hv (c.emb j i)) hxQ
    (fun i => hvQ (c.emb j i)) hQ

end ContinuousFlexibility.Statements
