module

public import ContinuousFlexibility.Analysis.N07aCompositionBudget
public import Mathlib.Order.Preorder.Finite

/-!
# The triangular higher derivative formula for an actual inverse

The atomic partition is the unique term containing the highest forward
jet. Composing its input slots with the first forward differential removes
the first inverse differentials. Every remaining forward jet has smaller
order, while its total excess-order budget remains exactly n - 1.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff BigOperators

theorem n07a_orderedPartition_eq_atomic_of_length_eq
    {n : ℕ} (c : OrderedFinpartition n) (h : c.length = n) :
    c = OrderedFinpartition.atomic n := by
  have hs (i : Fin c.length) : c.partSize i = 1 := by
    have hb := n07a_partition_source_order c
    have hsum : (∑ j, (c.partSize j - 1)) = 0 := by omega
    have hi : c.partSize i - 1 ≤ ∑ j, (c.partSize j - 1) :=
      Finset.single_le_sum (f := fun j : Fin c.length => c.partSize j - 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hp := c.partSize_pos i
    omega
  rcases c with ⟨l, size, hpos, emb, hemb, hparts, hdis, hcover⟩
  dsimp only at h hs
  subst l
  obtain rfl : size = fun _ : Fin n => 1 := funext hs
  have hmono : StrictMono (fun i : Fin n => emb i 0) := by
    intro i j hij
    exact (congrArg (emb i) (Subsingleton.elim (0 : Fin 1) _)).trans_lt
      ((hparts hij).trans_eq
        (congrArg (emb j) (Subsingleton.elim _ (0 : Fin 1))))
  have he (i : Fin n) (j : Fin 1) : emb i j = i := by
    have hj : j = 0 := Subsingleton.elim _ _
    simpa only [hj] using hmono.apply_eq (x := i)
  simp only [OrderedFinpartition.ext_iff, OrderedFinpartition.atomic,
    heq_eq_eq, true_and]
  funext i j
  exact he i j

theorem n07a_orderedPartition_length_lt
    {n : ℕ} (c : OrderedFinpartition n) (h : c ≠ OrderedFinpartition.atomic n) :
    c.length < n := by
  have hle := c.length_le
  have hne : c.length ≠ n := fun hc => h (n07a_orderedPartition_eq_atomic_of_length_eq c hc)
  omega

private theorem n07a_iteratedFDeriv_linear_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) {n : ℕ} (hn : 2 ≤ n) (y : E) :
    iteratedFDeriv ℝ n (A : E → E) y = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ (A : E → E) = fun _ => A := funext fun _ => A.fderiv
  rw [he, iteratedFDeriv_succ_const]
  simp only [Pi.zero_apply, norm_zero]

theorem n07a_norm_inverse_jet_le_partition_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : E → E} {y : E}
    (hF : ContDiffAt ℝ ∞ F (G y)) (hG : ContDiffAt ℝ ∞ G y)
    (hFG : (F ∘ G) =ᶠ[𝓝 y] id)
    (V : E →L[ℝ] E) (hGV : ∀ v, fderiv ℝ G y (V v) = v)
    {b : ℝ} (hb : 0 ≤ b) (hV : ‖V‖ ≤ b) {n : ℕ} (hn : 2 ≤ n) :
    ‖iteratedFDeriv ℝ n F (G y)‖ ≤
      ∑ c : OrderedFinpartition n,
        if c = OrderedFinpartition.atomic n then 0 else
          b ^ n * ‖iteratedFDeriv ℝ c.length F (G y)‖ *
            ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) G y‖ := by
  classical
  let term (c : OrderedFinpartition n) : E [×n]→L[ℝ] E :=
    c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length F (G y))
      (fun j => iteratedFDeriv ℝ (c.partSize j) G y)
  let transformed (c : OrderedFinpartition n) : E [×n]→L[ℝ] E :=
    (term c).compContinuousLinearMap (fun _ => V)
  have hsum : (∑ c, term c) = 0 := by
    have hformula : iteratedFDeriv ℝ n (F ∘ G) y = ∑ c, term c :=
      iteratedFDeriv_comp hF hG (by simp : (n : ℕ∞ω) ≤ ∞)
    rw [← hformula, (hFG.iteratedFDeriv ℝ n).self_of_nhds]
    exact n07a_iteratedFDeriv_linear_eq_zero (ContinuousLinearMap.id ℝ E) hn y
  have htsum : (∑ c, transformed c) = 0 := by
    ext v
    have h := congrArg (fun A : E [×n]→L[ℝ] E => A (fun i => V (v i))) hsum
    simpa only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.zero_apply,
      transformed, ContinuousMultilinearMap.compContinuousLinearMap_apply] using h
  have hatomic : transformed (OrderedFinpartition.atomic n) = iteratedFDeriv ℝ n F (G y) := by
    ext v
    change (iteratedFDeriv ℝ n F (G y))
        (fun i : Fin n => iteratedFDeriv ℝ 1 G y (fun _ : Fin 1 => V (v i))) =
      (iteratedFDeriv ℝ n F (G y)) v
    apply congrArg (iteratedFDeriv ℝ n F (G y))
    funext i
    exact (iteratedFDeriv_one_apply (fun _ : Fin 1 => V (v i))).trans (hGV (v i))
  have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := transformed)
    (Finset.mem_univ (OrderedFinpartition.atomic n))
  rw [htsum] at hsplit
  have hnegative : transformed (OrderedFinpartition.atomic n) =
      -(∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic n), transformed c) := by
    calc
      _ = ((∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic n), transformed c) +
          transformed (OrderedFinpartition.atomic n)) -
          (∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic n), transformed c) := by abel
      _ = _ := by rw [hsplit]; simp only [zero_sub]
  have hbound (c : OrderedFinpartition n) :
      ‖transformed c‖ ≤ b ^ n * ‖iteratedFDeriv ℝ c.length F (G y)‖ *
        ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) G y‖ := by
    calc
      _ ≤ ‖term c‖ * ∏ _i : Fin n, ‖V‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ (‖iteratedFDeriv ℝ c.length F (G y)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) G y‖) * b ^ n := by
        rw [Fin.prod_const]
        exact mul_le_mul (c.norm_compAlongOrderedFinpartition_le _ _)
          (pow_le_pow_left₀ (norm_nonneg V) hV n) (pow_nonneg (norm_nonneg V) n)
          (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
      _ = _ := by ring
  calc
    ‖iteratedFDeriv ℝ n F (G y)‖ =
        ‖∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic n), transformed c‖ := by
      rw [← hatomic, hnegative, norm_neg]
    _ ≤ ∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic n), ‖transformed c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic n),
        b ^ n * ‖iteratedFDeriv ℝ c.length F (G y)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) G y‖ :=
      Finset.sum_le_sum fun c _ => hbound c
    _ = _ := by
      have heq := Finset.sum_subset
        (Finset.erase_subset (OrderedFinpartition.atomic n) Finset.univ)
        (f := fun c => if c = OrderedFinpartition.atomic n then (0 : ℝ) else
          b ^ n * ‖iteratedFDeriv ℝ c.length F (G y)‖ *
            ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) G y‖)
        (by
          intro c hc hnot
          have he : c = OrderedFinpartition.atomic n := by
            by_contra hne
            exact hnot (Finset.mem_erase.mpr ⟨hne, hc⟩)
          exact if_pos he)
      rw [← heq]
      apply Finset.sum_congr rfl
      intro c hc
      rw [if_neg (Finset.mem_erase.mp hc).1]

end ContinuousFlexibility.Analysis
