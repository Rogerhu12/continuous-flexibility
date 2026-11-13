import ContinuousFlexibility.Analysis.ScalarTransportSystemBounds

/-!
# State-order budgets in the actual transport recurrence

Multiplying the parameter jet of order `n` by `Q ^ (-(n * D) / denom)`
commutes with the three-index Leibniz product. The existing radial
transport induction therefore applies unchanged, and undoing the scalar
rescaling restores exactly the degree `n * D + a + b`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators

variable {X : Type*} {W H Q : X → ℝ} {U : Set X} {denom : ℝ}

private def stateBudgetScale (D : ℕ) (F : ℕ → ℕ → ℕ → X → ℝ)
    (n a b : ℕ) (x : X) : ℝ :=
  Q x ^ (-((n * D : ℕ) : ℝ) / denom) * F n a b x

private theorem weighted_rpow_mul
    {f : X → ℝ} {d e c : ℕ} {α : ℝ}
    (hQ : ∀ x ∈ U, 0 < Q x)
    (he : (e : ℝ) / denom = α + (d : ℝ) / denom)
    (hf : HasWeightedJetBound W H Q U denom d c f) :
    HasWeightedJetBound W H Q U denom e c (fun x => Q x ^ α * f x) := by
  obtain ⟨C, P, hC, hP, hb⟩ := hf
  refine ⟨C, P, hC, hP, fun x hx => ?_⟩
  calc
    _ = Q x ^ α * |f x| := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hQ x hx).le _)]
    _ ≤ Q x ^ α * (C * W x ^ P * H x ^ c * Q x ^ ((d : ℝ) / denom)) :=
      mul_le_mul_of_nonneg_left (hb x hx) (Real.rpow_nonneg (hQ x hx).le _)
    _ = _ := by rw [he, Real.rpow_add (hQ x hx)]; ring

private theorem stateBudgetScale_bound {D n a b d c : ℕ}
    {F : ℕ → ℕ → ℕ → X → ℝ}
    (hQ : ∀ x ∈ U, 0 < Q x)
    (hf : HasWeightedJetBound W H Q U denom (n * D + d) c (F n a b)) :
    HasWeightedJetBound W H Q U denom d c
      (stateBudgetScale (Q := Q) (denom := denom) D F n a b) :=
  weighted_rpow_mul hQ (by push_cast; ring) hf

private theorem stateBudgetScale_bound_restore {D n a b d c : ℕ}
    {F : ℕ → ℕ → ℕ → X → ℝ}
    (hQ : ∀ x ∈ U, 0 < Q x)
    (hf : HasWeightedJetBound W H Q U denom d c
      (stateBudgetScale (Q := Q) (denom := denom) D F n a b)) :
    HasWeightedJetBound W H Q U denom (n * D + d) c (F n a b) := by
  have h := weighted_rpow_mul (α := ((n * D : ℕ) : ℝ) / denom)
    (e := n * D + d) hQ (by push_cast; ring) hf
  exact h.congr (fun x hx => by
    dsimp only [stateBudgetScale]
    rw [← mul_assoc, ← Real.rpow_add (hQ x hx), neg_div, add_neg_cancel,
      Real.rpow_zero, one_mul])

private theorem stateBudgetScale_product
    (D n a b : ℕ) (F G : ℕ → ℕ → ℕ → X → ℝ) (x : X) (hx : 0 < Q x) :
    stateBudgetScale (Q := Q) (denom := denom) D (diagonalJetProduct F G) n a b x =
      diagonalJetProduct (stateBudgetScale (Q := Q) (denom := denom) D F)
        (stateBudgetScale (Q := Q) (denom := denom) D G) n a b x := by
  simp only [stateBudgetScale, diagonalJetProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hsum : k * D + (n - k) * D = n * D := by
    rw [← Nat.add_mul, show k + (n - k) = n by omega]
  have hp : Q x ^ (-((k * D : ℕ) : ℝ) / denom) *
      Q x ^ (-(((n - k) * D : ℕ) : ℝ) / denom) =
        Q x ^ (-((n * D : ℕ) : ℝ) / denom) := by
    rw [← Real.rpow_add hx, ← add_div, ← neg_add, ← Nat.cast_add, hsum]
  rw [← hp]
  ring

private theorem diagonalJetProduct_point_congr
    (F G F' G' : ℕ → ℕ → ℕ → X → ℝ) (n a b : ℕ) (x : X)
    (hF : ∀ k i j, F k i j x = F' k i j x)
    (hG : ∀ k i j, G k i j x = G' k i j x) :
    diagonalJetProduct F G n a b x = diagonalJetProduct F' G' n a b x := by
  unfold diagonalJetProduct
  simp_rw [hF, hG]

/-- The original transport system with an additive state-order budget.
The two copies of a transported field may keep different height charges. -/
theorem n04NegativeChart_weighted_transport_stateBudget
    (K N D : ℕ)
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x) (hdenom : 0 < denom)
    (L C A T : ℕ → ℕ → ℕ → X → ℝ)
    (Z : Fin 2 → ℕ → ℕ → ℕ → X → ℝ)
    (hL : ∀ n a b, n ≤ K → a + b ≤ N →
      HasWeightedJetBound W H Q U denom (n * D + a + b) 0 (L n a b))
    (hC : ∀ n a b, n ≤ K → a + b ≤ N →
      HasWeightedJetBound W H Q U denom (n * D) 0 (C n a b))
    (hA0 : ∀ n b, n ≤ K → b ≤ N →
      HasWeightedJetBound W H Q U denom (n * D + b) 0 (A n 0 b))
    (hZ0 : ∀ c n b, n ≤ K → b ≤ N →
      HasWeightedJetBound W H Q U denom (n * D + b) c.val (Z c n 0 b))
    (hT : ∀ n a b, n ≤ K → a + b ≤ N → ∀ x ∈ U,
      T n a b x = L n a b x +
        diagonalJetProduct (diagonalJetProduct C A) (Z 0) n a b x)
    (hAr : ∀ n a b, n ≤ K → a + 1 + b ≤ N → ∀ x ∈ U,
      A n (a + 1) b x =
        diagonalJetProduct (fun k i j => L k i (j + 1)) A n a b x -
          diagonalJetProduct L (fun k i j => A k i (j + 1)) n a b x)
    (hZr : ∀ c n a b, n ≤ K → a + 1 + b ≤ N → ∀ x ∈ U,
      Z c n (a + 1) b x =
        -diagonalJetProduct T (fun k i j => Z c k i (j + 1)) n a b x) :
    ∀ a n b, n ≤ K → a + b ≤ N →
      HasWeightedJetBound W H Q U denom (n * D + a + b) 0 (A n a b) ∧
        ∀ c : Fin 2,
          HasWeightedJetBound W H Q U denom (n * D + a + b) c.val (Z c n a b) := by
  let S := stateBudgetScale (Q := Q) (denom := denom) D
  have hQpos (x : X) (hx : x ∈ U) : 0 < Q x := zero_lt_one.trans_le (hQ x hx)
  have hs : ∀ a n b, n ≤ K → a + b ≤ N →
      HasWeightedJetBound W H Q U denom (a + b) 0 (S A n a b) ∧
        ∀ c : Fin 2,
          HasWeightedJetBound W H Q U denom (a + b) c.val (S (Z c) n a b) := by
    apply weightedJetBounds_transportSystem K N hW hH hQ hdenom
      (S L) (S C) (S A) (S T) (fun c => S (Z c))
    · intro n a b hn hab
      apply stateBudgetScale_bound hQpos
      simpa only [Nat.add_assoc] using hL n a b hn hab
    · intro n a b hn hab
      apply stateBudgetScale_bound hQpos
      simpa only [Nat.add_zero] using hC n a b hn hab
    · intro n b hn hb
      exact stateBudgetScale_bound hQpos (hA0 n b hn hb)
    · intro c n b hn hb
      exact stateBudgetScale_bound hQpos (hZ0 c n b hn hb)
    · intro n a b hn hab x hx
      change Q x ^ _ * T n a b x = _
      rw [hT n a b hn hab x hx, mul_add]
      congr 1
      exact (stateBudgetScale_product D n a b (diagonalJetProduct C A) (Z 0)
        x (hQpos x hx)).trans (diagonalJetProduct_point_congr _ _ _ _ n a b x
          (fun k i j => stateBudgetScale_product D k i j C A x (hQpos x hx))
          (fun _ _ _ => rfl))
    · intro n a b hn hab x hx
      change Q x ^ _ * A n (a + 1) b x = _
      rw [hAr n a b hn hab x hx, mul_sub]
      exact congrArg₂ (fun u v : ℝ => u - v)
        (stateBudgetScale_product D n a b (fun k i j => L k i (j + 1)) A x (hQpos x hx))
        (stateBudgetScale_product D n a b L (fun k i j => A k i (j + 1)) x (hQpos x hx))
    · intro c n a b hn hab x hx
      change Q x ^ _ * Z c n (a + 1) b x = _
      rw [hZr c n a b hn hab x hx, mul_neg]
      exact congrArg Neg.neg
        (stateBudgetScale_product D n a b T (fun k i j => Z c k i (j + 1)) x (hQpos x hx))
  intro a n b hn hab
  have hb := hs a n b hn hab
  constructor
  · simpa only [Nat.add_assoc] using stateBudgetScale_bound_restore hQpos hb.1
  · intro c
    simpa only [Nat.add_assoc] using stateBudgetScale_bound_restore hQpos (hb.2 c)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_weighted_transport_stateBudget'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_weighted_transport_stateBudget
