import ContinuousFlexibility.Analysis.ScalarTransportJetBounds

/-!
# Weighted bounds for the actual three-field transport recurrence

The finite product below is the three-index Leibniz expression for a
parameter-line jet and two spatial derivatives. The transport system
has one slope field and two transported fields; only the second
transported field carries the independent-residual weight. Radial
strong induction preserves the exact spatial degree and that charge.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators

variable {X : Type*}

/-- The actual parameter/radius/angle Leibniz sum. -/
def diagonalJetProduct (F G : ℕ → ℕ → ℕ → X → ℝ)
    (n a b : ℕ) (x : X) : ℝ :=
  ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
    ∑ k ∈ Finset.range (n + 1),
      (b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ) *
        F k i j x * G (n - k) (a - i) (b - j) x

/-- Two fixed angular shifts are charged once to the product degree. -/
theorem hasWeightedJetBound_diagonalJetProduct
    {W H Q : X → ℝ} {U : Set X} {denom : ℝ}
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x)
    (F G : ℕ → ℕ → ℕ → X → ℝ)
    (n a b dF dG cF cG : ℕ)
    (hF : ∀ k, k ≤ n → ∀ i, i ≤ a → ∀ j, j ≤ b →
      HasWeightedJetBound W H Q U denom (i + j + dF) cF (F k i j))
    (hG : ∀ k, k ≤ n → ∀ i, i ≤ a → ∀ j, j ≤ b →
      HasWeightedJetBound W H Q U denom (i + j + dG) cG (G k i j)) :
    HasWeightedJetBound W H Q U denom (a + b + dF + dG) (cF + cG)
      (diagonalJetProduct F G n a b) := by
  unfold diagonalJetProduct
  apply HasWeightedJetBound.finset_sum (Finset.range (b + 1)) hW hH hQ
  intro j hj
  have hjb : j ≤ b := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  apply HasWeightedJetBound.finset_sum (Finset.range (a + 1)) hW hH hQ
  intro i hi
  have hia : i ≤ a := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  apply HasWeightedJetBound.finset_sum (Finset.range (n + 1)) hW hH hQ
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hp := (hF k hkn i hia j hjb).mul hW hH hQ
    (hG (n - k) (Nat.sub_le _ _) (a - i) (Nat.sub_le _ _)
      (b - j) (Nat.sub_le _ _))
  have hdegree : (i + j + dF) + (a - i + (b - j) + dG) = a + b + dF + dG := by
    omega
  have hs := hp.const_mul hW hH hQ
    ((b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ))
  have hs' : HasWeightedJetBound W H Q U denom (a + b + dF + dG) (cF + cG)
      (fun x => ((b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ)) *
        (F k i j x * G (n - k) (a - i) (b - j) x)) := by
    simpa only [hdegree] using hs
  exact hs'.congr (fun x hx => by ring)

/-- The slope/transport system preserves every spatial degree. The
input identities are equalities of the specified jet arrays, so this
lemma applies directly after the genuine three-index Leibniz formula.
The two transported fields are treated by the same proof. -/
theorem weightedJetBounds_transportSystem
    {W H Q : X → ℝ} {U : Set X} {denom : ℝ}
    (nmax N : ℕ)
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x) (hdenom : 0 < denom)
    (L C A T : ℕ → ℕ → ℕ → X → ℝ)
    (Z : Fin 2 → ℕ → ℕ → ℕ → X → ℝ)
    (hL : ∀ n a b, n ≤ nmax → a + b ≤ N →
      HasWeightedJetBound W H Q U denom (a + b) 0 (L n a b))
    (hC : ∀ n a b, n ≤ nmax → a + b ≤ N →
      HasWeightedJetBound W H Q U denom 0 0 (C n a b))
    (hA0 : ∀ n b, n ≤ nmax → b ≤ N →
      HasWeightedJetBound W H Q U denom b 0 (A n 0 b))
    (hZ0 : ∀ c n b, n ≤ nmax → b ≤ N →
      HasWeightedJetBound W H Q U denom b c.val (Z c n 0 b))
    (hT : ∀ n a b, n ≤ nmax → a + b ≤ N → ∀ x ∈ U,
      T n a b x = L n a b x +
        diagonalJetProduct (diagonalJetProduct C A) (Z 0) n a b x)
    (hAr : ∀ n a b, n ≤ nmax → a + 1 + b ≤ N → ∀ x ∈ U,
      A n (a + 1) b x =
        diagonalJetProduct (fun k i j => L k i (j + 1)) A n a b x -
          diagonalJetProduct L (fun k i j => A k i (j + 1)) n a b x)
    (hZr : ∀ c n a b, n ≤ nmax → a + 1 + b ≤ N → ∀ x ∈ U,
      Z c n (a + 1) b x =
        -diagonalJetProduct T (fun k i j => Z c k i (j + 1)) n a b x) :
    ∀ a n b, n ≤ nmax → a + b ≤ N →
      HasWeightedJetBound W H Q U denom (a + b) 0 (A n a b) ∧
        ∀ c : Fin 2,
          HasWeightedJetBound W H Q U denom (a + b) c.val (Z c n a b) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro n b hn hab
    cases a with
    | zero =>
      constructor
      · simpa only [Nat.zero_add] using
          hA0 n b hn (by simpa only [Nat.zero_add] using hab)
      · intro c
        simpa only [Nat.zero_add] using
          hZ0 c n b hn (by simpa only [Nat.zero_add] using hab)
    | succ a =>
      have hprev (k : ℕ) (hk : k ≤ nmax) (i : ℕ) (hi : i ≤ a)
          (j : ℕ) (hij : i + j ≤ N) :
          HasWeightedJetBound W H Q U denom (i + j) 0 (A k i j) ∧
            ∀ c : Fin 2,
              HasWeightedJetBound W H Q U denom (i + j) c.val (Z c k i j) :=
        ih i (Nat.lt_succ_of_le hi) k j hk hij
      have hCA (k : ℕ) (hk : k ≤ nmax) (i : ℕ) (hi : i ≤ a)
          (j : ℕ) (hij : i + j ≤ N) :
          HasWeightedJetBound W H Q U denom (i + j) 0
            (diagonalJetProduct C A k i j) := by
        have hcf (k' : ℕ) (hk' : k' ≤ k) (i' : ℕ) (hi' : i' ≤ i)
            (j' : ℕ) (hj' : j' ≤ j) :
            HasWeightedJetBound W H Q U denom (i' + j' + 0) 0 (C k' i' j') :=
          (hC k' i' j' (hk'.trans hk) (by omega)).monoDegree
            hW hH hQ hdenom (Nat.zero_le _)
        have haf (k' : ℕ) (hk' : k' ≤ k) (i' : ℕ) (hi' : i' ≤ i)
            (j' : ℕ) (hj' : j' ≤ j) :
            HasWeightedJetBound W H Q U denom (i' + j' + 0) 0 (A k' i' j') := by
          simpa only [Nat.add_zero] using
            (hprev k' (hk'.trans hk) i' (hi'.trans hi) j' (by omega)).1
        simpa only [Nat.add_zero] using
          hasWeightedJetBound_diagonalJetProduct hW hH hQ C A k i j 0 0 0 0 hcf haf
      have hTbound (k : ℕ) (hk : k ≤ nmax) (i : ℕ) (hi : i ≤ a)
          (j : ℕ) (hij : i + j ≤ N) :
          HasWeightedJetBound W H Q U denom (i + j) 0 (T k i j) := by
        have hcf (k' : ℕ) (hk' : k' ≤ k) (i' : ℕ) (hi' : i' ≤ i)
            (j' : ℕ) (hj' : j' ≤ j) :
            HasWeightedJetBound W H Q U denom (i' + j' + 0) 0
              (diagonalJetProduct C A k' i' j') := by
          simpa only [Nat.add_zero] using
            hCA k' (hk'.trans hk) i' (hi'.trans hi) j' (by omega)
        have hzf (k' : ℕ) (hk' : k' ≤ k) (i' : ℕ) (hi' : i' ≤ i)
            (j' : ℕ) (hj' : j' ≤ j) :
            HasWeightedJetBound W H Q U denom (i' + j' + 0) 0 (Z 0 k' i' j') := by
          simpa only [Nat.add_zero, Fin.val_zero] using
            (hprev k' (hk'.trans hk) i' (hi'.trans hi) j' (by omega)).2 0
        have hprod : HasWeightedJetBound W H Q U denom (i + j) 0
            (diagonalJetProduct (diagonalJetProduct C A) (Z 0) k i j) := by
          simpa only [Nat.add_zero] using hasWeightedJetBound_diagonalJetProduct
            hW hH hQ (diagonalJetProduct C A) (Z 0) k i j 0 0 0 0 hcf hzf
        exact ((hL k i j hk hij).add hW hH hQ hprod).congr
          (fun x hx => hT k i j hk hij x hx)
      have hfirst : HasWeightedJetBound W H Q U denom (a + 1 + b) 0
          (diagonalJetProduct (fun k i j => L k i (j + 1)) A n a b) := by
        have hlf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
            (j : ℕ) (hj : j ≤ b) :
            HasWeightedJetBound W H Q U denom (i + j + 1) 0 (L k i (j + 1)) := by
          simpa only [Nat.add_assoc] using hL k i (j + 1) (hk.trans hn) (by omega)
        have haf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
            (j : ℕ) (hj : j ≤ b) :
            HasWeightedJetBound W H Q U denom (i + j + 0) 0 (A k i j) := by
          simpa only [Nat.add_zero] using (hprev k (hk.trans hn) i hi j (by omega)).1
        have heq : a + b + 1 = a + 1 + b := by omega
        simpa only [Nat.add_zero, heq] using hasWeightedJetBound_diagonalJetProduct
          hW hH hQ (fun k i j => L k i (j + 1)) A n a b 1 0 0 0 hlf haf
      have hsecond : HasWeightedJetBound W H Q U denom (a + 1 + b) 0
          (diagonalJetProduct L (fun k i j => A k i (j + 1)) n a b) := by
        have hlf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
            (j : ℕ) (hj : j ≤ b) :
            HasWeightedJetBound W H Q U denom (i + j + 0) 0 (L k i j) := by
          simpa only [Nat.add_zero] using hL k i j (hk.trans hn) (by omega)
        have haf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
            (j : ℕ) (hj : j ≤ b) :
            HasWeightedJetBound W H Q U denom (i + j + 1) 0 (A k i (j + 1)) := by
          simpa only [Nat.add_assoc] using
            (hprev k (hk.trans hn) i hi (j + 1) (by omega)).1
        have heq : a + b + 1 = a + 1 + b := by omega
        simpa only [Nat.add_zero, heq] using hasWeightedJetBound_diagonalJetProduct
          hW hH hQ L (fun k i j => A k i (j + 1)) n a b 0 1 0 0 hlf haf
      refine ⟨(hfirst.sub hW hH hQ hsecond).congr
        (fun x hx => hAr n a b hn hab x hx), fun c => ?_⟩
      have htf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
          (j : ℕ) (hj : j ≤ b) :
          HasWeightedJetBound W H Q U denom (i + j + 0) 0 (T k i j) := by
        simpa only [Nat.add_zero] using hTbound k (hk.trans hn) i hi j (by omega)
      have hzf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
          (j : ℕ) (hj : j ≤ b) :
          HasWeightedJetBound W H Q U denom (i + j + 1) c.val (Z c k i (j + 1)) := by
        simpa only [Nat.add_assoc] using
          (hprev k (hk.trans hn) i hi (j + 1) (by omega)).2 c
      have hprod : HasWeightedJetBound W H Q U denom (a + 1 + b) c.val
          (diagonalJetProduct T (fun k i j => Z c k i (j + 1)) n a b) := by
        have heq : a + b + 1 = a + 1 + b := by omega
        simpa only [Nat.add_zero, Nat.zero_add, heq] using
          hasWeightedJetBound_diagonalJetProduct hW hH hQ T
            (fun k i j => Z c k i (j + 1)) n a b 0 1 0 c.val htf hzf
      exact hprod.neg.congr (fun x hx => hZr c n a b hn hab x hx)

end ContinuousFlexibility.Analysis
