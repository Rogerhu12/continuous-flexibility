import ContinuousFlexibility.Analysis.ScalarTransportSystemBounds

/-!
# Radial closure with an additive state-order budget

The degree `n * D + a + b` counts the state loss only once along each
Leibniz term. The centered first integral and its forcing retain exactly
one material height factor. All constants precede the evaluation point,
which may include the component, radius, angle, state and direction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators

variable {X : Type*} {W H Q : X → ℝ} {U : Set X} {denom : ℝ}

/-- State orders, like spatial orders, add exactly in the actual
three-index Leibniz sum. -/
theorem n04NegativeChart_weighted_diagonalJetProduct
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x)
    (F G : ℕ → ℕ → ℕ → X → ℝ)
    (D n a b dF dG cF cG : ℕ)
    (hF : ∀ k, k ≤ n → ∀ i, i ≤ a → ∀ j, j ≤ b →
      HasWeightedJetBound W H Q U denom (k * D + i + j + dF) cF (F k i j))
    (hG : ∀ k, k ≤ n → ∀ i, i ≤ a → ∀ j, j ≤ b →
      HasWeightedJetBound W H Q U denom (k * D + i + j + dG) cG (G k i j)) :
    HasWeightedJetBound W H Q U denom (n * D + a + b + dF + dG) (cF + cG)
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
  have hstate : k * D + (n - k) * D = n * D := by
    rw [← Nat.add_mul, show k + (n - k) = n by omega]
  have hdegree : (k * D + i + j + dF) +
      ((n - k) * D + (a - i) + (b - j) + dG) = n * D + a + b + dF + dG := by
    omega
  have hs := hp.const_mul hW hH hQ
    ((b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ))
  have hs' : HasWeightedJetBound W H Q U denom
      (n * D + a + b + dF + dG) (cF + cG)
      (fun x => ((b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ)) *
        (F k i j x * G (n - k) (a - i) (b - j) x)) := by
    simpa only [hdegree] using hs
  exact hs'.congr (fun x hx => by ring)

/-- Radial induction for the centered transport equation. The angular
input and the speed difference have one height factor; multiplication
by the actual speed never discards it. -/
theorem n04NegativeChart_weighted_firstIntegral_radial
    (K N D : ℕ)
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x) (hdenom : 0 < denom)
    (C E F : ℕ → ℕ → ℕ → X → ℝ)
    (hC : ∀ n a b, n ≤ K → a + b ≤ N →
      HasWeightedJetBound W H Q U denom (n * D + a + b) 0 (C n a b))
    (hE : ∀ n a b, n ≤ K → a + b ≤ N →
      HasWeightedJetBound W H Q U denom (n * D + a + b) 1 (E n a b))
    (hF0 : ∀ n b, n ≤ K → b ≤ N →
      HasWeightedJetBound W H Q U denom (n * D + b) 1 (F n 0 b))
    (hFr : ∀ n a b, n ≤ K → a + 1 + b ≤ N → ∀ x ∈ U,
      F n (a + 1) b x =
        -diagonalJetProduct C (fun k i j => F k i (j + 1)) n a b x - E n a b x) :
    ∀ a n b, n ≤ K → a + b ≤ N →
      HasWeightedJetBound W H Q U denom (n * D + a + b) 1 (F n a b) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro n b hn hab
    cases a with
    | zero =>
        simpa only [Nat.add_zero] using hF0 n b hn (by simpa only [Nat.zero_add] using hab)
    | succ a =>
        have hcf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
            (j : ℕ) (hj : j ≤ b) :
            HasWeightedJetBound W H Q U denom (k * D + i + j + 0) 0 (C k i j) := by
          simpa only [Nat.add_zero] using hC k i j (hk.trans hn) (by omega)
        have hff (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
            (j : ℕ) (hj : j ≤ b) :
            HasWeightedJetBound W H Q U denom (k * D + i + j + 1) 1 (F k i (j + 1)) := by
          simpa only [Nat.add_assoc] using
            ih i (Nat.lt_succ_of_le hi) k (j + 1) (hk.trans hn) (by omega)
        have hprod : HasWeightedJetBound W H Q U denom (n * D + (a + 1) + b) 1
            (diagonalJetProduct C (fun k i j => F k i (j + 1)) n a b) := by
          have heq : n * D + a + b + 1 = n * D + (a + 1) + b := by omega
          simpa only [Nat.add_zero, Nat.zero_add, heq] using
            n04NegativeChart_weighted_diagonalJetProduct hW hH hQ
              C (fun k i j => F k i (j + 1)) D n a b 0 1 0 1 hcf hff
        have hforcing := (hE n a b hn (by omega)).monoDegree hW hH hQ hdenom
          (show n * D + a + b ≤ n * D + (a + 1) + b by omega)
        exact (hprod.neg.sub hW hH hQ hforcing).congr
          (fun x hx => hFr n a b hn hab x hx)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_weighted_firstIntegral_radial'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_weighted_firstIntegral_radial
