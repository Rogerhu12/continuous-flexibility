module

public import ContinuousFlexibility.Analysis.ScalarTransportSystemBounds

/-!
# Parameter charges in the genuine transport recurrence

A fixed charge per parameter slot is additive over the actual Leibniz
partitions. Radial induction therefore preserves `a + b + shift * n`,
with no increase of the low grading as the spatial order grows.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators

variable {X : Type*}

/-- A common linear parameter charge is preserved by the exact
Leibniz partition. Fixed spatial shifts are charged once. -/
theorem n04PulledFields_diagonalJetProduct_parameterDegree
    {W H Q : X → ℝ} {U : Set X} {denom : ℝ}
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x)
    (F G : ℕ → ℕ → ℕ → X → ℝ)
    (n a b shift dF dG cF cG : ℕ)
    (hF : ∀ k, k ≤ n → ∀ i, i ≤ a → ∀ j, j ≤ b →
      HasWeightedJetBound W H Q U denom (i + j + dF + shift * k) cF (F k i j))
    (hG : ∀ k, k ≤ n → ∀ i, i ≤ a → ∀ j, j ≤ b →
      HasWeightedJetBound W H Q U denom (i + j + dG + shift * k) cG (G k i j)) :
    HasWeightedJetBound W H Q U denom (a + b + dF + dG + shift * n) (cF + cG)
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
  have hshift : shift * k + shift * (n - k) = shift * n := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hkn]
  have hdegree : (i + j + dF + shift * k) +
      (a - i + (b - j) + dG + shift * (n - k)) = a + b + dF + dG + shift * n := by
    omega
  have hs := hp.const_mul hW hH hQ
    ((b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ))
  have hs' : HasWeightedJetBound W H Q U denom (a + b + dF + dG + shift * n) (cF + cG)
      (fun x => ((b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ)) *
        (F k i j x * G (n - k) (a - i) (b - j) x)) := by
    simpa only [hdegree] using hs
  exact hs'.congr (fun x hx => by ring)

/-- The true transport recurrence preserves spatial degree plus a
fixed charge per parameter derivative. Zero-parameter factors carry
no parameter charge, independently of the radial induction depth. -/
theorem n04PulledFields_transportSystem_parameterDegree
    {W H Q : X → ℝ} {U : Set X} {denom : ℝ}
    (nmax N shift : ℕ)
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x) (hdenom : 0 < denom)
    (L C A T : ℕ → ℕ → ℕ → X → ℝ)
    (Z : Fin 2 → ℕ → ℕ → ℕ → X → ℝ)
    (hL : ∀ n a b, n ≤ nmax → a + b ≤ N →
      HasWeightedJetBound W H Q U denom (a + b + shift * n) 0 (L n a b))
    (hC : ∀ n a b, n ≤ nmax → a + b ≤ N →
      HasWeightedJetBound W H Q U denom (shift * n) 0 (C n a b))
    (hA0 : ∀ n b, n ≤ nmax → b ≤ N →
      HasWeightedJetBound W H Q U denom (b + shift * n) 0 (A n 0 b))
    (hZ0 : ∀ c n b, n ≤ nmax → b ≤ N →
      HasWeightedJetBound W H Q U denom (b + shift * n) c.val (Z c n 0 b))
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
      HasWeightedJetBound W H Q U denom (a + b + shift * n) 0 (A n a b) ∧
        ∀ c : Fin 2,
          HasWeightedJetBound W H Q U denom (a + b + shift * n) c.val (Z c n a b) := by
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
          HasWeightedJetBound W H Q U denom (i + j + shift * k) 0 (A k i j) ∧
            ∀ c : Fin 2,
              HasWeightedJetBound W H Q U denom (i + j + shift * k) c.val (Z c k i j) :=
        ih i (Nat.lt_succ_of_le hi) k j hk hij
      have hCA (k : ℕ) (hk : k ≤ nmax) (i : ℕ) (hi : i ≤ a)
          (j : ℕ) (hij : i + j ≤ N) :
          HasWeightedJetBound W H Q U denom (i + j + shift * k) 0
            (diagonalJetProduct C A k i j) := by
        have hcf (k' : ℕ) (hk' : k' ≤ k) (i' : ℕ) (hi' : i' ≤ i)
            (j' : ℕ) (hj' : j' ≤ j) :
            HasWeightedJetBound W H Q U denom (i' + j' + 0 + shift * k') 0 (C k' i' j') :=
          (hC k' i' j' (hk'.trans hk) (by omega)).monoDegree
            hW hH hQ hdenom (Nat.le_add_left _ _)
        have haf (k' : ℕ) (hk' : k' ≤ k) (i' : ℕ) (hi' : i' ≤ i)
            (j' : ℕ) (hj' : j' ≤ j) :
            HasWeightedJetBound W H Q U denom (i' + j' + 0 + shift * k') 0 (A k' i' j') := by
          simpa only [Nat.add_zero] using
            (hprev k' (hk'.trans hk) i' (hi'.trans hi) j' (by omega)).1
        simpa only [Nat.add_zero] using
          n04PulledFields_diagonalJetProduct_parameterDegree hW hH hQ C A k i j shift 0 0 0 0 hcf haf
      have hTbound (k : ℕ) (hk : k ≤ nmax) (i : ℕ) (hi : i ≤ a)
          (j : ℕ) (hij : i + j ≤ N) :
          HasWeightedJetBound W H Q U denom (i + j + shift * k) 0 (T k i j) := by
        have hcf (k' : ℕ) (hk' : k' ≤ k) (i' : ℕ) (hi' : i' ≤ i)
            (j' : ℕ) (hj' : j' ≤ j) :
            HasWeightedJetBound W H Q U denom (i' + j' + 0 + shift * k') 0
              (diagonalJetProduct C A k' i' j') := by
          simpa only [Nat.add_zero] using
            hCA k' (hk'.trans hk) i' (hi'.trans hi) j' (by omega)
        have hzf (k' : ℕ) (hk' : k' ≤ k) (i' : ℕ) (hi' : i' ≤ i)
            (j' : ℕ) (hj' : j' ≤ j) :
            HasWeightedJetBound W H Q U denom (i' + j' + 0 + shift * k') 0 (Z 0 k' i' j') := by
          simpa only [Nat.add_zero, Fin.val_zero] using
            (hprev k' (hk'.trans hk) i' (hi'.trans hi) j' (by omega)).2 0
        have hprod : HasWeightedJetBound W H Q U denom (i + j + shift * k) 0
            (diagonalJetProduct (diagonalJetProduct C A) (Z 0) k i j) := by
          simpa only [Nat.add_zero] using n04PulledFields_diagonalJetProduct_parameterDegree
            hW hH hQ (diagonalJetProduct C A) (Z 0) k i j shift 0 0 0 0 hcf hzf
        exact ((hL k i j hk hij).add hW hH hQ hprod).congr
          (fun x hx => hT k i j hk hij x hx)
      have hfirst : HasWeightedJetBound W H Q U denom (a + 1 + b + shift * n) 0
          (diagonalJetProduct (fun k i j => L k i (j + 1)) A n a b) := by
        have hlf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
            (j : ℕ) (hj : j ≤ b) :
            HasWeightedJetBound W H Q U denom (i + j + 1 + shift * k) 0 (L k i (j + 1)) := by
          simpa only [Nat.add_assoc] using hL k i (j + 1) (hk.trans hn) (by omega)
        have haf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
            (j : ℕ) (hj : j ≤ b) :
            HasWeightedJetBound W H Q U denom (i + j + 0 + shift * k) 0 (A k i j) := by
          simpa only [Nat.add_zero] using (hprev k (hk.trans hn) i hi j (by omega)).1
        have heq : a + b + 1 = a + 1 + b := by omega
        simpa only [Nat.add_zero, heq] using n04PulledFields_diagonalJetProduct_parameterDegree
          hW hH hQ (fun k i j => L k i (j + 1)) A n a b shift 1 0 0 0 hlf haf
      have hsecond : HasWeightedJetBound W H Q U denom (a + 1 + b + shift * n) 0
          (diagonalJetProduct L (fun k i j => A k i (j + 1)) n a b) := by
        have hlf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
            (j : ℕ) (hj : j ≤ b) :
            HasWeightedJetBound W H Q U denom (i + j + 0 + shift * k) 0 (L k i j) := by
          simpa only [Nat.add_zero] using hL k i j (hk.trans hn) (by omega)
        have haf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
            (j : ℕ) (hj : j ≤ b) :
            HasWeightedJetBound W H Q U denom (i + j + 1 + shift * k) 0 (A k i (j + 1)) := by
          simpa only [Nat.add_assoc] using
            (hprev k (hk.trans hn) i hi (j + 1) (by omega)).1
        have heq : a + b + 1 = a + 1 + b := by omega
        simpa only [Nat.add_zero, heq] using n04PulledFields_diagonalJetProduct_parameterDegree
          hW hH hQ L (fun k i j => A k i (j + 1)) n a b shift 0 1 0 0 hlf haf
      refine ⟨(hfirst.sub hW hH hQ hsecond).congr
        (fun x hx => hAr n a b hn hab x hx), fun c => ?_⟩
      have htf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
          (j : ℕ) (hj : j ≤ b) :
          HasWeightedJetBound W H Q U denom (i + j + 0 + shift * k) 0 (T k i j) := by
        simpa only [Nat.add_zero] using hTbound k (hk.trans hn) i hi j (by omega)
      have hzf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a)
          (j : ℕ) (hj : j ≤ b) :
          HasWeightedJetBound W H Q U denom (i + j + 1 + shift * k) c.val (Z c k i (j + 1)) := by
        simpa only [Nat.add_assoc] using
          (hprev k (hk.trans hn) i hi (j + 1) (by omega)).2 c
      have hprod : HasWeightedJetBound W H Q U denom (a + 1 + b + shift * n) c.val
          (diagonalJetProduct T (fun k i j => Z c k i (j + 1)) n a b) := by
        have heq : a + b + 1 = a + 1 + b := by omega
        simpa only [Nat.add_zero, Nat.zero_add, heq] using
          n04PulledFields_diagonalJetProduct_parameterDegree hW hH hQ T
            (fun k i j => Z c k i (j + 1)) n a b shift 0 1 0 c.val htf hzf
      exact hprod.neg.congr (fun x hx => hZr c n a b hn hab x hx)

end ContinuousFlexibility.Analysis
