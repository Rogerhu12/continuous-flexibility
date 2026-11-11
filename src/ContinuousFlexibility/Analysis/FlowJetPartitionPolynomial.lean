import ContinuousFlexibility.Analysis.FlowJetPolynomial
import ContinuousFlexibility.Analysis.FlowJetLinearization

/-!
# Weighted polynomial majorants for the nonlinear partition forcing

Finite sums and products are kept as expanded polynomials. In each
nonlinear partition term, the original outer derivative has weight
length−1 and each lower flow jet has weight partSize−1; their sum is
exactly the required total derivative weight.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

theorem flowJetPolynomial_exists_finite_sum
    {ι : Type*} [Fintype ι] (Q : ι → FlowJetPolynomial) (s : ℕ)
    (hQ : ∀ i, FlowJetPolynomialDegreeLE (Q i) s) :
    ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P s ∧
      ∀ X : ℕ → ℝ, flowJetPolynomialEval P X =
        ∑ i, flowJetPolynomialEval (Q i) X := by
  classical
  have aux (S : Finset ι) :
      ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P s ∧
        ∀ X : ℕ → ℝ, flowJetPolynomialEval P X =
          ∑ i ∈ S, flowJetPolynomialEval (Q i) X := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨[], FlowJetPolynomialDegreeLE.nil s, ?_⟩
      intro X
      simp only [flowJetPolynomialEval_nil, Finset.sum_empty]
    | @insert i S hi ih =>
      obtain ⟨P, hP, heP⟩ := ih
      refine ⟨Q i ++ P, (hQ i).append hP, ?_⟩
      intro X
      rw [flowJetPolynomialEval_append, heP X, Finset.sum_insert hi]
  exact aux Finset.univ

theorem flowJetPolynomial_exists_finite_prod
    {ι : Type*} [Fintype ι] (Q : ι → FlowJetPolynomial) (d : ι → ℕ)
    (hQ : ∀ i, FlowJetPolynomialDegreeLE (Q i) (d i)) :
    ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P (∑ i, d i) ∧
      ∀ X : ℕ → ℝ, flowJetPolynomialEval P X =
        ∏ i, flowJetPolynomialEval (Q i) X := by
  classical
  have aux (S : Finset ι) :
      ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P (∑ i ∈ S, d i) ∧
        ∀ X : ℕ → ℝ, flowJetPolynomialEval P X =
          ∏ i ∈ S, flowJetPolynomialEval (Q i) X := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨[(1, [])], ?_, ?_⟩
      · simpa only [Finset.sum_empty] using
          FlowJetPolynomialDegreeLE.const (c := (1 : ℝ)) zero_le_one 0
      · intro X
        simp only [flowJetPolynomialEval_const, Finset.prod_empty]
    | @insert i S hi ih =>
      obtain ⟨P, hP, heP⟩ := ih
      refine ⟨flowJetPolynomialMul (Q i) P, ?_, ?_⟩
      · simpa only [Finset.sum_insert hi] using (hQ i).mul hP
      · intro X
        rw [flowJetPolynomialEval_mul, heP X, Finset.prod_insert hi]
  exact aux Finset.univ

/-- This polynomial records exactly the nonlinear forcing in the actual
mixed flow-jet equation. Its degree uses the total weight, not the number
of factors or the maximum derivative order. -/
theorem flowJetPolynomial_exists_partition_forcing (n : ℕ)
    (Q : ℕ → FlowJetPolynomial)
    (hQ : ∀ k < n, FlowJetPolynomialDegreeLE (Q k) k) :
    ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P n ∧
      ∀ X : ℕ → ℝ, flowJetPolynomialEval P X =
        ∑ c : OrderedFinpartition (n + 1),
          if 2 ≤ c.length then
            X (c.length - 1) *
              ∏ j, (1 + flowJetPolynomialEval (Q (c.partSize j - 1)) X)
          else 0 := by
  classical
  have hterm (c : OrderedFinpartition (n + 1)) :
      ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P n ∧
        ∀ X : ℕ → ℝ, flowJetPolynomialEval P X =
          if 2 ≤ c.length then
            X (c.length - 1) *
              ∏ j, (1 + flowJetPolynomialEval (Q (c.partSize j - 1)) X)
          else 0 := by
    by_cases hc : 2 ≤ c.length
    · let Qc : Fin c.length → FlowJetPolynomial := fun j =>
        [(1, [])] ++ Q (c.partSize j - 1)
      have hQc (j : Fin c.length) :
          FlowJetPolynomialDegreeLE (Qc j) (c.partSize j - 1) := by
        have hj : c.partSize j - 1 < n := by
          have hlt := flowJet_partition_partSize_lt c hc j
          have hpos := c.partSize_pos j
          omega
        exact (FlowJetPolynomialDegreeLE.const zero_le_one _).append
          (hQ (c.partSize j - 1) hj)
      obtain ⟨R, hR, heR⟩ :=
        flowJetPolynomial_exists_finite_prod Qc (fun j => c.partSize j - 1) hQc
      refine ⟨flowJetPolynomialMul [(1, [c.length - 1])] R, ?_, ?_⟩
      · have hd := (FlowJetPolynomialDegreeLE.atom (c.length - 1)).mul hR
        have hw := flowJet_partition_weight c (Nat.succ_pos n)
        have hw' : (c.length - 1) + ∑ j, (c.partSize j - 1) = n := by
          simpa only [Nat.add_sub_cancel] using hw
        rw [hw'] at hd
        exact hd
      · intro X
        rw [if_pos hc, flowJetPolynomialEval_mul, flowJetPolynomialEval_atom, heR X]
        congr 1
        apply Finset.prod_congr rfl
        intro j _
        exact flowJetPolynomialEval_append [(1, [])] (Q (c.partSize j - 1)) X |>.trans
          (by rw [flowJetPolynomialEval_const])
    · refine ⟨[], FlowJetPolynomialDegreeLE.nil n, ?_⟩
      intro X
      rw [flowJetPolynomialEval_nil, if_neg hc]
  choose R hR heR using hterm
  obtain ⟨P, hP, heP⟩ := flowJetPolynomial_exists_finite_sum R n hR
  refine ⟨P, hP, ?_⟩
  intro X
  rw [heP X]
  exact Finset.sum_congr rfl (fun c _ => heR c X)

end ContinuousFlexibility.Analysis
