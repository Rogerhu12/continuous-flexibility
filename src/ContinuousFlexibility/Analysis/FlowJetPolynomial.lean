import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite nonnegative majorants with spatial derivative weights

An atom indexed by k represents an original field derivative of order
k+1 and has weight k. A finite sum of products is kept in expanded form.
This records the exact weight of each original factor before applying
state interpolation, so derivative losses are not multiplied during
the flow induction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Expanded finite real polynomials; repeated indices record powers. -/
abbrev FlowJetPolynomial := List (ℝ × List ℕ)

def flowJetPolynomialEval (P : FlowJetPolynomial) (X : ℕ → ℝ) : ℝ :=
  (P.map (fun m => m.1 * (m.2.map X).prod)).sum

/-- Coefficients are nonnegative and each monomial has the prescribed
weighted derivative degree. This condition asserts no estimate about a flow. -/
def FlowJetPolynomialDegreeLE (P : FlowJetPolynomial) (s : ℕ) : Prop :=
  ∀ m ∈ P, 0 ≤ m.1 ∧ m.2.sum ≤ s

def flowJetPolynomialMul (P Q : FlowJetPolynomial) : FlowJetPolynomial :=
  P.flatMap (fun m => Q.map (fun n => (m.1 * n.1, m.2 ++ n.2)))

@[simp] theorem flowJetPolynomialEval_nil (X : ℕ → ℝ) :
    flowJetPolynomialEval [] X = 0 := rfl

@[simp] theorem flowJetPolynomialEval_cons (m : ℝ × List ℕ)
    (P : FlowJetPolynomial) (X : ℕ → ℝ) :
    flowJetPolynomialEval (m :: P) X =
      m.1 * (m.2.map X).prod + flowJetPolynomialEval P X := rfl

theorem flowJetPolynomialEval_append (P Q : FlowJetPolynomial) (X : ℕ → ℝ) :
    flowJetPolynomialEval (P ++ Q) X =
      flowJetPolynomialEval P X + flowJetPolynomialEval Q X := by
  simp only [flowJetPolynomialEval, List.map_append, List.sum_append]

@[simp] theorem flowJetPolynomialEval_const (c : ℝ) (X : ℕ → ℝ) :
    flowJetPolynomialEval [(c, [])] X = c := by
  simp only [flowJetPolynomialEval_cons, List.map_nil, List.prod_nil,
    flowJetPolynomialEval_nil, mul_one, add_zero]

@[simp] theorem flowJetPolynomialEval_atom (k : ℕ) (X : ℕ → ℝ) :
    flowJetPolynomialEval [(1, [k])] X = X k := by
  simp only [flowJetPolynomialEval_cons, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, one_mul, flowJetPolynomialEval_nil, add_zero]

private theorem flowJetPolynomialEval_map_monomial
    (m : ℝ × List ℕ) (Q : FlowJetPolynomial) (X : ℕ → ℝ) :
    flowJetPolynomialEval (Q.map (fun n => (m.1 * n.1, m.2 ++ n.2))) X =
      (m.1 * (m.2.map X).prod) * flowJetPolynomialEval Q X := by
  induction Q with
  | nil => simp only [List.map_nil, flowJetPolynomialEval_nil, mul_zero]
  | cons n Q ih =>
    simp only [List.map_cons, flowJetPolynomialEval_cons,
      List.map_append, List.prod_append]
    rw [ih]
    ring

theorem flowJetPolynomialEval_mul (P Q : FlowJetPolynomial) (X : ℕ → ℝ) :
    flowJetPolynomialEval (flowJetPolynomialMul P Q) X =
      flowJetPolynomialEval P X * flowJetPolynomialEval Q X := by
  induction P with
  | nil => simp only [flowJetPolynomialMul, List.flatMap_nil,
      flowJetPolynomialEval_nil, zero_mul]
  | cons m P ih =>
    rw [flowJetPolynomialMul, List.flatMap_cons, flowJetPolynomialEval_append,
      flowJetPolynomialEval_map_monomial]
    change (m.1 * (m.2.map X).prod) * flowJetPolynomialEval Q X +
        flowJetPolynomialEval (flowJetPolynomialMul P Q) X =
      flowJetPolynomialEval (m :: P) X * flowJetPolynomialEval Q X
    rw [ih, flowJetPolynomialEval_cons]
    ring

namespace FlowJetPolynomialDegreeLE

theorem nil (s : ℕ) : FlowJetPolynomialDegreeLE [] s := by
  intro m hm
  cases hm

theorem const {c : ℝ} (hc : 0 ≤ c) (s : ℕ) :
    FlowJetPolynomialDegreeLE [(c, [])] s := by
  intro m hm
  have he : m = (c, []) := List.mem_singleton.mp hm
  rw [he]
  exact ⟨hc, Nat.zero_le s⟩

theorem atom (k : ℕ) : FlowJetPolynomialDegreeLE [(1, [k])] k := by
  intro m hm
  have he : m = ((1 : ℝ), [k]) := List.mem_singleton.mp hm
  rw [he]
  exact ⟨zero_le_one, by simp only [List.sum_cons, List.sum_nil, add_zero, le_refl]⟩

theorem mono {P : FlowJetPolynomial} {s t : ℕ}
    (hP : FlowJetPolynomialDegreeLE P s) (hst : s ≤ t) :
    FlowJetPolynomialDegreeLE P t :=
  fun m hm => ⟨(hP m hm).1, (hP m hm).2.trans hst⟩

theorem append {P Q : FlowJetPolynomial} {s : ℕ}
    (hP : FlowJetPolynomialDegreeLE P s) (hQ : FlowJetPolynomialDegreeLE Q s) :
    FlowJetPolynomialDegreeLE (P ++ Q) s := by
  intro m hm
  rcases List.mem_append.mp hm with hp | hq
  · exact hP m hp
  · exact hQ m hq

theorem mul {P Q : FlowJetPolynomial} {s t : ℕ}
    (hP : FlowJetPolynomialDegreeLE P s) (hQ : FlowJetPolynomialDegreeLE Q t) :
    FlowJetPolynomialDegreeLE (flowJetPolynomialMul P Q) (s + t) := by
  intro m hm
  obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
  rw [← he]
  refine ⟨mul_nonneg (hP a ha).1 (hQ b hb).1, ?_⟩
  rw [List.sum_append]
  exact Nat.add_le_add (hP a ha).2 (hQ b hb).2

end FlowJetPolynomialDegreeLE

theorem flowJetPolynomialEval_nonneg {P : FlowJetPolynomial} {s : ℕ}
    (hP : FlowJetPolynomialDegreeLE P s) {X : ℕ → ℝ} (hX : ∀ k, 0 ≤ X k) :
    0 ≤ flowJetPolynomialEval P X := by
  have hprod (ks : List ℕ) : 0 ≤ (ks.map X).prod := by
    induction ks with
    | nil => exact zero_le_one
    | cons k ks ih => exact mul_nonneg (hX k) ih
  unfold flowJetPolynomialEval
  apply List.sum_nonneg
  intro y hy
  obtain ⟨m, hm, he⟩ := List.mem_map.mp hy
  rw [← he]
  exact mul_nonneg (hP m hm).1 (hprod m.2)

end ContinuousFlexibility.Analysis
