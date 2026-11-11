import ContinuousFlexibility.Analysis.FlowJetMaterialClosure
import ContinuousFlexibility.Analysis.FlowJetPartitionPolynomial
import ContinuousFlexibility.Analysis.SpacesHeightAlgebra
import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets
import Mathlib.Algebra.BigOperators.Fin

/-!
# Material one-high bounds for the actual coefficient discriminant

The mixed Leibniz formula records the sum of the two input derivative
orders exactly. Interpolation is applied once to its finite expanded
polynomial. Hence b²−ac has one common low order and one common loss,
independent of the requested mixed derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem exists_mixedProduct_majorant (a b : ℕ) :
    ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P (a + b) ∧
      ∀ X : ℕ → ℝ, flowJetPolynomialEval P X =
        ∑ j : Fin (b + 1), ∑ i : Fin (a + 1),
          (b.choose j : ℝ) * (a.choose i : ℝ) *
            X ((i : ℕ) + (j : ℕ)) * X ((a - i) + (b - j)) := by
  classical
  let Q : Fin (b + 1) → Fin (a + 1) → FlowJetPolynomial := fun j i =>
    [((b.choose j : ℝ) * (a.choose i : ℝ),
      [(i : ℕ) + (j : ℕ), (a - i) + (b - j)])]
  have hQ (j : Fin (b + 1)) (i : Fin (a + 1)) :
      FlowJetPolynomialDegreeLE (Q j i) (a + b) := by
    intro m hm
    have he : m = ((b.choose j : ℝ) * (a.choose i : ℝ),
        [(i : ℕ) + (j : ℕ), (a - i) + (b - j)]) := List.mem_singleton.mp hm
    rw [he]
    refine ⟨by positivity, ?_⟩
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hinner (j : Fin (b + 1)) :=
    flowJetPolynomial_exists_finite_sum (Q j) (a + b) (hQ j)
  choose P hP heP using hinner
  obtain ⟨R, hR, heR⟩ := flowJetPolynomial_exists_finite_sum P (a + b) hP
  refine ⟨R, hR, ?_⟩
  intro X
  rw [heR X]
  apply Finset.sum_congr rfl
  intro j _
  rw [heP j X]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Q, flowJetPolynomialEval_cons, flowJetPolynomialEval_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, add_zero]
  ring

private theorem abs_mixedDerivative_mul_le
    {f g : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (a b : ℕ) (q : PolarPoint) {X : ℕ → ℝ} (hX : ∀ n, 0 ≤ X n)
    (hfbound : ∀ i j : ℕ, i + j ≤ a + b → |mixedDerivative i j f q| ≤ X (i + j))
    (hgbound : ∀ i j : ℕ, i + j ≤ a + b → |mixedDerivative i j g q| ≤ X (i + j)) :
    |mixedDerivative a b (fun p => f p * g p) q| ≤
      ∑ j : Fin (b + 1), ∑ i : Fin (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          X ((i : ℕ) + (j : ℕ)) * X ((a - i) + (b - j)) := by
  have he : mixedDerivative a b (fun p => f p * g p) q =
      ∑ j : Fin (b + 1), ∑ i : Fin (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          mixedDerivative i j f q * mixedDerivative (a - i) (b - j) g q := by
    rw [spaces_mixedDerivative_mul hf hg a b q, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_range _
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hi := i.isLt
  have hj := j.isLt
  have hc : 0 ≤ (b.choose j : ℝ) * (a.choose i : ℝ) := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hc]
  have hb := mul_le_mul
    (hfbound i j (by omega))
    (hgbound (a - i) (b - j) (by omega))
    (abs_nonneg _) (hX (i + j))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hc

/-- The constants precede the state, envelope, actual coefficient fields,
and point. The input order in every factor is its true spatial order;
the common derivative loss is not multiplied by the output order. -/
theorem coefficientDiscriminant_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∀ a b : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
        ∀ K : Fin 3 → PolarPoint → ℝ, (∀ i, ContDiff ℝ ∞ (K i)) →
        ∀ q : PolarPoint,
        (∀ c : Fin 3, ∀ i j : ℕ, i + j ≤ a + b →
          |mixedDerivative i j (K c) q| ≤
            A (i + j) * W ^ (A (i + j)) * (1 + p (i + j + inputLoss) z)) →
        |mixedDerivative a b (fun x => K 1 x ^ 2 - K 0 x * K 2 x) q| ≤
          B * W ^ B * (1 + p (a + b + loss) z) := by
  classical
  obtain ⟨base, loss, hmaterial⟩ := flowJetPolynomial_le_material_one_high hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA a b
  obtain ⟨P, hP, heP⟩ := exists_mixedProduct_majorant a b
  obtain ⟨B, hB, hbound⟩ := hmaterial (a + b) (P ++ P) (hP.append hP) A hA
  refine ⟨B, hB, ?_⟩
  intro z hz W hW K hK q hj
  let X : ℕ → ℝ := fun n => A n * W ^ (A n) * (1 + p (n + inputLoss) z)
  have hX (n : ℕ) : 0 ≤ X n :=
    mul_nonneg (mul_nonneg (zero_le_one.trans (hA n))
      (Real.rpow_nonneg (zero_le_one.trans hW) _))
      (add_nonneg zero_le_one (apply_nonneg _ _))
  have hprod (i j : Fin 3) :
      |mixedDerivative a b (fun x => K i x * K j x) q| ≤ flowJetPolynomialEval P X := by
    rw [heP X]
    exact abs_mixedDerivative_mul_le (hK i) (hK j) a b q hX (hj i) (hj j)
  have hfield : (fun x : PolarPoint => K 1 x ^ 2 - K 0 x * K 2 x) =
      (fun x => (K 1 x * K 1 x) + (-1 : ℝ) * (K 0 x * K 2 x)) := by
    funext x
    ring
  have hmajorant :
      |mixedDerivative a b (fun x => K 1 x ^ 2 - K 0 x * K 2 x) q| ≤
        flowJetPolynomialEval (P ++ P) X := by
    rw [hfield, spaces_mixedDerivative_add ((hK 1).mul (hK 1))
      (contDiff_const.mul ((hK 0).mul (hK 2))),
      spaces_mixedDerivative_const_mul]
    calc
      _ ≤ |mixedDerivative a b (fun x => K 1 x * K 1 x) q| +
          |(-1 : ℝ) * mixedDerivative a b (fun x => K 0 x * K 2 x) q| :=
        abs_add_le _ _
      _ = |mixedDerivative a b (fun x => K 1 x * K 1 x) q| +
          |mixedDerivative a b (fun x => K 0 x * K 2 x) q| := by
        rw [abs_mul, abs_neg, abs_one, one_mul]
      _ ≤ flowJetPolynomialEval P X + flowJetPolynomialEval P X :=
        add_le_add (hprod 1 1) (hprod 0 2)
      _ = flowJetPolynomialEval (P ++ P) X :=
        (flowJetPolynomialEval_append P P X).symm
  exact hmajorant.trans (hbound z hz W hW)

end ContinuousFlexibility.Analysis
