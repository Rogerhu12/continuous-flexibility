module

public import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus
public import ContinuousFlexibility.Analysis.N07aNormalExpansionData

/-!
# The genuine mixed normal recurrence on an open piece

Differentiating the actual second-normal equation gives the finite
Leibniz expansion used by the normal bootstrap. The source is the
original source in that equation. All identities are local to the open
domain; smooth extension of the solution across its boundary is not an
input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def n07aNormalRhs (A : Fin 6 → PolarPoint → ℝ) (u f : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  (∑ i : Fin 5, A i.castSucc p *
    mixedDerivative (n07aNormalShift i).1 (n07aNormalShift i).2 u p) + A 5 p * f p

theorem n07a_normal_mixed_recursion {U : Set PolarPoint} (hU : IsOpen U)
    {A : Fin 6 → PolarPoint → ℝ} {u f : PolarPoint → ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hu : ContDiffOn ℝ ∞ u U) (hf : ContDiffOn ℝ ∞ f U)
    (heq : EqOn (mixedDerivative 2 0 u) (n07aNormalRhs A u f) U)
    (a b : ℕ) {x : PolarPoint} (hx : x ∈ U) :
    mixedDerivative (a + 2) b u x =
      (∑ q ∈ Finset.range (b + 1), ∑ p ∈ Finset.range (a + 1), ∑ i : Fin 5,
        n07aNormalBinomial a b p q * mixedDerivative p q (A i.castSucc) x *
          mixedDerivative (a - p + (n07aNormalShift i).1)
            (b - q + (n07aNormalShift i).2) u x) +
      ∑ q ∈ Finset.range (b + 1), ∑ p ∈ Finset.range (a + 1),
        n07aNormalBinomial a b p q * mixedDerivative p q (A 5) x *
          mixedDerivative (a - p) (b - q) f x := by
  have hi (i : Fin 5) : ContDiffOn ℝ ∞
      (fun p => A i.castSucc p *
        mixedDerivative (n07aNormalShift i).1 (n07aNormalShift i).2 u p) U :=
    (hA i.castSucc).mul (contDiffOn_mixedDerivative hU hu _ _)
  have hsum : ContDiffOn ℝ ∞
      (fun p => ∑ i : Fin 5, A i.castSucc p *
        mixedDerivative (n07aNormalShift i).1 (n07aNormalShift i).2 u p) U :=
    ContDiffOn.sum (fun i _ => hi i)
  have hdiff := n07a_mixedDerivative_eqOn hU heq a b hx
  rw [n07a_mixedDerivative_mixedDerivative_on hU hu a b 2 0 hx, Nat.add_zero] at hdiff
  change mixedDerivative (a + 2) b u x = mixedDerivative a b
    (fun p => (∑ i : Fin 5, A i.castSucc p *
      mixedDerivative (n07aNormalShift i).1 (n07aNormalShift i).2 u p) + A 5 p * f p) x at hdiff
  rw [n07a_mixedDerivative_add_on hU hsum ((hA 5).mul hf) a b hx,
    n07a_mixedDerivative_sum_on hU (fun i _ => hi i) a b hx,
    n07a_mixedDerivative_mul_on hU (hA 5) hf a b hx] at hdiff
  refine hdiff.trans ?_
  apply congrArg₂ (· + ·)
  · calc
      (∑ i : Fin 5, mixedDerivative a b
        (fun p => A i.castSucc p *
          mixedDerivative (n07aNormalShift i).1 (n07aNormalShift i).2 u p) x) =
          ∑ i : Fin 5, ∑ q ∈ Finset.range (b + 1), ∑ p ∈ Finset.range (a + 1),
            n07aNormalBinomial a b p q * mixedDerivative p q (A i.castSucc) x *
              mixedDerivative (a - p + (n07aNormalShift i).1)
                (b - q + (n07aNormalShift i).2) u x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [n07a_mixedDerivative_mul_on hU (hA i.castSucc)
          (contDiffOn_mixedDerivative hU hu _ _) a b hx]
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro p _
        rw [n07a_mixedDerivative_mixedDerivative_on hU hu (a - p) (b - q)
          (n07aNormalShift i).1 (n07aNormalShift i).2 hx]
        unfold n07aNormalBinomial
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.sum_comm]
  · apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro p _
    unfold n07aNormalBinomial
    ring

end ContinuousFlexibility.Analysis
