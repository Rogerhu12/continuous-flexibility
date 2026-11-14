module

public import ContinuousFlexibility.Analysis.N06AngularLeibnizLp

/-!
# Finite sums of products on the actual angular-jet L² space

The fixed-order multiplication estimate is combined with finite
Cauchy--Schwarz. The output and every source component retain precisely
the same actual angular derivative order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped BigOperators ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n06_angularJet_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → PolarPoint → ℝ)
    (hf : ∀ i ∈ s, ∀ r, ContDiff ℝ ∞ (fun θ => f i (r, θ))) (k : ℕ) :
    mixedDerivative 0 k (fun p => ∑ i ∈ s, f i p) =
      fun p => ∑ i ∈ s, mixedDerivative 0 k (f i) p := by
  funext p
  simp only [mixedDerivative, iteratedDeriv_zero]
  exact iteratedDeriv_fun_sum (fun i hi =>
    (hf i hi p.1).contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞))

/-- A finite sum of coefficient-field products is bounded on the same
finite jet space. No bound for the final operator is assumed. -/
theorem n06_angularJet_sum_mul_lp_bound
    {ι : Type*} [Fintype ι] {μ : Measure PolarPoint}
    (f g : ι → PolarPoint → ℝ)
    (hf : ∀ i r, ContDiff ℝ ∞ (fun θ => f i (r, θ)))
    (hg : ∀ i r, ContDiff ℝ ∞ (fun θ => g i (r, θ)))
    (b : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hfmeas : ∀ i, ∀ j : Fin (b + 1),
      AEStronglyMeasurable (mixedDerivative 0 j.val (f i)) μ)
    (hgLp : ∀ i, ∀ j : Fin (b + 1), MemLp (mixedDerivative 0 j.val (g i)) 2 μ)
    (hcoeff : ∀ᵐ p ∂μ, ∀ i, ∀ j : Fin (b + 1),
      |mixedDerivative 0 j.val (f i) p| ≤ δ) :
    ∃ hsum : ∀ k : Fin (b + 1),
        MemLp (mixedDerivative 0 k.val (fun p => ∑ i, f i p * g i p)) 2 μ,
      (∑ k : Fin (b + 1),
        ‖(hsum k).toLp (mixedDerivative 0 k.val (fun p => ∑ i, f i p * g i p))‖ ^ 2) ≤
        ((Fintype.card ι : ℝ) * n06AngularMultiplierCost b * δ ^ 2) *
          ∑ i, ∑ j : Fin (b + 1), ‖(hgLp i j).toLp (mixedDerivative 0 j.val (g i))‖ ^ 2 := by
  have hprod (i : ι) := n06_angularJet_mul_lp_bound (f i) (g i) (hf i) (hg i)
    b hδ (hfmeas i) (hgLp i) (hcoeff.mono (fun p hp => hp i))
  choose hmul hmulBound using hprod
  have heq (k : Fin (b + 1)) :
      mixedDerivative 0 k.val (fun p => ∑ i, f i p * g i p) =
        fun p => ∑ i, mixedDerivative 0 k.val (fun q => f i q * g i q) p :=
    n06_angularJet_finset_sum Finset.univ (fun i p => f i p * g i p)
      (fun i _ r => (hf i r).mul (hg i r)) k.val
  have hmeas (k : Fin (b + 1)) :
      AEStronglyMeasurable
        (mixedDerivative 0 k.val (fun p => ∑ i, f i p * g i p)) μ := by
    rw [heq k]
    exact Finset.univ.aestronglyMeasurable_fun_sum
      (fun i _ => (hmul i k).aestronglyMeasurable)
  have hpoint (k : Fin (b + 1)) (p : PolarPoint) :
      (mixedDerivative 0 k.val (fun q => ∑ i, f i q * g i q) p) ^ 2 ≤
        (Fintype.card ι : ℝ) * ∑ i,
          (mixedDerivative 0 k.val (fun q => f i q * g i q) p) ^ 2 := by
    rw [congrFun (heq k) p]
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1 : ℝ))
        (fun i => mixedDerivative 0 k.val (fun q => f i q * g i q) p)
  have hrow (k : Fin (b + 1)) := n06_memLp_of_square_le_finiteSum
    (fun i => mixedDerivative 0 k.val (fun p => f i p * g i p))
    (K := (Fintype.card ι : ℝ)) (Nat.cast_nonneg _) (hmeas k) (fun i => hmul i k)
    (Eventually.of_forall (hpoint k))
  choose hsum hsumBound hnorm using hrow
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑ k : Fin (b + 1), (Fintype.card ι : ℝ) * ∑ i,
        ‖(hmul i k).toLp (mixedDerivative 0 k.val (fun p => f i p * g i p))‖ ^ 2 :=
      Finset.sum_le_sum (fun k _ => hsumBound k)
    _ = (Fintype.card ι : ℝ) * ∑ i, ∑ k : Fin (b + 1),
        ‖(hmul i k).toLp (mixedDerivative 0 k.val (fun p => f i p * g i p))‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, (n06AngularMultiplierCost b * δ ^ 2) *
        ∑ j : Fin (b + 1), ‖(hgLp i j).toLp (mixedDerivative 0 j.val (g i))‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hmulBound i))
        (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

end ContinuousFlexibility.Analysis
