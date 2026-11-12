import ContinuousFlexibility.Analysis.N07aInverseJetFormula
import ContinuousFlexibility.Analysis.N07aJetBudgetExpression

/-!
# A fixed-loss bound for inverse spatial jets

Strong induction constructs finite unabsorbed expressions. Every
non-atomic partition spends exactly n - 1 spatial orders. Only after
this construction is complete is the common one-high estimate applied.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}
  {Z : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem n07a_inverseJet_budget
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ Z) (U : Set Z) (Q : Z → ℕ → Set E)
    (F G : Z → ℕ → E → E) (d : ℕ)
    (hF : ∀ z ∈ U, ∀ m y, y ∈ Q z m → ContDiffAt ℝ ∞ (F z m) (G z m y))
    (hG : ∀ z ∈ U, ∀ m y, y ∈ Q z m → ContDiffAt ℝ ∞ (G z m) y)
    (hFG : ∀ z ∈ U, ∀ m y, y ∈ Q z m → (F z m ∘ G z m) =ᶠ[𝓝 y] id)
    (hInverse : ∀ z ∈ U, ∀ m y, y ∈ Q z m → ∀ v,
      fderiv ℝ (G z m) y (fderiv ℝ (F z m) (G z m y) v) = v)
    {b : ℕ → ℝ} (hb : N07aSampleSubpower T K b) (hb0 : ∀ m, 0 ≤ b m)
    (hfirst : ∀ z ∈ U, ∀ m y, y ∈ Q z m →
      ‖fderiv ℝ (F z m) (G z m y)‖ ≤ b m)
    (hInv : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ m y, y ∈ Q z m →
          ‖iteratedFDeriv ℝ n (G z m) y‖ ≤ e m * (1 + p ((n - 1) + d) z)) :
    ∀ n : ℕ, 0 < n → ∃ e : N07aJetBudgetExpression T K (n - 1),
      ∀ z ∈ U, ∀ m y, y ∈ Q z m →
        ‖iteratedFDeriv ℝ n (F z m) (G z m y)‖ ≤ e.eval p d z m := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hone : n = 1
    · subst n
      refine ⟨N07aJetBudgetExpression.constant b hb hb0, fun z hz m y hy => ?_⟩
      simpa only [norm_iteratedFDeriv_one, N07aJetBudgetExpression.eval_constant]
        using hfirst z hz m y hy
    have hn2 : 2 ≤ n := by omega
    have hterm (c : OrderedFinpartition n) :
        ∃ e : N07aJetBudgetExpression T K (n - 1),
          ∀ z ∈ U, ∀ m y, y ∈ Q z m →
            (if c = OrderedFinpartition.atomic n then 0 else
              b m ^ n * ‖iteratedFDeriv ℝ c.length (F z m) (G z m y)‖ *
                ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) (G z m) y‖) ≤ e.eval p d z m := by
      by_cases hc : c = OrderedFinpartition.atomic n
      · refine ⟨N07aJetBudgetExpression.zero T K (n - 1), fun z hz m y hy => ?_⟩
        simp only [if_pos hc, N07aJetBudgetExpression.eval_zero, le_refl]
      obtain ⟨eF, heF⟩ := ih c.length (n07a_orderedPartition_length_lt c hc) (c.length_pos hn)
      choose eG heG heG0 heGb using fun j : Fin c.length => hInv (c.partSize j) (c.partSize_pos j)
      let coeff : ℕ → ℝ := fun m => b m ^ n * ∏ j, eG j m
      have hcoeff : N07aSampleSubpower T K coeff := N07aSampleSubpower.mul hD hT
        (hb.nat_pow hD hT n)
        (N07aSampleSubpower.finset_prod hD hT Finset.univ eG (fun j _ => heG j))
      have hcoeff0 (m : ℕ) : 0 ≤ coeff m := mul_nonneg (pow_nonneg (hb0 m) n)
        (Finset.prod_nonneg fun j _ => heG0 j m)
      have hbudget : (c.length - 1) + (∑ j, (c.partSize j - 1)) ≤ n - 1 := by
        have hsum := n07a_partition_source_order c
        have hpos := c.length_pos hn
        omega
      let e := (eF.appendFactors hD hT (fun j => c.partSize j - 1)
        coeff hcoeff hcoeff0).regrade hbudget
      refine ⟨e, fun z hz m y hy => ?_⟩
      rw [if_neg hc]
      have hprod : (∏ j, ‖iteratedFDeriv ℝ (c.partSize j) (G z m) y‖) ≤
          ∏ j, (eG j m * (1 + p ((c.partSize j - 1) + d) z)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun j _ => heGb j z hz m y hy)
      calc
        _ ≤ (b m ^ n * eF.eval p d z m) *
            ∏ j, (eG j m * (1 + p ((c.partSize j - 1) + d) z)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (heF z hz m y hy) (pow_nonneg (hb0 m) n))
            hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
            (mul_nonneg (pow_nonneg (hb0 m) n) (eF.eval_nonneg p d z m))
        _ = e.eval p d z m := by
          simp only [e, N07aJetBudgetExpression.eval_regrade,
            N07aJetBudgetExpression.eval_appendFactors, coeff, Finset.prod_mul_distrib]
          ring
    choose e he using hterm
    refine ⟨N07aJetBudgetExpression.sum e, fun z hz m y hy => ?_⟩
    have hformula := n07a_norm_inverse_jet_le_partition_sum
      (hF z hz m y hy) (hG z hz m y hy) (hFG z hz m y hy)
      (fderiv ℝ (F z m) (G z m y)) (hInverse z hz m y hy)
      (hb0 m) (hfirst z hz m y hy) hn2
    apply hformula.trans
    rw [N07aJetBudgetExpression.eval_sum]
    exact Finset.sum_le_sum fun c _ => he c z hz m y hy

theorem n07a_inverseJet_fixedLoss
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ Z) (hp : Monotone p) (hIp : HasSmoothing p)
    (U : Set Z) (Q : Z → ℕ → Set E) (F G : Z → ℕ → E → E) (d : ℕ)
    (hF : ∀ z ∈ U, ∀ m y, y ∈ Q z m → ContDiffAt ℝ ∞ (F z m) (G z m y))
    (hG : ∀ z ∈ U, ∀ m y, y ∈ Q z m → ContDiffAt ℝ ∞ (G z m) y)
    (hFG : ∀ z ∈ U, ∀ m y, y ∈ Q z m → (F z m ∘ G z m) =ᶠ[𝓝 y] id)
    (hInverse : ∀ z ∈ U, ∀ m y, y ∈ Q z m → ∀ v,
      fderiv ℝ (G z m) y (fderiv ℝ (F z m) (G z m y) v) = v)
    {b : ℕ → ℝ} (hb : N07aSampleSubpower T K b) (hb0 : ∀ m, 0 ≤ b m)
    (hfirst : ∀ z ∈ U, ∀ m y, y ∈ Q z m →
      ‖fderiv ℝ (F z m) (G z m y)‖ ≤ b m)
    (hInv : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ m y, y ∈ Q z m →
          ‖iteratedFDeriv ℝ n (G z m) y‖ ≤ e m * (1 + p ((n - 1) + d) z)) :
    ∃ low loss : ℕ, ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, p low z ≤ 1 → ∀ m y, y ∈ Q z m →
          ‖iteratedFDeriv ℝ n (F z m) (G z m y)‖ ≤
            e m * (1 + p ((n - 1) + loss) z) := by
  obtain ⟨low, loss, hcollapse⟩ := N07aJetBudgetExpression.oneHigh (K := K) hD hT p hp hIp d
  have hraw := n07a_inverseJet_budget hD hT p U Q F G d hF hG hFG hInverse hb hb0 hfirst hInv
  refine ⟨low, loss, fun n hn => ?_⟩
  obtain ⟨expr, hexpr⟩ := hraw n hn
  obtain ⟨e, he, he0, heb⟩ := hcollapse (n - 1) expr
  exact ⟨e, he, he0, fun z hz hlow m y hy => (hexpr z hz m y hy).trans (heb z hlow m)⟩

end ContinuousFlexibility.Analysis
