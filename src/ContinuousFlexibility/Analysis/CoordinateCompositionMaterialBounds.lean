module

public import ContinuousFlexibility.Analysis.FlowJetPartitionPolynomial
public import ContinuousFlexibility.Analysis.FlowJetMaterialClosure

/-!
# Fixed-loss material bounds for actual coordinate compositions

Both inner and outer derivatives may contain a high state seminorm.
The actual partition formula assigns weight k−1 to a derivative of
order k. Its total weight is n−1, so interpolation reduces each term
to one high factor without multiplying the derivative loss by n.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem exists_coordinateComposition_polynomial (n : ℕ) :
    ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P n ∧
      ∀ X : ℕ → ℝ, flowJetPolynomialEval P X =
        ∑ c : OrderedFinpartition (n + 1),
          X (c.length - 1) * ∏ j, X (c.partSize j - 1) := by
  classical
  let Q : OrderedFinpartition (n + 1) → FlowJetPolynomial := fun c =>
    [(1, (c.length - 1) :: List.ofFn (fun j => c.partSize j - 1))]
  have hQ (c : OrderedFinpartition (n + 1)) : FlowJetPolynomialDegreeLE (Q c) n := by
    intro m hm
    have he : m = ((1 : ℝ), (c.length - 1) :: List.ofFn (fun j => c.partSize j - 1)) :=
      List.mem_singleton.mp hm
    rw [he]
    refine ⟨zero_le_one, ?_⟩
    have hw := flowJet_partition_weight c (Nat.succ_pos n)
    simpa only [List.sum_cons, List.sum_ofFn, Nat.add_sub_cancel] using hw.le
  obtain ⟨P, hP, heP⟩ := flowJetPolynomial_exists_finite_sum Q n hQ
  refine ⟨P, hP, ?_⟩
  intro X
  rw [heP X]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Q, flowJetPolynomialEval_cons, flowJetPolynomialEval_nil,
    List.map_cons, List.prod_cons, List.map_ofFn, List.prod_ofFn,
    Function.comp_apply, one_mul, add_zero]

/-- Uniform estimates on the actual positive-order inner and outer jets
give a fixed-loss estimate for their actual composition. The constants
are chosen before the state, the envelope, the functions, and the point.
Zeroth order is handled directly from the outer function's value bound. -/
theorem coordinateComposition_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ k, 1 ≤ A k) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ f : Y → Z, ∀ g : X → Y, ∀ x : X,
        ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
        (∀ k : ℕ, 1 ≤ k → ‖iteratedFDeriv ℝ k f (g x)‖ ≤
          A k * W ^ (A k) * (1 + p (k + inputLoss) z)) →
        (∀ k : ℕ, 1 ≤ k → ‖iteratedFDeriv ℝ k g x‖ ≤
          A k * W ^ (A k) * (1 + p (k + inputLoss) z)) →
        ∀ n : ℕ, ‖iteratedFDeriv ℝ (n + 1) (f ∘ g) x‖ ≤
          B n * W ^ (B n) * (1 + p ((n + 1) + loss) z) := by
  classical
  obtain ⟨base, loss, hmaterial⟩ :=
    flowJetPolynomial_le_material_one_high hp hI (inputLoss + 1)
  choose P hP heP using exists_coordinateComposition_polynomial
  refine ⟨base, loss, ?_⟩
  intro A hA
  have hpacked (n : ℕ) :
      ∃ C : ℝ, 0 < C ∧ ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
        flowJetPolynomialEval (P n)
          (fun k => A (k + 1) * W ^ (A (k + 1)) *
            (1 + p (k + (inputLoss + 1)) z)) ≤
          C * W ^ C * (1 + p ((n + 1) + loss) z) :=
    hmaterial (n + 1) (P n) ((hP n).mono (Nat.le_succ n))
      (fun k => A (k + 1)) (fun k => hA (k + 1))
  choose B hB hb using hpacked
  refine ⟨B, hB, ?_⟩
  intro z hz W hW f g x hf hg hfb hgb n
  let M : ℕ → ℝ := fun k => A (k + 1) * W ^ (A (k + 1)) *
    (1 + p (k + (inputLoss + 1)) z)
  have hM (k : ℕ) : 0 ≤ M k :=
    mul_nonneg
      (mul_nonneg (zero_le_one.trans (hA (k + 1)))
        (Real.rpow_nonneg (zero_le_one.trans hW) _))
      (add_nonneg zero_le_one (apply_nonneg _ _))
  have houter (k : ℕ) (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k f (g x)‖ ≤ M (k - 1) := by
    have hi : k - 1 + (inputLoss + 1) = k + inputLoss := by omega
    simpa only [M, Nat.sub_add_cancel hk, hi] using hfb k hk
  have hinner (k : ℕ) (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k g x‖ ≤ M (k - 1) := by
    have hi : k - 1 + (inputLoss + 1) = k + inputLoss := by omega
    simpa only [M, Nat.sub_add_cancel hk, hi] using hgb k hk
  calc
    _ ≤ ∑ c : OrderedFinpartition (n + 1),
        ‖iteratedFDeriv ℝ c.length f (g x)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) g x‖ :=
      norm_iteratedFDeriv_comp_le_partition_sum hf hg (n + 1)
    _ ≤ ∑ c : OrderedFinpartition (n + 1),
        M (c.length - 1) * ∏ j, M (c.partSize j - 1) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul (houter c.length (c.length_pos (Nat.succ_pos n)))
        (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun j _ => hinner (c.partSize j) (c.partSize_pos j)))
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (hM (c.length - 1))
    _ = flowJetPolynomialEval (P n) M := (heP n M).symm
    _ ≤ _ := hb n z hz W hW

end ContinuousFlexibility.Analysis
