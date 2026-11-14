import ContinuousFlexibility.Analysis.NonlinearInversePolynomialBounds

/-!
# Finite raw jets suffice for a finite inverse-jet bound

The existing nonlinear inverse polynomial has weighted degree n.
Consequently it only uses raw entries through n. Truncating the input
sequence beyond that order gives a bound selected before the actual
maps, using the true inverse first derivative and only the required
finite forward jets.
-/

noncomputable section

universe u v

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem list_nat_mem_le_sum {k : ℕ} {ks : List ℕ} (hk : k ∈ ks) :
    k ≤ ks.sum := by
  induction ks with
  | nil => simp only [List.not_mem_nil] at hk
  | cons j ks ih =>
      rcases List.mem_cons.mp hk with he | hm
      · subst k
        exact Nat.le_add_right _ _
      · exact (ih hm).trans (Nat.le_add_left _ _)

private theorem flowJetPolynomialEval_congr_finite
    {P : FlowJetPolynomial} {n : ℕ} (hP : FlowJetPolynomialDegreeLE P n)
    {X Y : ℕ → ℝ} (hXY : ∀ k ≤ n, X k = Y k) :
    flowJetPolynomialEval P X = flowJetPolynomialEval P Y := by
  unfold flowJetPolynomialEval
  apply congrArg List.sum
  apply List.map_congr_left
  intro m hm
  have he : m.2.map X = m.2.map Y := by
    apply List.map_congr_left
    intro k hk
    exact hXY k ((list_nat_mem_le_sum hk).trans (hP m hm).2)
  rw [he]

/-- Order n+1 of an actual inverse requires the inverse first derivative
and original derivatives only through n+1. The bound precedes both maps. -/
theorem exists_nonlinearInverse_finiteJet_bound
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (M : ℕ → ℝ) (hM : ∀ k, 0 ≤ M k) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ f : E → F, ∀ g : F → E, ∀ x : F,
        ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
        f ∘ g =ᶠ[𝓝 x] (id : F → F) →
      ∀ L : F →L[ℝ] E,
        L.comp (fderiv ℝ f (g x)) = ContinuousLinearMap.id ℝ E →
        ‖L‖ ≤ M 0 →
        (∀ k : ℕ, 1 ≤ k → k ≤ n →
          ‖iteratedFDeriv ℝ (k + 1) f (g x)‖ ≤ M k) →
        ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ B := by
  obtain ⟨P, hP, hbound⟩ := exists_nonlinearInverse_spatialJet_polynomial.{u, v} n
  have hnonneg := flowJetPolynomialEval_nonneg hP hM
  refine ⟨1 + flowJetPolynomialEval P M, by linarith, ?_⟩
  intro f g x hf hg hfg L hL hLb hraw
  let X : ℕ → ℝ := fun k => if k ≤ n then M k else
    ‖iteratedFDeriv ℝ (k + 1) f (g x)‖
  have hX (k : ℕ) : 0 ≤ X k := by
    dsimp only [X]
    split_ifs
    · exact hM k
    · exact norm_nonneg _
  have hLx : ‖L‖ ≤ X 0 := by
    simpa only [X, if_pos (Nat.zero_le n)] using hLb
  have hrawx (k : ℕ) (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ (k + 1) f (g x)‖ ≤ X k := by
    by_cases hkn : k ≤ n
    · simpa only [X, if_pos hkn] using hraw k hk hkn
    · simp only [X, if_neg hkn, le_refl]
  have hj := hbound X hX E F f g x hf hg hfg L hL hLx hrawx
  have he : flowJetPolynomialEval P X = flowJetPolynomialEval P M :=
    flowJetPolynomialEval_congr_finite hP (fun k hk => by simp only [X, if_pos hk])
  exact hj.trans (he.trans_le (le_add_of_nonneg_left zero_le_one))

end ContinuousFlexibility.Analysis

