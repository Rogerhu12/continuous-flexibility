module

public import ContinuousFlexibility.Analysis.NonlinearInversePolynomialBounds

/-!
# A fixed ordinary polynomial envelope for finite inverse jets

The true inverse polynomial has finitely many factors in each monomial.
Their number, including repeated zero-weight atoms, controls the ordinary
power of a common numerical bound. Weighted derivative degree is used
only to restrict which finite forward derivatives are needed.
This is a new reconstruction after the workspace reset.
-/

@[expose] public section

noncomputable section

universe u v

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem inversePolynomial_const_product (ks : List ℕ) (M : ℝ) :
    (ks.map (fun _ => M)).prod = M ^ ks.length := by
  induction ks with
  | nil => simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero]
  | cons k ks ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, ih, pow_succ]
      exact mul_comm _ _

private theorem inversePolynomial_constant_envelope (P : FlowJetPolynomial) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ d : ℕ, ∀ {M : ℝ}, 1 ≤ M →
      flowJetPolynomialEval P (fun _ => M) ≤ C * M ^ d := by
  induction P with
  | nil =>
      refine ⟨1, le_rfl, 0, ?_⟩
      intro M hM
      simp only [flowJetPolynomialEval_nil, pow_zero, mul_one, zero_le_one]
  | cons m P ih =>
      obtain ⟨C, hC, d, hbound⟩ := ih
      refine ⟨|m.1| + C, ?_, max m.2.length d, ?_⟩
      · linarith [abs_nonneg m.1]
      · intro M hM
        rw [flowJetPolynomialEval_cons, inversePolynomial_const_product]
        calc
          m.1 * M ^ m.2.length + flowJetPolynomialEval P (fun _ => M)
              ≤ |m.1| * M ^ m.2.length + C * M ^ d :=
            add_le_add (mul_le_mul_of_nonneg_right (le_abs_self m.1)
              (pow_nonneg (zero_le_one.trans hM) _)) (hbound hM)
          _ ≤ |m.1| * M ^ max m.2.length d + C * M ^ max m.2.length d :=
            add_le_add
              (mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hM (Nat.le_max_left _ _)) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hM (Nat.le_max_right _ _)) (zero_le_one.trans hC))
          _ = (|m.1| + C) * M ^ max m.2.length d := by ring

private theorem inversePolynomial_index_le_sum {k : ℕ} {ks : List ℕ}
    (hk : k ∈ ks) : k ≤ ks.sum := by
  induction ks with
  | nil => simp only [List.not_mem_nil] at hk
  | cons j ks ih =>
      rcases List.mem_cons.mp hk with he | hm
      · subst k
        exact Nat.le_add_right _ _
      · exact (ih hm).trans (Nat.le_add_left _ _)

/-- The numerical coefficient and exponent precede the common bound and
the actual inverse pair. Only forward orders through n+1 are inputs. -/
theorem exists_nonlinearInverse_finiteJet_polynomial_envelope
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ d : ℕ, ∀ {M : ℝ}, 1 ≤ M →
      ∀ f : E → F, ∀ g : F → E, ∀ x : F,
        ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
        f ∘ g =ᶠ[𝓝 x] (id : F → F) →
      ∀ L : F →L[ℝ] E,
        L.comp (fderiv ℝ f (g x)) = ContinuousLinearMap.id ℝ E →
        ‖L‖ ≤ M →
        (∀ k : ℕ, 1 ≤ k → k ≤ n →
          ‖iteratedFDeriv ℝ (k + 1) f (g x)‖ ≤ M) →
        ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ C * M ^ d := by
  obtain ⟨P, hP, hbound⟩ := exists_nonlinearInverse_spatialJet_polynomial.{u, v} n
  obtain ⟨C, hC, d, hmajor⟩ := inversePolynomial_constant_envelope P
  refine ⟨C, hC, d, ?_⟩
  intro M hM f g x hf hg hfg L hL hLb hraw
  let X : ℕ → ℝ := fun k => if k ≤ n then M else
    ‖iteratedFDeriv ℝ (k + 1) f (g x)‖
  have hX (k : ℕ) : 0 ≤ X k := by
    dsimp only [X]
    split_ifs
    · exact zero_le_one.trans hM
    · exact norm_nonneg _
  have hLx : ‖L‖ ≤ X 0 := by
    simpa only [X, if_pos (Nat.zero_le n)] using hLb
  have hrawx (k : ℕ) (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ (k + 1) f (g x)‖ ≤ X k := by
    by_cases hkn : k ≤ n
    · simpa only [X, if_pos hkn] using hraw k hk hkn
    · simp only [X, if_neg hkn, le_refl]
  have hj := hbound X hX E F f g x hf hg hfg L hL hLx hrawx
  have he : flowJetPolynomialEval P X = flowJetPolynomialEval P (fun _ => M) := by
    unfold flowJetPolynomialEval
    apply congrArg List.sum
    apply List.map_congr_left
    intro m hm
    have hmap : m.2.map X = m.2.map (fun _ => M) := by
      apply List.map_congr_left
      intro k hk
      have hkn : k ≤ n := (inversePolynomial_index_le_sum hk).trans (hP m hm).2
      simp only [X, if_pos hkn]
    rw [hmap]
  exact hj.trans (he.trans_le (hmajor hM))

end ContinuousFlexibility.Analysis
