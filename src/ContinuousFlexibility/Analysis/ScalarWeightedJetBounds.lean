import ContinuousFlexibility.Analysis.ScalarJetFamilyBounds

/-!
# Scalar jet estimates retaining a component weight

A positive weight depending only on the component commutes with angular
differentiation. Normalizing by that weight reduces composition and
product estimates to the uniform scalar bounds, and restores exactly the
same weight at the end.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem iteratedDeriv_comp_weighted_bound
    {ι : Type*} (f g : ι → ℝ → ℝ) (W : ι → ℝ) (hW : ∀ i, 0 < W i)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (n : ℕ)
    (hfbound : ∀ k : ℕ, k ≤ n → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, |iteratedDeriv k (f i) x| ≤ A * W i)
    (hgbound : ∀ k : ℕ, 1 ≤ k → k ≤ n → ∃ B : ℝ, 0 ≤ B ∧
      ∀ i x, |iteratedDeriv k (g i) x| ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i x,
      |iteratedDeriv n (fun y => f i (g i y)) x| ≤ K * W i := by
  let F (i : ι) : ℝ → ℝ := fun x => f i x / W i
  have hF (i : ι) : ContDiff ℝ ∞ (F i) := (hf i).div_const (W i)
  have hFb (k : ℕ) (hk : k ≤ n) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, |iteratedDeriv k (F i) (g i x)| ≤ A := by
    obtain ⟨A, hA, hb⟩ := hfbound k hk
    refine ⟨A, hA, fun i x => ?_⟩
    change |iteratedDeriv k (fun y => f i y / W i) (g i x)| ≤ A
    rw [iteratedDeriv_div_const, abs_div, abs_of_pos (hW i)]
    exact (div_le_iff₀ (hW i)).mpr (hb i (g i x))
  obtain ⟨K, hK, hb⟩ := iteratedDeriv_comp_uniform_bound F g isOpen_univ
    (fun i => (hF i).contDiffOn) hg (fun _ _ => mem_univ _) n hFb hgbound
  refine ⟨K, hK, fun i x => ?_⟩
  have heq : (fun y => f i (g i y)) = fun y => W i * F i (g i y) := by
    funext y
    dsimp only [F]
    field_simp [(hW i).ne'] <;> ring
  rw [heq, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (hW i)]
  exact (mul_le_mul_of_nonneg_left (hb i x) (hW i).le).trans_eq (mul_comm _ _)

theorem iteratedDeriv_mul_weighted_bound
    {ι : Type*} (f g : ι → ℝ → ℝ) (W : ι → ℝ) (hW : ∀ i, 0 < W i)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (n : ℕ)
    (hfbound : ∀ k : ℕ, k ≤ n → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, |iteratedDeriv k (f i) x| ≤ A)
    (hgbound : ∀ k : ℕ, k ≤ n → ∃ B : ℝ, 0 ≤ B ∧
      ∀ i x, |iteratedDeriv k (g i) x| ≤ B * W i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i x,
      |iteratedDeriv n (fun y => f i y * g i y) x| ≤ K * W i := by
  let G (i : ι) : ℝ → ℝ := fun x => g i x / W i
  have hG (i : ι) : ContDiff ℝ ∞ (G i) := (hg i).div_const (W i)
  have hGb (k : ℕ) (hk : k ≤ n) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ i x, |iteratedDeriv k (G i) x| ≤ B := by
    obtain ⟨B, hB, hb⟩ := hgbound k hk
    refine ⟨B, hB, fun i x => ?_⟩
    change |iteratedDeriv k (fun y => g i y / W i) x| ≤ B
    rw [iteratedDeriv_div_const, abs_div, abs_of_pos (hW i)]
    exact (div_le_iff₀ (hW i)).mpr (hb i x)
  obtain ⟨K, hK, hb⟩ := iteratedDeriv_mul_uniform_bound f G hf hG n hfbound hGb
  refine ⟨K, hK, fun i x => ?_⟩
  have heq : (fun y => f i y * g i y) = fun y => W i * (f i y * G i y) := by
    funext y
    dsimp only [G]
    field_simp [(hW i).ne'] <;> ring
  rw [heq, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (hW i)]
  exact (mul_le_mul_of_nonneg_left (hb i x) (hW i).le).trans_eq (mul_comm _ _)

end ContinuousFlexibility.Analysis
