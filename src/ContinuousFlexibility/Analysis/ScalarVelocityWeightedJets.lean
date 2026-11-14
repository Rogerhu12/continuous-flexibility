module

public import ContinuousFlexibility.Analysis.ScalarWeightedJetBounds

/-!
# Weighted angular jets of a correction velocity

The scalar expression is the actual velocity formula, with its two
inverse coordinate maps supplied as scalar functions. The component
weight and the radial cutoff derivative remain explicit in the bound.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem correctionVelocity_angular_weighted_bound
    {ι : Type*} (f a b d : ι → ℝ → ℝ) (c W : ι → ℝ)
    (hW : ∀ i, 0 < W i)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hd : ∀ i, ContDiff ℝ ∞ (d i))
    (hfbound : ∀ k : ℕ, 1 ≤ k → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (f i) θ| ≤ A)
    (habound : ∀ k : ℕ, 1 ≤ k → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (a i) θ| ≤ A)
    (hbbound : ∀ k : ℕ, 1 ≤ k → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (b i) θ| ≤ A)
    (hdbound : ∀ k : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (d i) θ| ≤ A * W i) :
    (∀ i, ContDiff ℝ ∞ (fun θ =>
      deriv (f i) (a i θ) * c i * d i (b i (a i θ)))) ∧
    ∀ n : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ i θ,
      |iteratedDeriv n (fun t =>
        deriv (f i) (a i t) * c i * d i (b i (a i t))) θ| ≤ A * |c i| * W i := by
  let β (i : ι) : ℝ → ℝ := fun θ => b i (a i θ)
  let q (i : ι) : ℝ → ℝ := fun θ => deriv (f i) (a i θ)
  have hdf (i : ι) : ContDiff ℝ ∞ (deriv (f i)) :=
    (contDiff_infty_iff_deriv.mp (hf i)).2
  have hβ (i : ι) : ContDiff ℝ ∞ (β i) := (hb i).comp (ha i)
  have hq (i : ι) : ContDiff ℝ ∞ (q i) := (hdf i).comp (ha i)
  have hβbound := positive_iteratedDeriv_comp_uniform_bound b a hb ha hbbound habound
  have hqbound (k : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (q i) θ| ≤ A := by
    apply iteratedDeriv_comp_uniform_bound (fun i => deriv (f i)) a isOpen_univ
      (fun i => (hdf i).contDiffOn) ha (fun _ _ => mem_univ _) k
    · intro j _
      obtain ⟨A, hA, hbound⟩ := hfbound (j + 1) (by omega)
      exact ⟨A, hA, fun i θ => by
        rw [← iteratedDeriv_succ']
        exact hbound i (a i θ)⟩
    · exact fun j hj _ => habound j hj
  have hdβbound (k : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (fun t => d i (β i t)) θ| ≤ A * W i :=
    iteratedDeriv_comp_weighted_bound d β W hW hd hβ k
      (fun j _ => hdbound j) (fun j hj _ => hβbound j hj)
  refine ⟨fun i => ((hq i).mul contDiff_const).mul ((hd i).comp (hβ i)), fun n => ?_⟩
  obtain ⟨A, hA, hbound⟩ := iteratedDeriv_mul_weighted_bound q
    (fun i t => d i (β i t)) W hW hq (fun i => (hd i).comp (hβ i)) n
    (fun j _ => hqbound j) (fun j _ => hdβbound j)
  refine ⟨A, hA, fun i θ => ?_⟩
  have heq : (fun t => deriv (f i) (a i t) * c i * d i (b i (a i t))) =
      fun t => c i * (q i t * d i (β i t)) := by
    funext t
    dsimp only [q, β]
    ring
  rw [heq, iteratedDeriv_const_mul_field, abs_mul]
  exact (mul_le_mul_of_nonneg_left (hbound i θ) (abs_nonneg _)).trans_eq (by ring)

theorem iteratedDeriv_reflected_drift_speed_abs_le
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (n : ℕ) {A : ℝ}
    (hA : ∀ θ, |iteratedDeriv n v θ| ≤ A) (θ : ℝ) :
    |iteratedDeriv n (fun t => (v t - v (-t)) / 2) θ| ≤ A ∧
      |iteratedDeriv n (fun t => (-v (-t) - v t) / 2) θ| ≤ A := by
  refine ⟨iteratedDeriv_oddPart_abs_le hv n hA θ, ?_⟩
  have heq : (fun t => (-v (-t) - v t) / 2) =
      fun t => -ContinuousFlexibility.Statements.evenPart v t := by
    funext t
    unfold ContinuousFlexibility.Statements.evenPart
    ring
  rw [heq, iteratedDeriv_fun_neg, abs_neg]
  exact iteratedDeriv_evenPart_abs_le hv n hA θ

end ContinuousFlexibility.Analysis
