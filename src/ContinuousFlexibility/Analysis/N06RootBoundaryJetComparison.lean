import ContinuousFlexibility.Analysis.N06RootJetTransportCalculus
import ContinuousFlexibility.Analysis.N06RootBoundaryFiniteFormulas

/-!
# Finite angular jet comparison for the root boundary polynomials

The common factor delta is retained under addition, multiplication and
angular differentiation. These elementary estimates are used on the
explicit physical boundary formulas, whose depth is only four.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

structure N06RootJetPair (n : ℕ) (M δ : ℝ) (f g : ℝ → ℝ) : Prop where
  left_smooth : ContDiff ℝ ∞ f
  right_smooth : ContDiff ℝ ∞ g
  left_bound : ∀ k, k ≤ n → ∀ θ, |iteratedDeriv k f θ| ≤ M
  right_bound : ∀ k, k ≤ n → ∀ θ, |iteratedDeriv k g θ| ≤ M
  difference : ∀ k, k ≤ n → ∀ θ,
    |iteratedDeriv k f θ - iteratedDeriv k g θ| ≤ M * δ

namespace N06RootJetPair

variable {n : ℕ} {M N R δ : ℝ} {f g h j : ℝ → ℝ}

theorem nonneg (H : N06RootJetPair n M δ f g) : 0 ≤ M :=
  (abs_nonneg _).trans (H.left_bound 0 (Nat.zero_le n) 0)

theorem restrict (H : N06RootJetPair n M δ f g) {m : ℕ} (hm : m ≤ n) :
    N06RootJetPair m M δ f g :=
  ⟨H.left_smooth, H.right_smooth,
    fun k hk θ => H.left_bound k (hk.trans hm) θ,
    fun k hk θ => H.right_bound k (hk.trans hm) θ,
    fun k hk θ => H.difference k (hk.trans hm) θ⟩

theorem enlarge (H : N06RootJetPair n M δ f g) (hδ : 0 ≤ δ) (hM : M ≤ R) :
    N06RootJetPair n R δ f g :=
  ⟨H.left_smooth, H.right_smooth,
    fun k hk θ => (H.left_bound k hk θ).trans hM,
    fun k hk θ => (H.right_bound k hk θ).trans hM,
    fun k hk θ => (H.difference k hk θ).trans (mul_le_mul_of_nonneg_right hM hδ)⟩

theorem neg (H : N06RootJetPair n M δ f g) :
    N06RootJetPair n M δ (fun θ => -f θ) (fun θ => -g θ) := by
  refine ⟨H.left_smooth.neg, H.right_smooth.neg, ?_, ?_, ?_⟩
  · intro k hk θ
    simpa only [iteratedDeriv_fun_neg, abs_neg] using H.left_bound k hk θ
  · intro k hk θ
    simpa only [iteratedDeriv_fun_neg, abs_neg] using H.right_bound k hk θ
  · intro k hk θ
    rw [iteratedDeriv_fun_neg, iteratedDeriv_fun_neg, neg_sub_neg, abs_sub_comm]
    exact H.difference k hk θ

theorem const_mul (H : N06RootJetPair n M δ f g) (c : ℝ) :
    N06RootJetPair n (|c| * M) δ (fun θ => c * f θ) (fun θ => c * g θ) := by
  refine ⟨contDiff_const.mul H.left_smooth, contDiff_const.mul H.right_smooth, ?_, ?_, ?_⟩
  · intro k hk θ
    rw [iteratedDeriv_const_mul_field, abs_mul]
    exact mul_le_mul_of_nonneg_left (H.left_bound k hk θ) (abs_nonneg _)
  · intro k hk θ
    rw [iteratedDeriv_const_mul_field, abs_mul]
    exact mul_le_mul_of_nonneg_left (H.right_bound k hk θ) (abs_nonneg _)
  · intro k hk θ
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, ← mul_sub, abs_mul]
    exact (mul_le_mul_of_nonneg_left (H.difference k hk θ) (abs_nonneg _)).trans_eq
      (mul_assoc _ _ _).symm

theorem const_mul_le_one (H : N06RootJetPair n M δ f g) (hδ : 0 ≤ δ)
    {c : ℝ} (hc : |c| ≤ 1) :
    N06RootJetPair n M δ (fun θ => c * f θ) (fun θ => c * g θ) :=
  (H.const_mul c).enlarge hδ
    ((mul_le_mul_of_nonneg_right hc H.nonneg).trans_eq (one_mul M))

theorem add (H : N06RootJetPair n M δ f g) (J : N06RootJetPair n N δ h j) :
    N06RootJetPair n (M + N) δ (fun θ => f θ + h θ) (fun θ => g θ + j θ) := by
  refine ⟨H.left_smooth.add J.left_smooth, H.right_smooth.add J.right_smooth, ?_, ?_, ?_⟩
  · intro k hk θ
    rw [iteratedDeriv_fun_add (H.left_smooth.contDiffAt.of_le (by simp))
      (J.left_smooth.contDiffAt.of_le (by simp))]
    exact (abs_add_le _ _).trans (add_le_add (H.left_bound k hk θ) (J.left_bound k hk θ))
  · intro k hk θ
    rw [iteratedDeriv_fun_add (H.right_smooth.contDiffAt.of_le (by simp))
      (J.right_smooth.contDiffAt.of_le (by simp))]
    exact (abs_add_le _ _).trans (add_le_add (H.right_bound k hk θ) (J.right_bound k hk θ))
  · intro k hk θ
    rw [iteratedDeriv_fun_add (H.left_smooth.contDiffAt.of_le (by simp))
      (J.left_smooth.contDiffAt.of_le (by simp)),
      iteratedDeriv_fun_add (H.right_smooth.contDiffAt.of_le (by simp))
        (J.right_smooth.contDiffAt.of_le (by simp))]
    have he : iteratedDeriv k f θ + iteratedDeriv k h θ -
        (iteratedDeriv k g θ + iteratedDeriv k j θ) =
      (iteratedDeriv k f θ - iteratedDeriv k g θ) +
        (iteratedDeriv k h θ - iteratedDeriv k j θ) := by ring
    rw [he]
    exact ((abs_add_le _ _).trans (add_le_add (H.difference k hk θ)
      (J.difference k hk θ))).trans_eq (add_mul M N δ).symm

theorem sub (H : N06RootJetPair n M δ f g) (J : N06RootJetPair n N δ h j) :
    N06RootJetPair n (M + N) δ (fun θ => f θ - h θ) (fun θ => g θ - j θ) := by
  simpa only [sub_eq_add_neg] using H.add J.neg

theorem deriv (H : N06RootJetPair (n + 1) M δ f g) :
    N06RootJetPair n M δ (deriv f) (deriv g) := by
  refine ⟨(contDiff_infty_iff_deriv.mp H.left_smooth).2,
    (contDiff_infty_iff_deriv.mp H.right_smooth).2, ?_, ?_, ?_⟩
  · intro k hk θ
    rw [← iteratedDeriv_succ']
    exact H.left_bound (k + 1) (by omega) θ
  · intro k hk θ
    rw [← iteratedDeriv_succ']
    exact H.right_bound (k + 1) (by omega) θ
  · intro k hk θ
    rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
    exact H.difference (k + 1) (by omega) θ

private theorem iteratedDeriv_mul_bound
    {u v : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (k : ℕ) (θ : ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hU : ∀ l, l ≤ k → |iteratedDeriv l u θ| ≤ A)
    (hV : ∀ l, l ≤ k → |iteratedDeriv l v θ| ≤ B) :
    |iteratedDeriv k (fun η => u η * v η) θ| ≤ (2 : ℝ) ^ k * A * B := by
  have h := n06_norm_iteratedFDeriv_mul_at_le hu.contDiffAt hv.contDiffAt k hA hB
    (fun l hl => by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
        using hU l hl)
    (fun l hl => by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
        using hV l hl)
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using h

theorem mul (H : N06RootJetPair n M δ f g) (J : N06RootJetPair n N δ h j)
    (hδ : 0 ≤ δ) :
    N06RootJetPair n ((2 : ℝ) ^ (n + 1) * M * N) δ
      (fun θ => f θ * h θ) (fun θ => g θ * j θ) := by
  have hscale (k : ℕ) (hk : k ≤ n + 1) :
      (2 : ℝ) ^ k * M * N ≤ (2 : ℝ) ^ (n + 1) * M * N :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) H.nonneg) J.nonneg
  refine ⟨H.left_smooth.mul J.left_smooth, H.right_smooth.mul J.right_smooth, ?_, ?_, ?_⟩
  · intro k hk θ
    exact (iteratedDeriv_mul_bound H.left_smooth J.left_smooth k θ H.nonneg J.nonneg
      (fun l hl => H.left_bound l (hl.trans hk) θ)
      (fun l hl => J.left_bound l (hl.trans hk) θ)).trans (hscale k (by omega))
  · intro k hk θ
    exact (iteratedDeriv_mul_bound H.right_smooth J.right_smooth k θ H.nonneg J.nonneg
      (fun l hl => H.right_bound l (hl.trans hk) θ)
      (fun l hl => J.right_bound l (hl.trans hk) θ)).trans (hscale k (by omega))
  · intro k hk θ
    have hdf (l : ℕ) (hl : l ≤ k) :
        |iteratedDeriv l (fun η => f η - g η) θ| ≤ M * δ := by
      rw [iteratedDeriv_fun_sub (H.left_smooth.contDiffAt.of_le (by simp))
        (H.right_smooth.contDiffAt.of_le (by simp))]
      exact H.difference l (hl.trans hk) θ
    have hdh (l : ℕ) (hl : l ≤ k) :
        |iteratedDeriv l (fun η => h η - j η) θ| ≤ N * δ := by
      rw [iteratedDeriv_fun_sub (J.left_smooth.contDiffAt.of_le (by simp))
        (J.right_smooth.contDiffAt.of_le (by simp))]
      exact J.difference l (hl.trans hk) θ
    have h₁ := iteratedDeriv_mul_bound H.left_smooth
      (J.left_smooth.sub J.right_smooth) k θ H.nonneg (mul_nonneg J.nonneg hδ)
      (fun l hl => H.left_bound l (hl.trans hk) θ) hdh
    have h₂ := iteratedDeriv_mul_bound (H.left_smooth.sub H.right_smooth)
      J.right_smooth k θ (mul_nonneg H.nonneg hδ) J.nonneg hdf
      (fun l hl => J.right_bound l (hl.trans hk) θ)
    have he : (fun η => f η * h η - g η * j η) =
        fun η => f η * (h η - j η) + (f η - g η) * j η := by
      funext η
      ring
    rw [← iteratedDeriv_fun_sub
      ((H.left_smooth.mul J.left_smooth).contDiffAt.of_le (by simp))
      ((H.right_smooth.mul J.right_smooth).contDiffAt.of_le (by simp)), he,
      iteratedDeriv_fun_add
        ((H.left_smooth.mul (J.left_smooth.sub J.right_smooth)).contDiffAt.of_le (by simp))
        (((H.left_smooth.sub H.right_smooth).mul J.right_smooth).contDiffAt.of_le (by simp))]
    calc
      _ ≤ (2 : ℝ) ^ k * M * (N * δ) + (2 : ℝ) ^ k * (M * δ) * N :=
        (abs_add_le _ _).trans (add_le_add h₁ h₂)
      _ = ((2 : ℝ) ^ (k + 1) * M * N) * δ := by rw [pow_succ]; ring
      _ ≤ ((2 : ℝ) ^ (n + 1) * M * N) * δ :=
        mul_le_mul_of_nonneg_right (hscale (k + 1) (by omega)) hδ

end N06RootJetPair

end ContinuousFlexibility.Analysis
