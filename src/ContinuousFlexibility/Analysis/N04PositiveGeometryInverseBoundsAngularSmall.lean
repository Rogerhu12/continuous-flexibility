import ContinuousFlexibility.Analysis.N04RealizationPositiveAngularCircle
import ContinuousFlexibility.Analysis.CircleSingleComponent

/-!
# Uniform low angular control for the stored interpolation

The actual finite Taylor interpolation has uniformly bounded angular
jets when its finite endpoint displacements do. The estimate uses only
the already stored width being at most one. In particular it neither
changes that width nor introduces a component-dependent inverse constant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem angular_displacement_sum
    (n : ℕ) (c x θ : ℝ) (A : ℕ → ℝ → ℝ) :
    (∑ j : Fin (n + 1), (x - c) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ) *
      (A j θ - if (j : ℕ) = 0 then θ else 0)) =
        boundaryTaylorPolynomial n c A (x, θ) - θ := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (x - c) ^ j / (j.factorial : ℝ) * (A j θ - if j = 0 then θ else 0))]
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
        (A j θ / (j.factorial : ℝ) * (x - c) ^ j -
          if j = 0 then θ else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = 0
      · subst j
        simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
          one_mul, if_pos rfl, mul_one]
      · simp only [if_neg hj, sub_zero]
        ring
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp [boundaryTaylorPolynomial]

private theorem angular_patch_displacement_sum
    (n : ℕ) (c δ x θ : ℝ) (A : ℕ → ℝ → ℝ) :
    positiveAngularTaylorPatch n c δ A (x, θ) - θ =
      ∑ j : Fin (n + 1),
        (positiveEndpointCutoff c δ x *
          ((x - c) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ))) *
          (A j θ - if (j : ℕ) = 0 then θ else 0) := by
  rw [show (∑ j : Fin (n + 1),
      (positiveEndpointCutoff c δ x *
        ((x - c) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ))) *
        (A j θ - if (j : ℕ) = 0 then θ else 0)) =
      positiveEndpointCutoff c δ x * ∑ j : Fin (n + 1),
        ((x - c) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) *
          (A j θ - if (j : ℕ) = 0 then θ else 0) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [angular_displacement_sum]
  simp only [positiveAngularTaylorPatch]
  ring

/-- Every actual cutoff Taylor weight is bounded by one on the entire
radial line. No reciprocal collar width occurs in this angular estimate. -/
theorem n04PositiveGeometry_angularTaylorWeight_abs_le_one
    {c δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (j : ℕ) (x : ℝ) :
    |positiveEndpointCutoff c δ x * ((x - c) ^ j / (j.factorial : ℝ))| ≤ 1 := by
  apply abs_positiveEndpointCutoff_mul_le hδ zero_le_one
  intro t ht
  have htc : |t - c| ≤ 1 :=
    (show |t - c| < δ by simpa only [Metric.mem_ball, Real.dist_eq] using ht).le.trans hδone
  have hfact : (1 : ℝ) ≤ (j.factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos j)
  have hfactpos : (0 : ℝ) < (j.factorial : ℝ) := zero_lt_one.trans_le hfact
  rw [abs_div, abs_pow, abs_of_pos hfactpos]
  apply (div_le_one hfactpos).mpr
  exact (pow_le_one₀ (abs_nonneg _) htc).trans hfact

private theorem angular_patch_jet_bound
    {n b : ℕ} {A : ℕ → ℝ → ℝ} {c δ M : ℝ}
    (hA : ∀ j ≤ n, ContDiff ℝ ∞ (A j))
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hM : 0 ≤ M)
    (hbound : ∀ j ≤ n, ∀ θ,
      |iteratedDeriv b (fun η => A j η - if j = 0 then η else 0) θ| ≤ M)
    (x θ : ℝ) :
    |iteratedDeriv b
      (fun η => positiveAngularTaylorPatch n c δ A (x, η) - η) θ| ≤
      ((n + 1 : ℕ) : ℝ) * M := by
  let w : Fin (n + 1) → ℝ := fun j =>
    positiveEndpointCutoff c δ x * ((x - c) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ))
  let f : Fin (n + 1) → ℝ → ℝ := fun j η => A j η - if (j : ℕ) = 0 then η else 0
  have hf (j : Fin (n + 1)) : ContDiff ℝ ∞ (f j) := by
    dsimp only [f]
    by_cases hj : (j : ℕ) = 0
    · simp only [if_pos hj]
      exact (hA j (Nat.le_of_lt_succ j.isLt)).sub contDiff_id
    · simp only [if_neg hj, sub_zero]
      exact hA j (Nat.le_of_lt_succ j.isLt)
  have hsum : (fun η => positiveAngularTaylorPatch n c δ A (x, η) - η) =
      (fun η => ∑ j, w j * f j η) :=
    funext (fun η => angular_patch_displacement_sum n c δ x η A)
  rw [hsum, iteratedDeriv_fun_sum (fun j _ =>
    (contDiff_const.mul (hf j)).contDiffAt.of_le (by simp))]
  simp only [iteratedDeriv_const_mul_field]
  calc
    _ ≤ ∑ j : Fin (n + 1), |w j * iteratedDeriv b (f j) θ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (n + 1), M := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul
        (n04PositiveGeometry_angularTaylorWeight_abs_le_one hδ hδone j x)
        (hbound j (Nat.le_of_lt_succ j.isLt) θ) (abs_nonneg _) zero_le_one).trans_eq
          (one_mul M)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Finite endpoint angular jets bound the literal whole interpolation,
uniformly over every radial point. -/
theorem n04PositiveGeometry_angularInterpolation_defect_jet_bound
    {n b : ℕ} {A : Bool → ℕ → ℝ → ℝ} {l r δ M : ℝ}
    (hA : ∀ side j, j ≤ n → ContDiff ℝ ∞ (A side j))
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hM : 0 ≤ M)
    (hbound : ∀ side j, j ≤ n → ∀ θ,
      |iteratedDeriv b (fun η => A side j η - if j = 0 then η else 0) θ| ≤ M)
    (x θ : ℝ) :
    |iteratedDeriv b
      (fun η => positiveAngularTaylorInterpolation n l r δ A (x, η) - η) θ| ≤
      2 * ((n + 1 : ℕ) : ℝ) * M := by
  have hsplit : (fun η => positiveAngularTaylorInterpolation n l r δ A (x, η) - η) =
      (fun η => (positiveAngularTaylorPatch n l δ (A false) (x, η) - η) +
        (positiveAngularTaylorPatch n r δ (A true) (x, η) - η)) := by
    funext η
    simp only [positiveAngularTaylorInterpolation]
    ring
  have hsmooth (side : Bool) (c : ℝ) : ContDiff ℝ ∞
      (fun η => positiveAngularTaylorPatch n c δ (A side) (x, η) - η) :=
    ((contDiff_positiveAngularTaylorPatch (hA side) c δ).comp
      (contDiff_const.prodMk contDiff_id)).sub contDiff_id
  rw [hsplit, iteratedDeriv_fun_add
    ((hsmooth false l).contDiffAt.of_le (by simp))
    ((hsmooth true r).contDiffAt.of_le (by simp))]
  exact (abs_add_le _ _).trans ((add_le_add
    (angular_patch_jet_bound (hA false) hδ hδone hM (hbound false) x θ)
    (angular_patch_jet_bound (hA true) hδ hδone hM (hbound true) x θ)).trans_eq (by ring))

/-- A common low endpoint variation yields a fixed angular lower bound
for the same stored interpolation. -/
theorem n04PositiveGeometry_angularInterpolation_lower_of_small
    {n : ℕ} {A : Bool → ℕ → ℝ → ℝ} {l r δ M : ℝ}
    (hA : ∀ side j, j ≤ n → ContDiff ℝ ∞ (A side j))
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hM : 0 ≤ M)
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * M ≤ 3 / 4)
    (hbound : ∀ side j, j ≤ n → ∀ θ,
      |deriv (fun η => A side j η - if j = 0 then η else 0) θ| ≤ M)
    (x θ : ℝ) :
    (1 / 4 : ℝ) ≤ deriv
      (fun η => positiveAngularTaylorInterpolation n l r δ A (x, η)) θ := by
  have hjet := n04PositiveGeometry_angularInterpolation_defect_jet_bound
    (b := 1) hA hδ hδone hM (by simpa only [iteratedDeriv_one] using hbound) x θ
  have hsmooth : ContDiff ℝ ∞
      (fun η => positiveAngularTaylorInterpolation n l r δ A (x, η)) :=
    (contDiff_positiveAngularTaylorInterpolation hA l r δ).comp
      (contDiff_const.prodMk contDiff_id)
  rw [iteratedDeriv_one, deriv_fun_sub (hsmooth.differentiable (by simp) θ)
    (differentiableAt_id), deriv_id''] at hjet
  have hlow := (abs_le.mp hjet).1
  linarith

/-- Using the fixed circle label zero turns the preceding pointwise
estimate into one circle bound chosen before the physical component,
the endpoint data, the radius, and the stored width. -/
theorem n04PositiveGeometry_angularInterpolation_fixedCircle_bound
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S)
    (hM : ∀ i, 0 ≤ T.M (T.sample i)) (hH : ∀ i, 0 ≤ T.H (T.sample i))
    (n s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Bool → ℕ → ℝ → ℝ) (l r δ M : ℝ),
      (∀ side j, j ≤ n → ContDiff ℝ ∞ (A side j)) →
      0 < δ → δ ≤ 1 → 0 ≤ M →
      (∀ side j, j ≤ n → ∀ b ≤ s, ∀ θ,
        |iteratedDeriv b (fun η => A side j η - if j = 0 then η else 0) θ| ≤ M) →
      ∀ (x : ℝ) (F : S.Space),
        S.decode F = circleSingleComponentField 0
          (fun θ => positiveAngularTaylorInterpolation n l r δ A (x, θ) - θ) →
        S.grading s F ≤ C * M := by
  classical
  let a : ℕ → ℝ := fun j =>
    Real.sqrt ((Fintype.card (CircleJetIndex j) : ℝ) * Real.pi) *
      (max 1 (T.M (T.sample 0))) ^ j * T.H (T.sample 0) ^ (-γ)
  have ha (j : ℕ) : 0 ≤ a j := by
    dsimp only [a]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
      (Real.rpow_nonneg (hH 0) _)
  let B : ℝ := 1 + ∑ j ∈ Finset.range (s + 1), a j
  have hB : 0 < B := by
    have hsum := Finset.sum_nonneg (fun j (_hj : j ∈ Finset.range (s + 1)) => ha j)
    dsimp only [B]
    linarith
  have haB (j : ℕ) (hj : j ≤ s) : a j ≤ B := by
    have hsingle := Finset.single_le_sum (fun k (_hk : k ∈ Finset.range (s + 1)) => ha k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    dsimp only [B]
    linarith
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  refine ⟨B * (2 * ((n + 1 : ℕ) : ℝ)), mul_pos hB (mul_pos (by norm_num) hN), ?_⟩
  intro A l r δ M hA hδ hδone hM₀ hbound x F hdecode
  have hC : 0 ≤ (B * (2 * ((n + 1 : ℕ) : ℝ))) * M :=
    mul_nonneg (mul_nonneg hB.le (mul_nonneg (by norm_num) hN.le)) hM₀
  apply (circleGrading_le_iff_circleNorm hS s F hC).mpr
  intro j hj
  rw [hdecode]
  have hsmooth : ContDiff ℝ ∞
      (fun θ => positiveAngularTaylorInterpolation n l r δ A (x, θ) - θ) :=
    ((contDiff_positiveAngularTaylorInterpolation hA l r δ).comp
      (contDiff_const.prodMk contDiff_id)).sub contDiff_id
  have hlow : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) * M :=
    mul_nonneg (mul_nonneg (by norm_num) hN.le) hM₀
  have hjets (b : ℕ) (hb : b ≤ j) (θ : ℝ) :=
    n04PositiveGeometry_angularInterpolation_defect_jet_bound (b := b)
      hA hδ hδone hM₀
      (fun side k hk η => hbound side k hk b (hb.trans hj) η) x θ
  have hn := circleSingleComponentField_norm_le hM hH 0 j _ hsmooth hlow hjets
  exact hn.trans ((mul_le_mul_of_nonneg_right (haB j hj) hlow).trans_eq (by ring))

end ContinuousFlexibility.Analysis
