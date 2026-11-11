import ContinuousFlexibility.Analysis.AngularSineQuotient
import Mathlib.Algebra.BigOperators.Fin

/-!
# A fixed angular multiplier preserves the radial order

The multiplier is a translated fixed smooth function, raised to a fixed
power and multiplied by a scalar of absolute value at most one. Taking
the genuine radial boundary jet leaves it unchanged. The ordinary
one-dimensional Leibniz rule then bounds every mixed derivative with no
loss. The constant is independent of the radial order and translation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem exists_fixedAngularMultiplier_constant
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (n b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ c σ : ℝ, |σ| ≤ 1 → ∀ G : PolarPoint → ℝ, ContDiff ℝ ∞ G →
        ∀ a : ℕ, ∀ p : PolarPoint,
          p.2 - c ∈ Icc (-(Real.pi / 3)) (Real.pi / 3) →
          ∀ M : ℝ, 0 ≤ M →
            (∀ j : ℕ, j ≤ b → |mixedDerivative a j G p| ≤ M) →
            |mixedDerivative a b (fun q => (σ * ψ (q.2 - c)) ^ n * G q) p| ≤
              C * M := by
  let f : ℝ → ℝ := fun x => ψ x ^ n
  have hf : ContDiff ℝ ∞ f := hψ.pow n
  have hbounds (j : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ x ∈ Icc (-(Real.pi / 3)) (Real.pi / 3), |iteratedDeriv j f x| ≤ A := by
    obtain ⟨B, hB⟩ :=
      (isCompact_Icc : IsCompact (Icc (-(Real.pi / 3)) (Real.pi / 3))).exists_bound_of_continuousOn
        (hf.continuous_iteratedDeriv j (by simp)).continuousOn
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro x hx
    have h : |iteratedDeriv j f x| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB x hx
    exact h.trans (le_max_left _ _)
  choose A hA hbound using hbounds
  let C : ℝ := ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * A j
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hA j)
  refine ⟨C, hC, ?_⟩
  intro c σ hσ G hG a p hp M hM hGj
  let φ : ℝ → ℝ := fun θ => (σ * ψ (θ - c)) ^ n
  have hφ : ContDiff ℝ ∞ φ :=
    (contDiff_const.mul (hψ.comp (contDiff_id.sub contDiff_const))).pow n
  have hφform : φ = fun θ => σ ^ n * f (θ - c) := by
    funext θ
    dsimp only [φ, f]
    rw [mul_pow]
  have hσpow : |σ ^ n| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hσ
  have hφjet (j : ℕ) : |iteratedDeriv j φ p.2| ≤ A j := by
    rw [hφform, iteratedDeriv_const_mul_field, iteratedDeriv_comp_sub_const, abs_mul]
    calc
      _ ≤ 1 * A j :=
        mul_le_mul hσpow (hbound j (p.2 - c) hp) (abs_nonneg _) zero_le_one
      _ = A j := one_mul _
  let g : ℝ → ℝ := radialBoundaryJet G p.1 a
  have hg : ContDiff ℝ ∞ g :=
    contDiff_radialBoundaryJet_of_contDiffAt p.1 (fun _ => hG.contDiffAt) a
  have hproduct : ContDiff ℝ ∞ (fun q : PolarPoint => φ q.2 * G q) :=
    (hφ.comp contDiff_snd).mul hG
  have he : radialBoundaryJet (fun q : PolarPoint => φ q.2 * G q) p.1 a =
      fun θ => φ θ * g θ := by
    funext θ
    simp only [radialBoundaryJet, g, iteratedDeriv_const_mul_field]
  have hj : mixedDerivative a b (fun q : PolarPoint => φ q.2 * G q) p =
      iteratedDeriv b (fun θ => φ θ * g θ) p.2 := by
    rw [← iteratedDeriv_radialBoundaryJet_eq_mixedDerivative
      isOpen_univ hproduct.contDiffOn p.1 (fun _ => mem_univ _) a b p.2, he]
  have hgjet (j : ℕ) (hj : j ≤ b) : |iteratedDeriv j g p.2| ≤ M := by
    rw [iteratedDeriv_radialBoundaryJet_eq_mixedDerivative
      isOpen_univ hG.contDiffOn p.1 (fun _ => mem_univ _) a j p.2]
    exact hGj j hj
  change |mixedDerivative a b (fun q : PolarPoint => φ q.2 * G q) p| ≤ C * M
  rw [hj, iteratedDeriv_mul (hφ.contDiffAt.of_le (by simp))
    (hg.contDiffAt.of_le (by simp))]
  calc
    _ ≤ ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * A j * M := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (b.choose j))]
      have hb := mul_le_mul (hφjet j) (hgjet (b - j) (by omega))
        (abs_nonneg _) (hA j)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (b.choose j))
    _ = C * M := by simp only [C, Finset.sum_mul, mul_assoc]

end ContinuousFlexibility.Analysis
