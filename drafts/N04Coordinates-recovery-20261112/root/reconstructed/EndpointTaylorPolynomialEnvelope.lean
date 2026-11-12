import ContinuousFlexibility.Analysis.BoundaryTaylorBounds
import ContinuousFlexibility.Analysis.PositiveHeightTaylorInterpolation

/-!
# Polynomial jets of the actual endpoint Taylor correction

The chosen collar is used literally. Its inverse width and the finitely
many angular coefficient jets enter one polynomial envelope, with a
constant fixed before the collar or boundary data are supplied.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

/-- A single actual endpoint patch is the existing extension with zero
data at an auxiliary point one collar-width away. This is an algebraic
identity, not a change to the physical component or its partition. -/
private theorem endpointTaylorPatch_eq_extension
    (n : ℕ) (c : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (A : ℕ → ℝ → ℝ) (p : PolarPoint) :
    positiveEndpointCutoff c δ p.1 * boundaryTaylorPolynomial n c A p =
      boundaryTaylorExtension n c (c + δ) A (fun _ _ => 0) p := by
  have hw : |c + δ - c| = δ := by
    rw [add_sub_cancel_left, abs_of_pos hδ]
  simp only [boundaryTaylorExtension, hw, positiveEndpointCutoff,
    boundaryTaylorPolynomial, zero_div, zero_mul, Finset.sum_const_zero,
    mul_zero, add_zero]

/-- Uniform finite angular data and the inverse of the actual selected
width control every ordinary full jet of the constructed correction. -/
theorem exists_endpointTaylorCorrection_polynomial_envelope (n N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {M δ : ℝ}, 1 ≤ M → 0 < δ → δ ≤ 1 → δ⁻¹ ≤ M →
      ∀ (l r : ℝ) (A : Bool → ℕ → ℝ → ℝ),
      (∀ side j, j ≤ n → ContDiff ℝ ∞ (A side j)) →
      (∀ side j, j ≤ n → ∀ b, b ≤ N → ∀ θ,
        |iteratedDeriv b (A side j) θ| ≤ M) →
      ∀ k, k ≤ N → ∀ p : PolarPoint,
        ‖iteratedFDeriv ℝ k (endpointTaylorCorrection n l r δ A) p‖ ≤
          C * M ^ (N + 1) := by
  classical
  choose K hK hbound using (fun a : ℕ => exists_boundaryTaylorExtension_mixed_bound n a)
  let B : ℝ := 1 + ∑ a ∈ Finset.range (N + 1), K a
  have hB : 1 ≤ B := by
    have hs : 0 ≤ ∑ a ∈ Finset.range (N + 1), K a :=
      Finset.sum_nonneg fun a _ => (hK a).le
    dsimp only [B]
    linarith only [hs]
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hKB (a : ℕ) (ha : a ≤ N) : K a ≤ B :=
    (Finset.single_le_sum (fun a _ => (hK a).le)
      (Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)
  let C : ℝ := 1 + 2 * (2 : ℝ) ^ N * B * ((n + 1 : ℕ) : ℝ)
  have hC : 1 ≤ C := by
    have ht : 0 ≤ 2 * (2 : ℝ) ^ N * B * ((n + 1 : ℕ) : ℝ) := by positivity
    dsimp only [C]
    linarith only [ht]
  refine ⟨C, hC, ?_⟩
  intro M δ hM hδ hδone hδinv l r A hA hcoeff k hk p
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hpatch (c : ℝ) (side : Bool) :
      ‖iteratedFDeriv ℝ k
        (boundaryTaylorExtension n c (c + δ) (A side) (fun _ _ => 0)) p‖ ≤
        (2 : ℝ) ^ N * B * ((n + 1 : ℕ) : ℝ) * M ^ (N + 1) := by
    have hc : c ≠ c + δ := by linarith only [hδ]
    have hw : |c + δ - c| = δ := by
      rw [add_sub_cancel_left, abs_of_pos hδ]
    have hsmooth := contDiff_boundaryTaylorExtension (hA side)
      (fun _ _ => contDiff_const) c (c + δ)
    have hnonneg : 0 ≤ B * ((n + 1 : ℕ) : ℝ) * M ^ (N + 1) := by positivity
    have hfull := norm_iteratedFDeriv_le_of_mixedDerivative isOpen_univ
      hsmooth.contDiffOn k (mem_univ p) hnonneg (fun a b hab => by
        have ha : a ≤ N := by omega
        have hb : b ≤ N := by omega
        have hinv : (δ⁻¹) ^ a ≤ M ^ N :=
          (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hδinv a).trans
            (pow_le_pow_right₀ hM ha)
        have hsum :
            (∑ j ∈ Finset.range (n + 1), δ ^ j *
              |iteratedDeriv b (A side j) p.2|) ≤ ((n + 1 : ℕ) : ℝ) * M := by
          calc
            _ ≤ ∑ _j ∈ Finset.range (n + 1), M := by
              apply Finset.sum_le_sum
              intro j hj
              exact (mul_le_mul (pow_le_one₀ hδ.le hδone)
                (hcoeff side j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)
                  b hb p.2) (abs_nonneg _) zero_le_one).trans_eq (one_mul M)
            _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have he :
            |mixedDerivative a b
              (boundaryTaylorExtension n c (c + δ) (A side) (fun _ _ => 0)) p| ≤
              K a * (δ⁻¹) ^ a * (∑ j ∈ Finset.range (n + 1),
                δ ^ j * |iteratedDeriv b (A side j) p.2|) := by
          simpa only [hw, iteratedDeriv_fun_const_zero, abs_zero, add_zero] using
            hbound a c (c + δ) hc (A side) (fun _ _ => 0)
              (hA side) (fun _ _ => contDiff_const) b p
        rw [Real.norm_eq_abs]
        calc
          _ ≤ K a * (δ⁻¹) ^ a * (∑ j ∈ Finset.range (n + 1),
              δ ^ j * |iteratedDeriv b (A side j) p.2|) := he
          _ ≤ (B * M ^ N) * (((n + 1 : ℕ) : ℝ) * M) :=
            mul_le_mul
              (mul_le_mul (hKB a ha) hinv (pow_nonneg (inv_nonneg.mpr hδ.le) _) hB0)
              hsum (Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hδ.le _) (abs_nonneg _))
              (mul_nonneg hB0 (pow_nonneg hM0 _))
          _ = B * ((n + 1 : ℕ) : ℝ) * M ^ (N + 1) := by rw [pow_succ]; ring)
    calc
      _ ≤ (2 : ℝ) ^ k * (B * ((n + 1 : ℕ) : ℝ) * M ^ (N + 1)) := hfull
      _ ≤ (2 : ℝ) ^ N * (B * ((n + 1 : ℕ) : ℝ) * M ^ (N + 1)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hnonneg
      _ = _ := by ring
  let F : PolarPoint → ℝ := boundaryTaylorExtension n l (l + δ) (A false) (fun _ _ => 0)
  let G : PolarPoint → ℝ := boundaryTaylorExtension n r (r + δ) (A true) (fun _ _ => 0)
  have hF : ContDiff ℝ ∞ F :=
    contDiff_boundaryTaylorExtension (hA false) (fun _ _ => contDiff_const) l (l + δ)
  have hG : ContDiff ℝ ∞ G :=
    contDiff_boundaryTaylorExtension (hA true) (fun _ _ => contDiff_const) r (r + δ)
  have heq : endpointTaylorCorrection n l r δ A = F + G := by
    funext x
    exact congrArg₂ (· + ·) (endpointTaylorPatch_eq_extension n l hδ (A false) x)
      (endpointTaylorPatch_eq_extension n r hδ (A true) x)
  rw [heq, iteratedFDeriv_add_apply
    (hF.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
    (hG.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k F p‖ + ‖iteratedFDeriv ℝ k G p‖ := norm_add_le _ _
    _ ≤ (2 : ℝ) ^ N * B * ((n + 1 : ℕ) : ℝ) * M ^ (N + 1) +
        (2 : ℝ) ^ N * B * ((n + 1 : ℕ) : ℝ) * M ^ (N + 1) :=
      add_le_add (hpatch l false) (hpatch r true)
    _ ≤ C * M ^ (N + 1) := by
      dsimp only [C]
      nlinarith only [pow_nonneg hM0 (N + 1)]

end ContinuousFlexibility.Analysis
