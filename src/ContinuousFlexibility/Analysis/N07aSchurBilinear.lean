import ContinuousFlexibility.Analysis.N07aRieszBilinear
import ContinuousFlexibility.Radial.WeightedSchurTest

/-!
# Constructing a bounded operator from actual Schur blocks

The real Schur test proves absolute summability of every scalar pairing.
Riesz realization then produces the operator itself; no vector series
convergence or commutator-domain conclusion is assumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem n07a_schur_bilinear_bound
    (b : ℕ × ℕ → E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (p : ℕ → E → ℝ) (q : ℕ → F → ℝ) (a : ℕ → ℕ → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : ∀ l j, 0 ≤ a l j)
    (hrow : ∀ l, Summable (fun j => a l j) ∧ ∑' j, a l j ≤ A)
    (hcol : ∀ j, Summable (fun l => a l j) ∧ ∑' l, a l j ≤ B)
    (hp₀ : ∀ j x, 0 ≤ p j x) (hq₀ : ∀ l y, 0 ≤ q l y)
    (hp : ∀ x, Summable (fun j => p j x ^ 2) ∧ ∑' j, p j x ^ 2 ≤ ‖x‖ ^ 2)
    (hq : ∀ y, Summable (fun l => q l y ^ 2) ∧ ∑' l, q l y ^ 2 ≤ ‖y‖ ^ 2)
    (hb : ∀ i x y, ‖b i x y‖ ≤ a i.1 i.2 * q i.1 y * p i.2 x) :
    (∀ x y, Summable (fun i => b i x y)) ∧
      ∀ x y, ‖∑' i, b i x y‖ ≤ Real.sqrt (A * B) * ‖x‖ * ‖y‖ := by
  have hschur (x : E) (y : F) := ContinuousFlexibility.Radial.real_schur_test
    a hA hB ha hrow hcol (fun l => q l y) (fun j => p j x)
      (fun l => hq₀ l y) (fun j => hp₀ j x) (hq y).1 (hp x).1
  refine ⟨fun x y => (hschur x y).1.of_norm_bounded (fun i => hb i x y), ?_⟩
  intro x y
  have hx : Real.sqrt (∑' j, p j x ^ 2) ≤ ‖x‖ :=
    Real.sqrt_le_iff.mpr ⟨norm_nonneg x, (hp x).2⟩
  have hy : Real.sqrt (∑' l, q l y ^ 2) ≤ ‖y‖ :=
    Real.sqrt_le_iff.mpr ⟨norm_nonneg y, (hq y).2⟩
  calc
    _ ≤ ∑' i : ℕ × ℕ, a i.1 i.2 * q i.1 y * p i.2 x :=
      tsum_of_norm_bounded (hschur x y).1.hasSum (fun i => hb i x y)
    _ ≤ Real.sqrt (A * B) * Real.sqrt (∑' l, q l y ^ 2) *
        Real.sqrt (∑' j, p j x ^ 2) := (hschur x y).2
    _ ≤ Real.sqrt (A * B) * ‖y‖ * ‖x‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _)) hx
        (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem exists_n07aSchurRiesz
    (b : ℕ × ℕ → E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (p : ℕ → E → ℝ) (q : ℕ → F → ℝ) (a : ℕ → ℕ → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : ∀ l j, 0 ≤ a l j)
    (hrow : ∀ l, Summable (fun j => a l j) ∧ ∑' j, a l j ≤ A)
    (hcol : ∀ j, Summable (fun l => a l j) ∧ ∑' l, a l j ≤ B)
    (hp₀ : ∀ j x, 0 ≤ p j x) (hq₀ : ∀ l y, 0 ≤ q l y)
    (hp : ∀ x, Summable (fun j => p j x ^ 2) ∧ ∑' j, p j x ^ 2 ≤ ‖x‖ ^ 2)
    (hq : ∀ y, Summable (fun l => q l y ^ 2) ∧ ∑' l, q l y ^ 2 ≤ ‖y‖ ^ 2)
    (hb : ∀ i x y, ‖b i x y‖ ≤ a i.1 i.2 * q i.1 y * p i.2 x) :
    ∃ K : E →L[ℝ] F, ‖K‖ ≤ Real.sqrt (A * B) ∧
      ∀ x y, ⟪K x, y⟫ = ∑' i, b i x y := by
  have h := n07a_schur_bilinear_bound b p q a hA hB ha hrow hcol hp₀ hq₀ hp hq hb
  exact ⟨n07aBilinearRiesz b h.1 _ h.2,
    n07aBilinearRiesz_norm_le b h.1 (Real.sqrt_nonneg _) h.2,
    n07aBilinearRiesz_pairing b h.1 _ h.2⟩

end ContinuousFlexibility.Analysis
