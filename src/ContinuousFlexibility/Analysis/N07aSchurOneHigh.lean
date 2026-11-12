import ContinuousFlexibility.Analysis.N07aSchurBilinear

/-!
# Schur realization retaining the two input norms

The high-order source and its fixed lower-order truncation have separate
Schur majorants.  The resulting operator retains their sum pointwise;
the higher parameter coefficient never multiplies the high input norm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped RealInnerProductSpace

private theorem n07a_schur_majorant
    (p q : ℕ → ℝ) (a : ℕ → ℕ → ℝ) {A B X Y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (ha : ∀ l j, 0 ≤ a l j)
    (hrow : ∀ l, Summable (fun j => a l j) ∧ ∑' j, a l j ≤ A)
    (hcol : ∀ j, Summable (fun l => a l j) ∧ ∑' l, a l j ≤ B)
    (hp₀ : ∀ j, 0 ≤ p j) (hq₀ : ∀ l, 0 ≤ q l)
    (hp : Summable (fun j => p j ^ 2) ∧ ∑' j, p j ^ 2 ≤ X ^ 2)
    (hq : Summable (fun l => q l ^ 2) ∧ ∑' l, q l ^ 2 ≤ Y ^ 2) :
    Summable (fun i : ℕ × ℕ => a i.1 i.2 * q i.1 * p i.2) ∧
      ∑' i : ℕ × ℕ, a i.1 i.2 * q i.1 * p i.2 ≤ Real.sqrt (A * B) * X * Y := by
  have h := ContinuousFlexibility.Radial.real_schur_test
    a hA hB ha hrow hcol q p hq₀ hp₀ hq.1 hp.1
  refine ⟨h.1, h.2.trans ?_⟩
  have hx : Real.sqrt (∑' j, p j ^ 2) ≤ X := Real.sqrt_le_iff.mpr ⟨hX, hp.2⟩
  have hy : Real.sqrt (∑' l, q l ^ 2) ≤ Y := Real.sqrt_le_iff.mpr ⟨hY, hq.2⟩
  calc
    _ ≤ Real.sqrt (A * B) * Y * X :=
      mul_le_mul (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _)) hx
        (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hY)
    _ = _ := by ring

variable {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem exists_n07aSchurRiesz_oneHigh
    (b : ℕ × ℕ → E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (I : E →L[ℝ] G)
    (p₀ p₁ : ℕ → E → ℝ) (q : ℕ → F → ℝ)
    (a₀ a₁ : ℕ → ℕ → ℝ) {A₀ B₀ A₁ B₁ : ℝ}
    (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀) (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (ha₀ : ∀ l j, 0 ≤ a₀ l j) (ha₁ : ∀ l j, 0 ≤ a₁ l j)
    (hrow₀ : ∀ l, Summable (fun j => a₀ l j) ∧ ∑' j, a₀ l j ≤ A₀)
    (hcol₀ : ∀ j, Summable (fun l => a₀ l j) ∧ ∑' l, a₀ l j ≤ B₀)
    (hrow₁ : ∀ l, Summable (fun j => a₁ l j) ∧ ∑' j, a₁ l j ≤ A₁)
    (hcol₁ : ∀ j, Summable (fun l => a₁ l j) ∧ ∑' l, a₁ l j ≤ B₁)
    (hp₀ : ∀ j x, 0 ≤ p₀ j x) (hp₁ : ∀ j x, 0 ≤ p₁ j x)
    (hq₀ : ∀ l y, 0 ≤ q l y)
    (hs₀ : ∀ x, Summable (fun j => p₀ j x ^ 2) ∧ ∑' j, p₀ j x ^ 2 ≤ ‖x‖ ^ 2)
    (hs₁ : ∀ x, Summable (fun j => p₁ j x ^ 2) ∧ ∑' j, p₁ j x ^ 2 ≤ ‖I x‖ ^ 2)
    (hsq : ∀ y, Summable (fun l => q l y ^ 2) ∧ ∑' l, q l y ^ 2 ≤ ‖y‖ ^ 2)
    (hb : ∀ i x y, ‖b i x y‖ ≤
      a₀ i.1 i.2 * q i.1 y * p₀ i.2 x + a₁ i.1 i.2 * q i.1 y * p₁ i.2 x) :
    ∃ K : E →L[ℝ] F,
      ‖K‖ ≤ Real.sqrt (A₀ * B₀) + Real.sqrt (A₁ * B₁) * ‖I‖ ∧
      (∀ x, ‖K x‖ ≤ Real.sqrt (A₀ * B₀) * ‖x‖ + Real.sqrt (A₁ * B₁) * ‖I x‖) ∧
      ∀ x y, ⟪K x, y⟫ = ∑' i, b i x y := by
  have h₀ (x : E) (y : F) := n07a_schur_majorant
    (fun j => p₀ j x) (fun l => q l y) a₀ hA₀ hB₀ (norm_nonneg x) (norm_nonneg y)
      ha₀ hrow₀ hcol₀ (fun j => hp₀ j x) (fun l => hq₀ l y) (hs₀ x) (hsq y)
  have h₁ (x : E) (y : F) := n07a_schur_majorant
    (fun j => p₁ j x) (fun l => q l y) a₁ hA₁ hB₁ (norm_nonneg (I x)) (norm_nonneg y)
      ha₁ hrow₁ hcol₁ (fun j => hp₁ j x) (fun l => hq₀ l y) (hs₁ x) (hsq y)
  have hsum (x : E) (y : F) : Summable (fun i => b i x y) :=
    ((h₀ x y).1.add (h₁ x y).1).of_norm_bounded (fun i => hb i x y)
  have hsharp (x : E) (y : F) : ‖∑' i, b i x y‖ ≤
      (Real.sqrt (A₀ * B₀) * ‖x‖ + Real.sqrt (A₁ * B₁) * ‖I x‖) * ‖y‖ := by
    calc
      _ ≤ ∑' i : ℕ × ℕ,
          (a₀ i.1 i.2 * q i.1 y * p₀ i.2 x + a₁ i.1 i.2 * q i.1 y * p₁ i.2 x) :=
        tsum_of_norm_bounded ((h₀ x y).1.add (h₁ x y).1).hasSum (fun i => hb i x y)
      _ = (∑' i : ℕ × ℕ, a₀ i.1 i.2 * q i.1 y * p₀ i.2 x) +
          ∑' i : ℕ × ℕ, a₁ i.1 i.2 * q i.1 y * p₁ i.2 x :=
        (h₀ x y).1.tsum_add (h₁ x y).1
      _ ≤ Real.sqrt (A₀ * B₀) * ‖x‖ * ‖y‖ +
          Real.sqrt (A₁ * B₁) * ‖I x‖ * ‖y‖ := add_le_add (h₀ x y).2 (h₁ x y).2
      _ = _ := by ring
  let C := Real.sqrt (A₀ * B₀) + Real.sqrt (A₁ * B₁) * ‖I‖
  have hC₀ : 0 ≤ C := by dsimp only [C]; positivity
  have hC (x : E) (y : F) : ‖∑' i, b i x y‖ ≤ C * ‖x‖ * ‖y‖ := by
    apply (hsharp x y).trans
    have hi := mul_le_mul_of_nonneg_left (I.le_opNorm x) (Real.sqrt_nonneg (A₁ * B₁))
    calc
      _ ≤ (Real.sqrt (A₀ * B₀) * ‖x‖ + Real.sqrt (A₁ * B₁) * (‖I‖ * ‖x‖)) * ‖y‖ :=
        mul_le_mul_of_nonneg_right (add_le_add le_rfl hi) (norm_nonneg y)
      _ = _ := by dsimp only [C]; ring
  let K := n07aBilinearRiesz b hsum C hC
  have hpair (x : E) (y : F) : ⟪K x, y⟫ = ∑' i, b i x y :=
    n07aBilinearRiesz_pairing b hsum C hC x y
  refine ⟨K, n07aBilinearRiesz_norm_le b hsum hC₀ hC, ?_, hpair⟩
  intro x
  have h := hsharp x (K x)
  rw [← hpair, real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
  by_cases hz : ‖K x‖ = 0
  · rw [hz]
    positivity
  · have hk : 0 < ‖K x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    rw [pow_two] at h
    exact le_of_mul_le_mul_right h hk

end ContinuousFlexibility.Analysis
