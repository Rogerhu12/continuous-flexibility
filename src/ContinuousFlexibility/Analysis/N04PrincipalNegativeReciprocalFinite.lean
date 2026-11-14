import ContinuousFlexibility.Analysis.N04PrincipalNegativeScalarComposition
import ContinuousFlexibility.Analysis.AbsoluteReciprocalJetBounds
import ContinuousFlexibility.Analysis.CircleCompositionFaaBounds

/-!
# Finite reciprocal composition estimates

Only the value of the reciprocal is charged to the outer kernel. Its
genuine derivatives are bounded by the reciprocal formula, so no upper
bound on the denominator enters the scalar derivative estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PrincipalNegative_inverse_outer_derivatives (N : ℕ)
    {M y : ℝ} (hM : 1 ≤ M) (hy : y ≠ 0) (hinv : |y⁻¹| ≤ M)
    (a b : ℕ) (hab : a + b ≤ N) :
    ‖iteratedFDeriv ℝ a (iteratedDeriv b (fun t : ℝ => t⁻¹)) y‖ ≤
      (N.factorial : ℝ) * M ^ (N + 1) := by
  have hraw := norm_iteratedFDeriv_one_div_le (abs_pos.mpr hy) le_rfl (a + b)
  have hrec : (|y| ^ (a + b + 1))⁻¹ ≤ M ^ (N + 1) := by
    calc
      _ = |y⁻¹| ^ (a + b + 1) := by rw [abs_inv, inv_pow]
      _ ≤ M ^ (a + b + 1) := pow_le_pow_left₀ (abs_nonneg _) hinv _
      _ ≤ M ^ (N + 1) := pow_le_pow_right₀ hM (Nat.add_le_add_right hab 1)
  have hfact : ((a + b).factorial : ℝ) ≤ (N.factorial : ℝ) :=
    Nat.cast_le.mpr (Nat.factorial_le hab)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, circle_iteratedDeriv_iteratedDeriv]
  have hraw' : ‖iteratedDeriv (a + b) (fun t : ℝ => t⁻¹) y‖ ≤
      ((a + b).factorial : ℝ) * (|y| ^ (a + b + 1))⁻¹ := by
    simpa only [one_div, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      absoluteReciprocalJetBound] using hraw
  exact hraw'.trans (mul_le_mul hfact hrec
    (inv_nonneg.mpr (pow_nonneg (abs_nonneg _) _)) (Nat.cast_nonneg _))

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Reciprocals preserve the finite interpolation exponent. The
coefficient remains polynomial in the common scalar envelope. -/
theorem n04PrincipalNegative_finiteReciprocal_shifted_bound
    (k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, ∃ d : ℕ, 1 ≤ B ∧ 1 ≤ d ∧
      ∀ (U : Set X), IsOpen U → ∀ (Ω : Set PolarPoint), IsOpen Ω →
      ∀ f : X → PolarPoint → ℝ, ∀ F : MixedJetRegularity U Ω f,
      (∀ y ∈ U, ∀ q ∈ Ω, f y q ≠ 0) →
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun y => mixedDerivative a b (fun p => (f y p)⁻¹) q),
      ∀ x ∈ U, ∀ (P : X → Prop) (v : Fin k → X), (∀ i, P (v i)) →
      ∀ s shift : ℕ, ∀ H M R : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M → 1 ≤ R →
      |(f x q)⁻¹| ≤ M →
      (∀ j : ℕ, j ≤ k → ∀ u w : ℕ, u + w ≤ a + b →
        ∀ z : Fin j → X, (∀ i, P (z i)) →
        ‖((F.parameter u w q hq).D j x z)‖ ≤
          M * parameterHeightWeight H j *
            R ^ (((u + w + shift * j : ℕ) : ℝ) / ((s : ℝ) + 1))) →
      ‖J.D k x v‖ ≤ B * M ^ d * parameterHeightWeight H k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  obtain ⟨CB, hCB, hcomp⟩ := n04PrincipalNegative_finiteScalarComposition_shifted_bound
    (X := X) k a b RH
  let N : ℕ := k + a + b
  let C : ℝ := 1 + (N.factorial : ℝ)
  have hC : 1 ≤ C := le_add_of_nonneg_right (Nat.cast_nonneg _)
  refine ⟨CB * C ^ (N + 1), (N + 1) * (N + 1),
    one_le_mul_of_one_le_of_one_le hCB (one_le_pow₀ hC), by
      have hN : 1 ≤ N + 1 := by omega
      exact Nat.mul_le_mul hN hN, ?_⟩
  intro U hU Ω hΩ f F hnonzero q hq J x hx P v hv s shift H M R
    hH hHR hM hR hinv hsource
  let M1 : ℝ := C * M ^ (N + 1)
  have hM1 : 1 ≤ M1 := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hM)
  have hMM1 : M ≤ M1 := by
    calc
      M = M ^ 1 := (pow_one _).symm
      _ ≤ M ^ (N + 1) := pow_le_pow_right₀ hM (by omega)
      _ ≤ C * M ^ (N + 1) := le_mul_of_one_le_left
        (pow_nonneg (zero_le_one.trans hM) _) hC
  let V : Set ℝ := {t | t ≠ 0}
  have hV : IsOpen V := isOpen_ne
  have hg : ContDiffOn ℝ ∞ (fun t : ℝ => t⁻¹) V :=
    fun t ht => (contDiffAt_inv ℝ ht).contDiffWithinAt
  have houter (m : ℕ) (hm : m ≤ a + b) (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (iteratedDeriv m (fun t : ℝ => t⁻¹)) (f x q)‖ ≤ M1 := by
    have h := n04PrincipalNegative_inverse_outer_derivatives N hM
      (hnonzero x hx q hq) hinv j m (by dsimp only [N]; omega)
    exact h.trans (mul_le_mul_of_nonneg_right
      (by dsimp only [C]; linarith : (N.factorial : ℝ) ≤ C)
      (pow_nonneg (zero_le_one.trans hM) _))
  have hsource' (j : ℕ) (hj : j ≤ k) (u w : ℕ) (huw : u + w ≤ a + b)
      (z : Fin j → X) (hz : ∀ i, P (z i)) :
      ‖((F.parameter u w q hq).D j x z)‖ ≤
        M1 * parameterHeightWeight H j *
          R ^ (((u + w + shift * j : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
    (hsource j hj u w huw z hz).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMM1 (parameterHeightWeight_nonneg hH j))
      (Real.rpow_nonneg (zero_le_one.trans hR) _))
  have h := hcomp U hU Ω hΩ V hV f (fun t : ℝ => t⁻¹) F hg
    hnonzero q hq J x hx P v hv s shift H M1 R hH hHR hM1 hR houter hsource'
  calc
    _ ≤ CB * M1 ^ (N + 1) * parameterHeightWeight H k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / ((s : ℝ) + 1)) := h
    _ = _ := by
      dsimp only [M1]
      rw [mul_pow, ← pow_mul]
      ring

end ContinuousFlexibility.Analysis
