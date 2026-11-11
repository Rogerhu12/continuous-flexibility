import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Neumann inverse package

For a bounded operator `R` on a real Banach space `E` with `‖R‖ < 1`, the operator `1 + R` is
invertible; we define `neumannInverse R hR` as its inverse and prove the identities, norm bound,
uniqueness, Lipschitz dependence on `R`, the perturbation statement for an invertible reference
operator (paper §8, `eq:rewrite-base-relative`, `eq:current-fixed-domain-factorization`), and the
parametric control inverse of paper §9.
-/


noncomputable section

namespace ContinuousFlexibility.Analysis

section Neumann

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The inverse of `1 + R` for `‖R‖ < 1`. -/
def neumannInverse (R : E →L[ℝ] E) (hR : ‖R‖ < 1) : E →L[ℝ] E :=
  ((Units.oneSub (-R) (by rwa [norm_neg])))⁻¹.val

theorem neumannInverse_mul (R : E →L[ℝ] E) (hR : ‖R‖ < 1) :
    neumannInverse R hR * (1 + R) = 1 := by
  have h := (Units.oneSub (-R) (by rwa [norm_neg])).inv_mul
  rw [Units.val_oneSub, sub_neg_eq_add] at h
  exact h

theorem mul_neumannInverse (R : E →L[ℝ] E) (hR : ‖R‖ < 1) :
    (1 + R) * neumannInverse R hR = 1 := by
  have h := (Units.oneSub (-R) (by rwa [norm_neg])).mul_inv
  rw [Units.val_oneSub, sub_neg_eq_add] at h
  exact h

theorem neumannInverse_apply_add (R : E →L[ℝ] E) (hR : ‖R‖ < 1) (F : E) :
    neumannInverse R hR (F + R F) = F := by
  have h := congrArg (fun T : E →L[ℝ] E => T F) (neumannInverse_mul R hR)
  simpa using h

theorem neumannInverse_add_apply (R : E →L[ℝ] E) (hR : ‖R‖ < 1) (F : E) :
    neumannInverse R hR F + R (neumannInverse R hR F) = F := by
  have h := congrArg (fun T : E →L[ℝ] E => T F) (mul_neumannInverse R hR)
  simpa using h

theorem norm_neumannInverse_le (R : E →L[ℝ] E) (hR : ‖R‖ < 1) :
    ‖neumannInverse R hR‖ ≤ 1 / (1 - ‖R‖) := by
  set N := neumannInverse R hR with hN
  have h1 : N = 1 - N * R := by
    have := neumannInverse_mul R hR
    rw [← hN, mul_add, mul_one] at this
    rw [← this]; abel
  have h2 : ‖N‖ ≤ 1 + ‖N‖ * ‖R‖ := by
    calc ‖N‖ = ‖1 - N * R‖ := by rw [← h1]
      _ ≤ ‖(1 : E →L[ℝ] E)‖ + ‖N * R‖ := norm_sub_le _ _
      _ ≤ 1 + ‖N‖ * ‖R‖ :=
        add_le_add (ContinuousLinearMap.norm_id_le) (ContinuousLinearMap.opNorm_comp_le _ _)
  have hpos : 0 < 1 - ‖R‖ := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith

theorem norm_neumannInverse_le_two (R : E →L[ℝ] E) (hR : ‖R‖ < 1) (h : ‖R‖ ≤ 1 / 2) :
    ‖neumannInverse R hR‖ ≤ 2 := by
  refine (norm_neumannInverse_le R hR).trans ?_
  have hpos : 0 < 1 - ‖R‖ := by linarith
  rw [div_le_iff₀ hpos]
  linarith

theorem neumannInverse_unique (R : E →L[ℝ] E) (hR : ‖R‖ < 1) (G : E →L[ℝ] E)
    (hG : ∀ F, G (F + R F) = F) : G = neumannInverse R hR := by
  ext F
  have h := hG (neumannInverse R hR F)
  rw [neumannInverse_add_apply] at h
  exact h

/-- Resolvent identity bound. -/
theorem norm_neumannInverse_sub_le (R R' : E →L[ℝ] E) (hR : ‖R‖ < 1) (hR' : ‖R'‖ < 1)
    (h : ‖R‖ ≤ 1 / 2) (h' : ‖R'‖ ≤ 1 / 2) :
    ‖neumannInverse R hR - neumannInverse R' hR'‖ ≤ 4 * ‖R - R'‖ := by
  set N := neumannInverse R hR with hN
  set N' := neumannInverse R' hR' with hN'
  have e : N * (R' - R) * N' = N - N' := by
    calc N * (R' - R) * N' = N * ((1 + R') * N') - (N * (1 + R)) * N' := by noncomm_ring
      _ = N - N' := by
        rw [hN', hN, mul_neumannInverse, neumannInverse_mul]; simp
  have hN2 : ‖N‖ ≤ 2 := norm_neumannInverse_le_two R hR h
  have hN2' : ‖N'‖ ≤ 2 := norm_neumannInverse_le_two R' hR' h'
  rw [← e]
  calc ‖N * (R' - R) * N'‖ ≤ ‖N * (R' - R)‖ * ‖N'‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖N‖ * ‖R' - R‖) * ‖N'‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ (2 * ‖R' - R‖) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hN2 (norm_nonneg _)) hN2' (norm_nonneg _)
          (by positivity)
    _ = 4 * ‖R - R'‖ := by rw [norm_sub_rev R' R]; ring

end Neumann

section Perturbation

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace Y] in
theorem perturbation_factorization (P₀ P : X →L[ℝ] Y) (G₀ : Y →L[ℝ] X)
    (hleft : ∀ u, G₀ (P₀ u) = u) (u : X) :
    P u = P₀ u + ((P - P₀).comp G₀) (P₀ u) := by
  simp [hleft]

theorem perturbation_rightInverse (P₀ P : X →L[ℝ] Y) (G₀ : Y →L[ℝ] X)
    (hright : ∀ F, P₀ (G₀ F) = F)
    (hrel : ‖(P - P₀).comp G₀‖ < 1 / 2) (F : Y) :
    P ((G₀.comp (neumannInverse ((P - P₀).comp G₀) (by linarith))) F) = F := by
  have h := neumannInverse_add_apply ((P - P₀).comp G₀) (by linarith) F
  simp only [ContinuousLinearMap.comp_apply]
  have h2 : P (G₀ (neumannInverse ((P - P₀).comp G₀) (by linarith) F))
      = P₀ (G₀ (neumannInverse ((P - P₀).comp G₀) (by linarith) F))
        + ((P - P₀).comp G₀) (neumannInverse ((P - P₀).comp G₀) (by linarith) F) := by
    simp [hright]
  rw [h2, hright]
  exact h

theorem perturbation_leftInverse (P₀ P : X →L[ℝ] Y) (G₀ : Y →L[ℝ] X)
    (hleft : ∀ u, G₀ (P₀ u) = u)
    (hrel : ‖(P - P₀).comp G₀‖ < 1 / 2) (u : X) :
    (G₀.comp (neumannInverse ((P - P₀).comp G₀) (by linarith))) (P u) = u := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [perturbation_factorization P₀ P G₀ hleft u, neumannInverse_apply_add, hleft]

theorem perturbation_norm_le (P₀ P : X →L[ℝ] Y) (G₀ : Y →L[ℝ] X)
    (hrel : ‖(P - P₀).comp G₀‖ < 1 / 2) :
    ‖G₀.comp (neumannInverse ((P - P₀).comp G₀) (by linarith))‖ ≤ 2 * ‖G₀‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have := norm_neumannInverse_le_two ((P - P₀).comp G₀) (by linarith) hrel.le
  nlinarith [norm_nonneg G₀]

end Perturbation

section Parametric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Z : Type*}

theorem norm_neg_smul_le_half (U : Set Z) (T : Z → E →L[ℝ] E) (K : ℝ) (hK : 0 < K)
    (hT : ∀ z ∈ U, ‖T z‖ ≤ K) (q : ℝ) (hq : |q| ≤ 1 / (2 * K)) (z : Z) (hz : z ∈ U) :
    ‖-(q • T z)‖ ≤ 1 / 2 := by
  rw [norm_neg, norm_smul, Real.norm_eq_abs]
  calc |q| * ‖T z‖ ≤ 1 / (2 * K) * K :=
        mul_le_mul hq (hT z hz) (norm_nonneg _) (by positivity)
    _ = 1 / 2 := by field_simp

variable [CompleteSpace E] in
theorem control_equation_iff (U : Set Z) (T : Z → E →L[ℝ] E) (K : ℝ) (hK : 0 < K)
    (hT : ∀ z ∈ U, ‖T z‖ ≤ K) (q : ℝ) (hq : |q| ≤ 1 / (2 * K)) (z : Z) (hz : z ∈ U)
    (a ξ : E) :
    ξ = a + q • T z ξ ↔
      ξ = neumannInverse (-(q • T z))
        (lt_of_le_of_lt (norm_neg_smul_le_half U T K hK hT q hq z hz) (by norm_num)) a := by
  set R : E →L[ℝ] E := -(q • T z) with hRdef
  have hR : ‖R‖ < 1 :=
    lt_of_le_of_lt (norm_neg_smul_le_half U T K hK hT q hq z hz) (by norm_num)
  have hRξ : ∀ ξ : E, R ξ = -(q • T z ξ) := fun ξ => by simp [hRdef]
  constructor
  · intro h
    have h1 : a = ξ + R ξ := by rw [hRξ, ← sub_eq_add_neg]; exact eq_sub_of_add_eq h.symm
    rw [h1, neumannInverse_apply_add]
  · intro h
    have h1 := neumannInverse_add_apply R hR a
    rw [← h, hRξ] at h1
    rw [← h1]; abel

end Parametric

end ContinuousFlexibility.Analysis
