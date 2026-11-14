module

public import ContinuousFlexibility.Radial.PositiveBufferGreenAlgebra

/-!
# Norm control of the finite-rank Dirichlet subtraction

All state norms here are the actual max norm in the frozen statement. The
pairing estimate includes its factor two explicitly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Matrix
open ContinuousFlexibility.Statements
open scoped InnerProductSpace

theorem positiveBufferStatePairing_abs_le (U F : RadialL2 × ℝ) :
    |positiveBufferStatePairing U F| ≤ 2 * ‖U‖ * ‖F‖ := by
  have hU1 : ‖U.1‖ ≤ ‖U‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have hU2 : |U.2| ≤ ‖U‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact le_max_right _ _
  have hF1 : ‖F.1‖ ≤ ‖F‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have hF2 : |F.2| ≤ ‖F‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact le_max_right _ _
  calc
    |positiveBufferStatePairing U F| ≤ |inner ℝ U.1 F.1| + |U.2 * F.2| :=
      abs_add_le _ _
    _ ≤ ‖U.1‖ * ‖F.1‖ + |U.2| * |F.2| := by
      rw [abs_mul]
      exact add_le_add (abs_real_inner_le_norm _ _) le_rfl
    _ ≤ ‖U‖ * ‖F‖ + ‖U‖ * ‖F‖ :=
      add_le_add (mul_le_mul hU1 hF1 (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul hU2 hF2 (abs_nonneg _) (norm_nonneg _))
    _ = 2 * ‖U‖ * ‖F‖ := by ring

def positiveBufferStateAnalysis (g : Fin 2 → RadialL2 × ℝ) :
    (RadialL2 × ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (LinearMap.pi (fun i => positiveBufferStatePairing (g i))).mkContinuous
    (2 * ∑ i, ‖g i‖) (by
      intro F
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      change |positiveBufferStatePairing (g i) F| ≤ _
      have hi : ‖g i‖ ≤ ∑ j, ‖g j‖ :=
        Finset.single_le_sum (fun j _ => norm_nonneg (g j)) (Finset.mem_univ i)
      exact (positiveBufferStatePairing_abs_le (g i) F).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num))
          (norm_nonneg F)))

@[simp] theorem positiveBufferStateAnalysis_apply
    (g : Fin 2 → RadialL2 × ℝ) (F : RadialL2 × ℝ) (i : Fin 2) :
    positiveBufferStateAnalysis g F i = positiveBufferStatePairing (g i) F := rfl

theorem positiveBufferStateAnalysis_bound (g : Fin 2 → RadialL2 × ℝ)
    (F : RadialL2 × ℝ) :
    ‖positiveBufferStateAnalysis g F‖ ≤ 2 * (∑ i, ‖g i‖) * ‖F‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [positiveBufferStateAnalysis_apply, Real.norm_eq_abs]
  have hi : ‖g i‖ ≤ ∑ j, ‖g j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (g j)) (Finset.mem_univ i)
  exact (positiveBufferStatePairing_abs_le (g i) F).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num))
      (norm_nonneg F))

def positiveBufferStateSynthesis (g : Fin 2 → RadialL2 × ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (RadialL2 × ℝ) :=
  (positiveBufferColumnLinear g).toContinuousLinearMap

@[simp] theorem positiveBufferStateSynthesis_apply
    (g : Fin 2 → RadialL2 × ℝ) (z : Fin 2 → ℝ) :
    positiveBufferStateSynthesis g z = ∑ i, z i • g i := rfl

theorem positiveBufferStateSynthesis_bound (g : Fin 2 → RadialL2 × ℝ)
    (z : Fin 2 → ℝ) :
    ‖positiveBufferStateSynthesis g z‖ ≤ (∑ i, ‖g i‖) * ‖z‖ := by
  rw [positiveBufferStateSynthesis_apply]
  calc
    ‖∑ i, z i • g i‖ ≤ ∑ i, ‖z i • g i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖g i‖ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

def positiveBufferMatrixCLM (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  M.mulVecLin.toContinuousLinearMap

@[simp] theorem positiveBufferMatrixCLM_apply (M : Matrix (Fin 2) (Fin 2) ℝ)
    (z : Fin 2 → ℝ) : positiveBufferMatrixCLM M z = M *ᵥ z := rfl

def positiveBufferFiniteRank (g : Fin 2 → RadialL2 × ℝ)
    (J : Matrix (Fin 2) (Fin 2) ℝ) : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ) :=
  (positiveBufferStateSynthesis g).comp
    ((positiveBufferMatrixCLM J).comp (positiveBufferStateAnalysis g))

theorem positiveBufferFiniteRank_bound (g : Fin 2 → RadialL2 × ℝ)
    (J : Matrix (Fin 2) (Fin 2) ℝ)
    (hJ : ∀ z : Fin 2 → ℝ, ‖J *ᵥ z‖ ≤ 2 * ‖z‖) (F : RadialL2 × ℝ) :
    ‖positiveBufferFiniteRank g J F‖ ≤ 8 * (∑ i, ‖g i‖ ^ 2) * ‖F‖ := by
  let S : ℝ := ∑ i, ‖g i‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hsq := positiveBuffer_two_weights_sq (fun i => ‖g i‖)
  change ‖positiveBufferStateSynthesis g (J *ᵥ positiveBufferStateAnalysis g F)‖ ≤ _
  calc
    _ ≤ S * ‖J *ᵥ positiveBufferStateAnalysis g F‖ :=
      positiveBufferStateSynthesis_bound g _
    _ ≤ S * (2 * ‖positiveBufferStateAnalysis g F‖) :=
      mul_le_mul_of_nonneg_left (hJ _) hS
    _ ≤ S * (2 * (2 * S * ‖F‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (positiveBufferStateAnalysis_bound g F) (by norm_num)) hS
    _ = 4 * S ^ 2 * ‖F‖ := by ring
    _ ≤ 8 * (∑ i, ‖g i‖ ^ 2) * ‖F‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg F)
      change 4 * S ^ 2 ≤ _
      change S ^ 2 ≤ _ at hsq
      linarith

theorem positiveBufferFiniteRank_opNorm_bound (g : Fin 2 → RadialL2 × ℝ)
    (J : Matrix (Fin 2) (Fin 2) ℝ)
    (hJ : ∀ z : Fin 2 → ℝ, ‖J *ᵥ z‖ ≤ 2 * ‖z‖) :
    ‖positiveBufferFiniteRank g J‖ ≤ 8 * ∑ i, ‖g i‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact positiveBufferFiniteRank_bound g J hJ

end ContinuousFlexibility.Radial
