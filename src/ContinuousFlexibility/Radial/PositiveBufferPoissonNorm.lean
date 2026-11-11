import ContinuousFlexibility.Radial.PositiveBufferSurgeryNorm
import ContinuousFlexibility.Radial.PositiveBufferIntervalProjection

/-!
# Physical Poisson norm estimates

The endpoint weights enter through their actual square roots. The estimate
uses the max norm on the state space and the Euclidean expression stated in R09.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory Matrix
open ContinuousFlexibility.Statements
open scoped InnerProductSpace

def positiveBufferPoissonMap (B : BufferData) (g : Fin 2 → RadialL2 × ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (A : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (RadialL2 × ℝ) :=
  (positiveBufferRetainedProjection B.l B.h).comp
    ((positiveBufferStateSynthesis g).comp
      ((positiveBufferMatrixCLM Q).comp
        (positiveBufferMatrixCLM (Matrix.diagonal (fun i => sqrt (A i))))))

@[simp] theorem positiveBufferPoissonMap_apply (B : BufferData)
    (g : Fin 2 → RadialL2 × ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (A z : Fin 2 → ℝ) :
    positiveBufferPoissonMap B g Q A z =
      positiveBufferRetainedProjection B.l B.h
        (positiveBufferStateSynthesis g (Q *ᵥ (fun i => sqrt (A i) * z i))) := by
  simp only [positiveBufferPoissonMap, ContinuousLinearMap.comp_apply,
    positiveBufferMatrixCLM_apply, Matrix.diagonal_mulVec, Pi.mul_apply]

theorem positiveBufferState_euclidean_le (U : RadialL2 × ℝ) :
    sqrt (‖U.1‖ ^ 2 + U.2 ^ 2) ≤ 2 * ‖U‖ := by
  have h1 : ‖U.1‖ ≤ ‖U‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have h2 : |U.2| ≤ ‖U‖ := by rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_right _ _
  have h1sq := pow_le_pow_left₀ (norm_nonneg U.1) h1 2
  have h2sq := pow_le_pow_left₀ (abs_nonneg U.2) h2 2
  rw [sq_abs] at h2sq
  have hs : 0 ≤ ‖U.1‖ ^ 2 + U.2 ^ 2 := by positivity
  have hroot := Real.sq_sqrt hs
  have hroot0 := Real.sqrt_nonneg (‖U.1‖ ^ 2 + U.2 ^ 2)
  nlinarith [norm_nonneg U, sq_nonneg ‖U‖]

theorem positiveBuffer_weighted_sup_le (A z : Fin 2 → ℝ) (hA : ∀ i, 0 ≤ A i) :
    ‖fun i => sqrt (A i) * z i‖ ≤ sqrt (∑ i, A i * z i ^ 2) := by
  have hs : 0 ≤ ∑ i, A i * z i ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hA i) (sq_nonneg _))
  apply (pi_norm_le_iff_of_nonneg (sqrt_nonneg _)).mpr
  intro i
  have hi : A i * z i ^ 2 ≤ ∑ j, A j * z j ^ 2 :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hA j) (sq_nonneg _)) (Finset.mem_univ i)
  have heq : |sqrt (A i) * z i| ^ 2 = A i * z i ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt (hA i)]
  rw [Real.norm_eq_abs]
  nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ j, A j * z j ^ 2),
    abs_nonneg (sqrt (A i) * z i)]

theorem positiveBuffer_norm_sum_le_sqrt (g : Fin 2 → RadialL2 × ℝ) :
    (∑ i, ‖g i‖) ≤ 2 * sqrt (∑ i, ‖g i‖ ^ 2) := by
  have hsq := positiveBuffer_two_weights_sq (fun i => ‖g i‖)
  have hs : 0 ≤ ∑ i, ‖g i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hn : 0 ≤ ∑ i, ‖g i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ i, ‖g i‖ ^ 2)]

theorem positiveBufferPoissonMap_euclidean_bound (B : BufferData)
    (g : Fin 2 → RadialL2 × ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : ∀ z : Fin 2 → ℝ, ‖Q *ᵥ z‖ ≤ 2 * ‖z‖)
    (A : Fin 2 → ℝ) (hA : ∀ i, 0 ≤ A i) (z : Fin 2 → ℝ) :
    sqrt (‖(positiveBufferPoissonMap B g Q A z).1‖ ^ 2 +
      (positiveBufferPoissonMap B g Q A z).2 ^ 2) ≤
      8 * sqrt (∑ i, ‖g i‖ ^ 2) * sqrt (∑ i, A i * z i ^ 2) := by
  have hs : 0 ≤ ∑ i, ‖g i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hn : ‖positiveBufferPoissonMap B g Q A z‖ ≤
      (∑ i, ‖g i‖) * (2 * sqrt (∑ i, A i * z i ^ 2)) := by
    rw [positiveBufferPoissonMap_apply]
    calc
      _ ≤ ‖positiveBufferStateSynthesis g (Q *ᵥ (fun i => sqrt (A i) * z i))‖ :=
        positiveBufferRetainedProjection_norm_le _ _ _
      _ ≤ (∑ i, ‖g i‖) * ‖Q *ᵥ (fun i => sqrt (A i) * z i)‖ :=
        positiveBufferStateSynthesis_bound g _
      _ ≤ (∑ i, ‖g i‖) * (2 * ‖fun i => sqrt (A i) * z i‖) :=
        mul_le_mul_of_nonneg_left (hQ _) hs
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (positiveBuffer_weighted_sup_le A z hA) (by norm_num)) hs
  calc
    _ ≤ 2 * ‖positiveBufferPoissonMap B g Q A z‖ := positiveBufferState_euclidean_le _
    _ ≤ 2 * ((∑ i, ‖g i‖) * (2 * sqrt (∑ i, A i * z i ^ 2))) :=
      mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = 4 * (∑ i, ‖g i‖) * sqrt (∑ i, A i * z i ^ 2) := by ring
    _ ≤ 4 * (2 * sqrt (∑ i, ‖g i‖ ^ 2)) * sqrt (∑ i, A i * z i ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (positiveBuffer_norm_sum_le_sqrt g) (by norm_num))
        (sqrt_nonneg _)
    _ = _ := by ring

theorem positiveBuffer_columns_square_norm (g : Fin 2 → RadialL2 × ℝ)
    (m : Fin 2 → ℝ) (hm : ∀ i, 0 < m i) {K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ i, ‖g i‖ ≤ K / m i) :
    (∑ i, ‖g i‖ ^ 2) ≤ K ^ 2 * ∑ i, (m i)⁻¹ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    ‖g i‖ ^ 2 ≤ (K / m i) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hg i) 2
    _ = K ^ 2 * (m i)⁻¹ ^ 2 := by rw [div_eq_mul_inv, mul_pow]

theorem positiveBuffer_columns_sqrt_norm (g : Fin 2 → RadialL2 × ℝ)
    (m : Fin 2 → ℝ) (hm : ∀ i, 0 < m i) {K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ i, ‖g i‖ ≤ K / m i) :
    sqrt (∑ i, ‖g i‖ ^ 2) ≤ K * sqrt (∑ i, (m i)⁻¹ ^ 2) := by
  have h := Real.sqrt_le_sqrt (positiveBuffer_columns_square_norm g m hm hK hg)
  simpa only [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq_eq_abs, abs_of_nonneg hK] using h

theorem positiveBufferPoissonMap_mass_bound (B : BufferData)
    (g : Fin 2 → RadialL2 × ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : ∀ z : Fin 2 → ℝ, ‖Q *ᵥ z‖ ≤ 2 * ‖z‖)
    (A : Fin 2 → ℝ) (hA : ∀ i, 0 ≤ A i)
    (hm : ∀ i, 0 < B.mass i) {K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ i, ‖g i‖ ≤ K / B.mass i) (z : Fin 2 → ℝ) :
    sqrt (‖(positiveBufferPoissonMap B g Q A z).1‖ ^ 2 +
      (positiveBufferPoissonMap B g Q A z).2 ^ 2) ≤
      (8 * K) * sqrt (∑ i, (B.mass i)⁻¹ ^ 2) * sqrt (∑ i, A i * z i ^ 2) := by
  calc
    _ ≤ 8 * sqrt (∑ i, ‖g i‖ ^ 2) * sqrt (∑ i, A i * z i ^ 2) :=
      positiveBufferPoissonMap_euclidean_bound B g Q hQ A hA z
    _ ≤ 8 * (K * sqrt (∑ i, (B.mass i)⁻¹ ^ 2)) * sqrt (∑ i, A i * z i ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (positiveBuffer_columns_sqrt_norm g B.mass hm hK hg)
          (by norm_num)) (sqrt_nonneg _)
    _ = _ := by ring

theorem positiveBuffer_single_expansion (z : Fin 2 → ℝ) :
    (∑ i, z i • Pi.single i (1 : ℝ)) = z := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp

theorem positiveBufferPoissonMap_columns (B : BufferData)
    (g : Fin 2 → RadialL2 × ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin 2 → ℝ) (P : Fin 2 → RadialL2) (scalar : Fin 2 → ℝ)
    (hcol : ∀ i, (P i, scalar i) = positiveBufferPoissonMap B g Q A (Pi.single i 1))
    (z : Fin 2 → ℝ) :
    (∑ i, z i • P i, ∑ i, z i * scalar i) = positiveBufferPoissonMap B g Q A z := by
  have hp : (∑ i, z i • (P i, scalar i)) =
      (∑ i, z i • P i, ∑ i, z i * scalar i) := by
    apply Prod.ext
    · simp only [Fin.sum_univ_two, Prod.fst_add, Prod.smul_fst]
    · simp only [Fin.sum_univ_two, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  rw [← hp]
  simp_rw [hcol]
  calc
    _ = positiveBufferPoissonMap B g Q A (∑ i, z i • Pi.single i 1) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (map_smul (positiveBufferPoissonMap B g Q A) (z i) (Pi.single i 1)).symm
    _ = _ := by rw [positiveBuffer_single_expansion]

end ContinuousFlexibility.Radial
