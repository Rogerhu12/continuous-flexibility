import ContinuousFlexibility.Radial.PositiveBufferMatrixPositivity
import ContinuousFlexibility.Radial.PositiveBufferPoissonNorm

/-!
# Uniform constants and physical conormal estimates

All smallness conditions are consequences of the single frozen attenuation
hypothesis. The diagonal comparison uses the genuine profile conormals.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Matrix Finset

def positiveBufferColumnConstant (P F : ℝ) : ℝ := 2 * P * (1 + F)
def positiveBufferErrorConstant (P F : ℝ) : ℝ := 2 * P * F

theorem positiveBuffer_choose_constants {P F : ℝ} (hP : 1 ≤ P) (hF : 1 ≤ F) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ε ≤ 1 ∧ P ≤ C ∧
      8 * positiveBufferColumnConstant P F ≤ C ∧
      8 * positiveBufferColumnConstant P F ^ 2 ≤ C ∧
      2 * positiveBufferErrorConstant P F ≤ C ∧
      2 * positiveBufferErrorConstant P F * ε ≤ 1 / 4 ∧
      4 * positiveBufferErrorConstant P F * ε ≤ (1 / (2 * P)) / 2 := by
  let K := positiveBufferColumnConstant P F
  let D := positiveBufferErrorConstant P F
  have hP0 : 0 < P := by linarith
  have hF0 : 0 < F := by linarith
  have hD : 0 < D := by dsimp [D, positiveBufferErrorConstant]; positivity
  have hK : 1 ≤ K := by
    dsimp [K, positiveBufferColumnConstant]
    nlinarith [mul_nonneg hP0.le hF0.le]
  have hPK : P ≤ K := by
    dsimp [K, positiveBufferColumnConstant]
    nlinarith [mul_nonneg hP0.le hF0.le]
  have hDK : D ≤ K := by
    dsimp [D, K, positiveBufferColumnConstant, positiveBufferErrorConstant]
    nlinarith
  have hKsq : K ≤ K ^ 2 := by
    simpa only [one_mul, pow_two] using
      mul_le_mul_of_nonneg_right hK (show 0 ≤ K by linarith)
  let ε := min 1 (1 / (32 * P * D))
  have hden : 0 < 32 * P * D := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos (by norm_num) hden)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεd : ε * (32 * P * D) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right 1 (1 / (32 * P * D)))
  have hDe : 0 ≤ D * ε := mul_nonneg hD.le hε.le
  have hscale : D * ε ≤ P * (D * ε) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hP hDe
  have hsmall : 2 * D * ε ≤ 1 / 4 := by nlinarith
  have hquad : 4 * D * ε ≤ (1 / (2 * P)) / 2 := by
    have hh : 4 * D * ε ≤ 1 / (4 * P) := by
      apply (le_div_iff₀ (show 0 < 4 * P by positivity)).mpr
      nlinarith
    convert hh using 1 <;> field_simp <;> ring
  refine ⟨8 * K ^ 2, ε, by positivity, hε, hε1, ?_, ?_, le_rfl, ?_, hsmall, hquad⟩
  · nlinarith
  · nlinarith
  · nlinarith

theorem positiveBuffer_attenuated_weights_sum {B₀ D ε : ℝ}
    (hB₀ : 0 ≤ B₀) (hD : 0 ≤ D) (m σ : Fin 2 → ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hsmall : ∀ i, B₀ * m i ^ 2 * exp (-σ i) ≤ ε) :
    (D * B₀) * (∑ i, (m i * exp (-σ i)) ^ 2) ≤ 2 * D * ε := by
  have hi (i : Fin 2) : B₀ * (m i * exp (-σ i)) ^ 2 ≤ ε := by
    have he : exp (-σ i) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr (hσ i))
    calc
      B₀ * (m i * exp (-σ i)) ^ 2 =
          (B₀ * m i ^ 2 * exp (-σ i)) * exp (-σ i) := by ring
      _ ≤ (B₀ * m i ^ 2 * exp (-σ i)) * 1 :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ ε := by simpa only [mul_one] using hsmall i
  have hsum : B₀ * (∑ i, (m i * exp (-σ i)) ^ 2) ≤ 2 * ε := by
    simp only [Fin.sum_univ_two]
    linarith [hi 0, hi 1]
  calc
    _ = D * (B₀ * ∑ i, (m i * exp (-σ i)) ^ 2) := by ring
    _ ≤ D * (2 * ε) := mul_le_mul_of_nonneg_left hsum hD
    _ = _ := by ring

theorem positiveBuffer_conormal_ratio_lower {P m a b : ℝ}
    (hP : 0 < P) (hm : 0 < m)
    (ha : m ≤ a) (hb : m ≤ b) (haP : a ≤ P * m) (hbP : b ≤ P * m) :
    1 / (2 * P) ≤ a / (a + b) := by
  have hsum : 0 < a + b := by linarith
  apply (div_le_div_iff₀ (show 0 < 2 * P by positivity) hsum).mpr
  have hmul := mul_le_mul_of_nonneg_left ha (show 0 ≤ 2 * P by positivity)
  nlinarith

def positiveBufferPhysicalConormal (A αout : Fin 2 → ℝ)
    (J : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => sqrt (A i) * J i j * sqrt (A j) - if i = j then αout i else 0

theorem positiveBufferPhysicalConormal_normalized_error
    (A αin αout : Fin 2 → ℝ) (hA : ∀ i, 0 < A i)
    (hAsum : ∀ i, A i = αin i + αout i)
    (J : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    (positiveBufferPhysicalConormal A αout J i j - (if i = j then αin i else 0)) /
        sqrt (A i * A j) = (J - 1) i j := by
  have hi : sqrt (A i) ≠ 0 := (Real.sqrt_pos.mpr (hA i)).ne'
  have hj : sqrt (A j) ≠ 0 := (Real.sqrt_pos.mpr (hA j)).ne'
  rw [Real.sqrt_mul (hA i).le]
  by_cases hij : i = j
  · subst j
    simp only [positiveBufferPhysicalConormal, Matrix.sub_apply, Matrix.one_apply, if_pos rfl, ite_true]
    have hs := Real.sq_sqrt (hA i).le
    field_simp [hi]
    nlinarith [hAsum i]
  · simp only [positiveBufferPhysicalConormal, Matrix.sub_apply, Matrix.one_apply, if_neg hij,
      sub_zero]
    field_simp [hi, hj] <;> ring

theorem positiveBufferPhysicalConormal_positive
    (A αin αout m w : Fin 2 → ℝ) (hA : ∀ i, 0 < A i)
    (hAsum : ∀ i, A i = αin i + αout i)
    {P η : ℝ} (hP : 0 < P) (hη : 0 ≤ η) (hm : ∀ i, 0 < m i)
    (hain : ∀ i, m i ≤ αin i) (haout : ∀ i, m i ≤ αout i)
    (hPin : ∀ i, αin i ≤ P * m i) (hPout : ∀ i, αout i ≤ P * m i)
    (hw : ∀ i, 0 ≤ w i) (J : Matrix (Fin 2) (Fin 2) ℝ)
    (hJ : ∀ i j, |(J - 1) i j| ≤ η * w i * w j)
    (hsmall : η * (∑ i, w i ^ 2) ≤ (1 / (2 * P)) / 2)
    (z : Fin 2 → ℝ) (hz : z ≠ 0) :
    0 < ∑ i, ∑ j, z i * positiveBufferPhysicalConormal A αout J i j * z j := by
  let d : Fin 2 → ℝ := fun i => αin i / A i
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal d + (J - 1)
  have hd (i : Fin 2) : 1 / (2 * P) ≤ d i := by
    dsimp only [d]
    rw [hAsum i]
    exact positiveBuffer_conormal_ratio_lower hP (hm i) (hain i) (haout i) (hPin i) (hPout i)
  have hM : ∀ y : Fin 2 → ℝ, y ≠ 0 → 0 < ∑ i, ∑ j, y i * M i j * y j :=
    positiveBufferMatrix_positive_perturbation (J - 1) w d hη
      (div_pos (by norm_num) (by positivity)) hw hd hJ hsmall
  have hentry (i j : Fin 2) :
      sqrt (A i) * M i j * sqrt (A j) = positiveBufferPhysicalConormal A αout J i j := by
    by_cases hij : i = j
    · subst j
      have hratio : sqrt (A i) * (αin i / A i - 1) * sqrt (A i) = -αout i := by
        calc
          _ = (αin i / A i - 1) * sqrt (A i) ^ 2 := by ring
          _ = (αin i / A i - 1) * A i := by rw [Real.sq_sqrt (hA i).le]
          _ = -αout i := by
            field_simp [(hA i).ne']
            nlinarith [hAsum i]
      simp only [M, d, Matrix.add_apply, Matrix.diagonal_apply, Matrix.sub_apply,
        Matrix.one_apply, if_pos rfl, ite_true, positiveBufferPhysicalConormal]
      calc
        _ = sqrt (A i) * J i i * sqrt (A i) +
            sqrt (A i) * (αin i / A i - 1) * sqrt (A i) := by ring
        _ = _ := by rw [hratio]; ring
    · simp only [M, Matrix.add_apply, Matrix.diagonal_apply, Matrix.sub_apply,
        Matrix.one_apply, if_neg hij, positiveBufferPhysicalConormal, zero_add, sub_zero]
  have h := positiveBufferMatrix_rescale_positive M (fun i => sqrt (A i))
    (fun i => (Real.sqrt_pos.mpr (hA i)).ne') hM z hz
  simpa only [hentry] using h

theorem positiveBuffer_attenuated_entry_bound {C D B₀ : ℝ}
    (hCD : 2 * D ≤ C) (hB₀ : 0 ≤ B₀)
    (m σ : Fin 2 → ℝ) (hm : ∀ i, 0 ≤ m i)
    {x : ℝ} (i j : Fin 2)
    (hx : |x| ≤ 2 * (D * B₀) * (m i * exp (-σ i)) * (m j * exp (-σ j))) :
    |x| ≤ C * B₀ * m i * m j * exp (-σ i - σ j) := by
  have hmi := hm i
  have hmj := hm j
  have he : exp (-σ i - σ j) = exp (-σ i) * exp (-σ j) := by
    rw [sub_eq_add_neg, Real.exp_add]
  calc
    |x| ≤ 2 * (D * B₀) * (m i * exp (-σ i)) * (m j * exp (-σ j)) := hx
    _ = (2 * D) * (B₀ * m i * m j * exp (-σ i - σ j)) := by rw [he]; ring
    _ ≤ C * (B₀ * m i * m j * exp (-σ i - σ j)) :=
      mul_le_mul_of_nonneg_right hCD (by positivity)
    _ = _ := by ring

end ContinuousFlexibility.Radial
