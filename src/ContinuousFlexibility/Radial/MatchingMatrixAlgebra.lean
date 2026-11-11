import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Matching matrix algebra

Finite-dimensional algebra for the matching problem of paper §6
(`06-global-reference-inverse.tex`, eqs. `eq:rad-eq-tm8`, `eq:rad-eq-tm9`, `eq:rad-eq-tm11`):
with `A = diag a`, `B = diag b`, `A² + B² = 1` and symmetric `D`, put
`K = A D - B` and `K₁ = A + B D`.  We prove `K A = A Kᵀ`, `Kᵀ K₁ = K₁ᵀ K`,
`K₁ A - B Kᵀ = 1`, the consequences for `K⁻¹`, the solution of the matching system,
invertibility of `K` from a lower bound on the diagonal part, and the scalar identity
of `eq:rad-eq-tm9`.
-/

open Matrix

namespace ContinuousFlexibility.Radial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matching matrix `K = A D - B`. -/
def matchingK (a b : n → ℝ) (D : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.diagonal a * D - Matrix.diagonal b

/-- The companion matrix `K₁ = A + B D`. -/
def matchingK₁ (a b : n → ℝ) (D : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.diagonal a + Matrix.diagonal b * D

private lemma diag_comm (a b : n → ℝ) :
    Matrix.diagonal b * Matrix.diagonal a = Matrix.diagonal a * Matrix.diagonal b := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

private lemma diag_sq (a b : n → ℝ) (hab : ∀ i, a i ^ 2 + b i ^ 2 = 1) :
    Matrix.diagonal a * Matrix.diagonal a + Matrix.diagonal b * Matrix.diagonal b = 1 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have h1 : Matrix.diagonal (fun i => a i * a i) + Matrix.diagonal (fun i => b i * b i) =
      Matrix.diagonal (fun i => a i * a i + b i * b i) :=
    Matrix.diagonal_add (fun i => a i * a i) (fun i => b i * b i)
  have hf : (fun i => a i * a i + b i * b i) = fun _ => (1 : ℝ) := by
    funext i
    have := hab i
    nlinarith
  rw [h1, hf]
  exact Matrix.diagonal_one

private lemma ring_id2 {R : Type*} [Ring R] (A B D : R) (hAB : B * A = A * B)
    (hsq : A * A + B * B = 1) : (D * A - B) * (A + B * D) = (A + D * B) * (A * D - B) := by
  have e : A * A = 1 - B * B := eq_sub_of_add_eq hsq
  have L : (D * A - B) * (A + B * D) = D * (A * A) + D * (A * B) * D - B * A - B * B * D := by
    noncomm_ring
  have R : (A + D * B) * (A * D - B) = (A * A) * D - A * B + D * (B * A) * D - D * B * B := by
    noncomm_ring
  rw [L, R, e, hAB]
  noncomm_ring

/-- `K A = A Kᵀ`. -/
theorem matchingK_mul_diag (a b : n → ℝ) (D : Matrix n n ℝ)
    (hD : D.transpose = D) :
    matchingK a b D * Matrix.diagonal a = Matrix.diagonal a * (matchingK a b D).transpose := by
  simp only [matchingK, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.diagonal_transpose,
    hD]
  rw [sub_mul, mul_sub, Matrix.mul_assoc (Matrix.diagonal a) D (Matrix.diagonal a),
    diag_comm a b]

/-- `Kᵀ K₁ = K₁ᵀ K`. -/
theorem matchingK_transpose_mul_K₁ (a b : n → ℝ) (hab : ∀ i, a i ^ 2 + b i ^ 2 = 1)
    (D : Matrix n n ℝ) (hD : D.transpose = D) :
    (matchingK a b D).transpose * matchingK₁ a b D =
      (matchingK₁ a b D).transpose * matchingK a b D := by
  simp only [matchingK, matchingK₁, Matrix.transpose_sub, Matrix.transpose_add,
    Matrix.transpose_mul, Matrix.diagonal_transpose, hD]
  exact ring_id2 (Matrix.diagonal a) (Matrix.diagonal b) D (diag_comm a b) (diag_sq a b hab)

/-- `K₁ A - B Kᵀ = 1`. -/
theorem matchingK₁_mul_diag_sub (a b : n → ℝ) (hab : ∀ i, a i ^ 2 + b i ^ 2 = 1)
    (D : Matrix n n ℝ) (hD : D.transpose = D) :
    matchingK₁ a b D * Matrix.diagonal a -
        Matrix.diagonal b * (matchingK a b D).transpose = 1 := by
  simp only [matchingK, matchingK₁, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.diagonal_transpose, hD]
  have h : (Matrix.diagonal a + Matrix.diagonal b * D) * Matrix.diagonal a -
      Matrix.diagonal b * (D * Matrix.diagonal a - Matrix.diagonal b) =
      Matrix.diagonal a * Matrix.diagonal a + Matrix.diagonal b * Matrix.diagonal b := by
    noncomm_ring
  rw [h]
  exact diag_sq a b hab

section Inverse

variable (a b : n → ℝ) (hab : ∀ i, a i ^ 2 + b i ^ 2 = 1) (D : Matrix n n ℝ)
  (hD : D.transpose = D)

private lemma inv_T_left (K : Matrix n n ℝ) (hK : IsUnit K.det) :
    K.transpose * (K⁻¹).transpose = 1 := by
  rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul K hK, Matrix.transpose_one]

private lemma inv_T_right (K : Matrix n n ℝ) (hK : IsUnit K.det) :
    (K⁻¹).transpose * K.transpose = 1 := by
  rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv K hK, Matrix.transpose_one]

include hD in
/-- `K⁻¹ A = A K⁻ᵀ`. -/
private lemma inv_mul_diag (hK : IsUnit (matchingK a b D).det) :
    (matchingK a b D)⁻¹ * Matrix.diagonal a =
      Matrix.diagonal a * ((matchingK a b D)⁻¹).transpose := by
  have h1 := matchingK_mul_diag a b D hD
  calc (matchingK a b D)⁻¹ * Matrix.diagonal a
      = (matchingK a b D)⁻¹ * Matrix.diagonal a *
          ((matchingK a b D).transpose * ((matchingK a b D)⁻¹).transpose) := by
        rw [inv_T_left _ hK, mul_one]
    _ = (matchingK a b D)⁻¹ * (Matrix.diagonal a * (matchingK a b D).transpose) *
          ((matchingK a b D)⁻¹).transpose := by simp only [Matrix.mul_assoc]
    _ = (matchingK a b D)⁻¹ * (matchingK a b D * Matrix.diagonal a) *
          ((matchingK a b D)⁻¹).transpose := by rw [← h1]
    _ = Matrix.diagonal a * ((matchingK a b D)⁻¹).transpose := by
        rw [← Matrix.mul_assoc (matchingK a b D)⁻¹ (matchingK a b D) (Matrix.diagonal a),
          Matrix.nonsing_inv_mul _ hK, one_mul]

include hab hD in
/-- `K₁ K⁻¹ A - B = K⁻ᵀ`. -/
theorem matchingK₁_mul_inv_mul_diag_sub (hK : IsUnit (matchingK a b D).det) :
    matchingK₁ a b D * (matchingK a b D)⁻¹ * Matrix.diagonal a - Matrix.diagonal b =
      ((matchingK a b D)⁻¹).transpose := by
  have h3 := matchingK₁_mul_diag_sub a b hab D hD
  have h3' : matchingK₁ a b D * Matrix.diagonal a =
      1 + Matrix.diagonal b * (matchingK a b D).transpose := by
    rw [← h3]; abel
  calc matchingK₁ a b D * (matchingK a b D)⁻¹ * Matrix.diagonal a - Matrix.diagonal b
      = matchingK₁ a b D * ((matchingK a b D)⁻¹ * Matrix.diagonal a) - Matrix.diagonal b := by
        rw [Matrix.mul_assoc]
    _ = matchingK₁ a b D * (Matrix.diagonal a * ((matchingK a b D)⁻¹).transpose) -
          Matrix.diagonal b := by rw [inv_mul_diag a b D hD hK]
    _ = (matchingK₁ a b D * Matrix.diagonal a) * ((matchingK a b D)⁻¹).transpose -
          Matrix.diagonal b := by rw [Matrix.mul_assoc]
    _ = (1 + Matrix.diagonal b * (matchingK a b D).transpose) *
          ((matchingK a b D)⁻¹).transpose - Matrix.diagonal b := by rw [h3']
    _ = ((matchingK a b D)⁻¹).transpose +
          Matrix.diagonal b * ((matchingK a b D).transpose * ((matchingK a b D)⁻¹).transpose) -
          Matrix.diagonal b := by rw [add_mul, one_mul, Matrix.mul_assoc]
    _ = ((matchingK a b D)⁻¹).transpose := by
        rw [inv_T_left _ hK, mul_one]; abel

include hD in
/-- `(K⁻¹ A)ᵀ = K⁻¹ A`. -/
theorem matchingK_inv_mul_diag_transpose (hK : IsUnit (matchingK a b D).det) :
    ((matchingK a b D)⁻¹ * Matrix.diagonal a).transpose =
      (matchingK a b D)⁻¹ * Matrix.diagonal a := by
  have h := inv_mul_diag a b D hD hK
  conv_lhs => rw [h]
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]

include hab hD in
/-- `(K₁ K⁻¹)ᵀ = K₁ K⁻¹`. -/
theorem matchingK₁_mul_inv_transpose (hK : IsUnit (matchingK a b D).det) :
    (matchingK₁ a b D * (matchingK a b D)⁻¹).transpose =
      matchingK₁ a b D * (matchingK a b D)⁻¹ := by
  have h2 := matchingK_transpose_mul_K₁ a b hab D hD
  calc (matchingK₁ a b D * (matchingK a b D)⁻¹).transpose
      = ((matchingK a b D)⁻¹).transpose * (matchingK₁ a b D).transpose := by
        rw [Matrix.transpose_mul]
    _ = ((matchingK a b D)⁻¹).transpose * (matchingK₁ a b D).transpose *
          (matchingK a b D * (matchingK a b D)⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hK, mul_one]
    _ = ((matchingK a b D)⁻¹).transpose *
          ((matchingK₁ a b D).transpose * matchingK a b D) * (matchingK a b D)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = ((matchingK a b D)⁻¹).transpose *
          ((matchingK a b D).transpose * matchingK₁ a b D) * (matchingK a b D)⁻¹ := by
        rw [h2]
    _ = (((matchingK a b D)⁻¹).transpose * (matchingK a b D).transpose) *
          (matchingK₁ a b D * (matchingK a b D)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = matchingK₁ a b D * (matchingK a b D)⁻¹ := by
        rw [inv_T_right _ hK, one_mul]

include hab hD in
/-- The middle block matrix of `eq:rad-eq-tm11` is symmetric. -/
theorem matchingK_middle_block_transpose (hK : IsUnit (matchingK a b D).det) :
    (Matrix.fromBlocks ((matchingK a b D)⁻¹ * Matrix.diagonal a) (matchingK a b D)⁻¹
        ((matchingK a b D)⁻¹).transpose (matchingK₁ a b D * (matchingK a b D)⁻¹)).transpose =
      Matrix.fromBlocks ((matchingK a b D)⁻¹ * Matrix.diagonal a) (matchingK a b D)⁻¹
        ((matchingK a b D)⁻¹).transpose (matchingK₁ a b D * (matchingK a b D)⁻¹) := by
  rw [Matrix.fromBlocks_transpose, matchingK_inv_mul_diag_transpose a b D hD hK,
    Matrix.transpose_transpose, matchingK₁_mul_inv_transpose a b hab D hD hK]

end Inverse

/-- Equivalence form of the matching system `eq:rad-eq-tm8`. -/
theorem matching_system_iff (a b : n → ℝ) (D : Matrix n n ℝ) (x z p q : n → ℝ) :
    (z = D *ᵥ x - p ∧ -(Matrix.diagonal b *ᵥ x) + Matrix.diagonal a *ᵥ z = q) ↔
      (matchingK a b D *ᵥ x = q + Matrix.diagonal a *ᵥ p ∧ z = D *ᵥ x - p) := by
  have key : ∀ z : n → ℝ, z = D *ᵥ x - p →
      -(Matrix.diagonal b *ᵥ x) + Matrix.diagonal a *ᵥ z =
        matchingK a b D *ᵥ x - Matrix.diagonal a *ᵥ p := by
    intro z hz
    subst hz
    simp only [matchingK, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨?_, hz⟩
    rw [key z hz] at h
    exact eq_add_of_sub_eq h
  · rintro ⟨h, hz⟩
    refine ⟨hz, ?_⟩
    rw [key z hz, h]
    abel

/-- Solution of the matching system for the inner coefficient `x`. -/
theorem matching_solution_x (a b : n → ℝ) (D : Matrix n n ℝ)
    (hK : IsUnit (matchingK a b D).det) (x z p q : n → ℝ)
    (hsys : z = D *ᵥ x - p ∧ -(Matrix.diagonal b *ᵥ x) + Matrix.diagonal a *ᵥ z = q) :
    x = ((matchingK a b D)⁻¹ * Matrix.diagonal a) *ᵥ p + (matchingK a b D)⁻¹ *ᵥ q := by
  obtain ⟨h, _⟩ := (matching_system_iff a b D x z p q).1 hsys
  calc x = (matchingK a b D)⁻¹ *ᵥ (matchingK a b D *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hK, Matrix.one_mulVec]
    _ = (matchingK a b D)⁻¹ *ᵥ (q + Matrix.diagonal a *ᵥ p) := by rw [h]
    _ = ((matchingK a b D)⁻¹ * Matrix.diagonal a) *ᵥ p + (matchingK a b D)⁻¹ *ᵥ q := by
        rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
        abel

/-- Solution of the matching system for the outer coefficient `A x + B z`. -/
theorem matching_solution_outer (a b : n → ℝ) (hab : ∀ i, a i ^ 2 + b i ^ 2 = 1)
    (D : Matrix n n ℝ) (hD : D.transpose = D) (hK : IsUnit (matchingK a b D).det)
    (x z p q : n → ℝ)
    (hsys : z = D *ᵥ x - p ∧ -(Matrix.diagonal b *ᵥ x) + Matrix.diagonal a *ᵥ z = q) :
    Matrix.diagonal a *ᵥ x + Matrix.diagonal b *ᵥ z =
      ((matchingK a b D)⁻¹).transpose *ᵥ p +
        (matchingK₁ a b D * (matchingK a b D)⁻¹) *ᵥ q := by
  have hx := matching_solution_x a b D hK x z p q hsys
  have hz := hsys.1
  have h1 : Matrix.diagonal a *ᵥ x + Matrix.diagonal b *ᵥ z =
      matchingK₁ a b D *ᵥ x - Matrix.diagonal b *ᵥ p := by
    rw [hz]
    simp only [matchingK₁, Matrix.add_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  have h4a := matchingK₁_mul_inv_mul_diag_sub a b hab D hD hK
  rw [h1, hx]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  rw [← h4a, Matrix.sub_mulVec, Matrix.mul_assoc]
  abel

/-- The diagonal part has a coordinatewise lower bound in sup norm. -/
private lemma diag_lower (δ : ℝ) (hδ : 0 < δ) (c : n → ℝ) (hc : ∀ i, δ ≤ |c i|)
    (x : n → ℝ) : δ * ‖x‖ ≤ ‖Matrix.diagonal c *ᵥ x‖ := by
  have h0 : 0 ≤ ‖Matrix.diagonal c *ᵥ x‖ / δ := by positivity
  have h : ‖x‖ ≤ ‖Matrix.diagonal c *ᵥ x‖ / δ := by
    rw [pi_norm_le_iff_of_nonneg h0]
    intro i
    rw [le_div_iff₀ hδ, Real.norm_eq_abs]
    have h1 : |(Matrix.diagonal c *ᵥ x) i| ≤ ‖Matrix.diagonal c *ᵥ x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (Matrix.diagonal c *ᵥ x) i
    rw [Matrix.mulVec_diagonal, abs_mul] at h1
    nlinarith [abs_nonneg (x i), hc i]
  rw [le_div_iff₀ hδ] at h
  linarith

private lemma matchingK_eq_diag (a b d : n → ℝ) (E D : Matrix n n ℝ)
    (hD : D = Matrix.diagonal d + E) :
    matchingK a b D = Matrix.diagonal (fun i => a i * d i - b i) + Matrix.diagonal a * E := by
  subst hD
  have h : Matrix.diagonal (fun i => a i * d i - b i) =
      Matrix.diagonal (fun i => a i * d i) - Matrix.diagonal b := by
    rw [← Matrix.diagonal_sub]
  unfold matchingK
  rw [Matrix.mul_add, Matrix.diagonal_mul_diagonal, h]
  abel

/-- Invertibility of `K` from the selected angle (paper lines 534–568). -/
theorem matchingK_lower_bound (a b d : n → ℝ) (E D : Matrix n n ℝ)
    (hD : D = Matrix.diagonal d + E) (δ : ℝ) (hδ : 0 < δ)
    (hdiag : ∀ i, δ ≤ |a i * d i - b i|)
    (hE : ∀ x : n → ℝ, ‖(Matrix.diagonal a * E) *ᵥ x‖ ≤ δ / 2 * ‖x‖) :
    (∀ x : n → ℝ, δ / 2 * ‖x‖ ≤ ‖matchingK a b D *ᵥ x‖) ∧
      IsUnit (matchingK a b D).det ∧
      ∀ y : n → ℝ, ‖(matchingK a b D)⁻¹ *ᵥ y‖ ≤ 2 / δ * ‖y‖ := by
  have hlow : ∀ x : n → ℝ, δ / 2 * ‖x‖ ≤ ‖matchingK a b D *ᵥ x‖ := by
    intro x
    have h1 := diag_lower δ hδ (fun i => a i * d i - b i) hdiag x
    have h2 := hE x
    have e : matchingK a b D *ᵥ x = Matrix.diagonal (fun i => a i * d i - b i) *ᵥ x +
        (Matrix.diagonal a * E) *ᵥ x := by
      rw [matchingK_eq_diag a b d E D hD, Matrix.add_mulVec]
    have e' : Matrix.diagonal (fun i => a i * d i - b i) *ᵥ x =
        matchingK a b D *ᵥ x - (Matrix.diagonal a * E) *ᵥ x := by
      rw [e]; abel
    have h3 : ‖Matrix.diagonal (fun i => a i * d i - b i) *ᵥ x‖ ≤
        ‖matchingK a b D *ᵥ x‖ + ‖(Matrix.diagonal a * E) *ᵥ x‖ := by
      rw [e']; exact norm_sub_le _ _
    linarith
  have hinj : Function.Injective (matchingK a b D).mulVec := by
    intro x y hxy
    have h := hlow (x - y)
    rw [Matrix.mulVec_sub, hxy, sub_self, norm_zero] at h
    have hpos : 0 < δ / 2 := by linarith
    have h' : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  have hunit : IsUnit (matchingK a b D) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit (matchingK a b D).det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  refine ⟨hlow, hdet, ?_⟩
  intro y
  have hKx : matchingK a b D *ᵥ ((matchingK a b D)⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have h := hlow ((matchingK a b D)⁻¹ *ᵥ y)
  rw [hKx] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  linarith

/-- The scalar identity of `eq:rad-eq-tm9`; the right factor is the sine of the angle between
`v` and `(1, d)`. -/
theorem abs_mul_sub_eq_sqrt_mul_sine (v : ℝ × ℝ) (hv : v.1 ^ 2 + v.2 ^ 2 = 1) (d : ℝ) :
    |v.1 * d - v.2| =
      Real.sqrt (1 + d ^ 2) *
        (|v.1 * d - v.2 * 1| /
          (Real.sqrt (v.1 ^ 2 + v.2 ^ 2) * Real.sqrt (1 ^ 2 + d ^ 2))) := by
  have hp : 0 < Real.sqrt (1 + d ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [hv, Real.sqrt_one, one_pow, one_mul, mul_one]
  field_simp

end ContinuousFlexibility.Radial
