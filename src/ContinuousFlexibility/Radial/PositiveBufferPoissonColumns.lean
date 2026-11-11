import ContinuousFlexibility.Radial.PositiveBufferCorrectedData
import Mathlib.Data.Matrix.Mul

/-!
# Classical Poisson columns from the corrected Green columns

The same finite linear combination is used for the representative and
the scalar row. Its boundary values and conormal matrix follow from
the actual corrected traces and the inverse of their normalized matrix.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Matrix
open ContinuousFlexibility.Statements
open scoped ContDiff

def positiveBufferPoissonTraceMatrix (B : BufferData) (A : Fin 2 → ℝ)
    (r : Fin 2 → ℝ → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => sqrt (A i) * r j (bufferCut B i)

def positiveBufferPoissonRepresentative (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → ℝ → ℝ) (j : Fin 2) (x : ℝ) : ℝ :=
  ∑ k, (sqrt (A j) * Q k j) * r k x

def positiveBufferPoissonScalarCombination (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (s : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  ∑ k, (sqrt (A j) * Q k j) * s k

theorem positiveBufferPoissonRepresentative_smooth
    (A : Fin 2 → ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → ℝ → ℝ)
    (hr : ∀ k, ContDiff ℝ ∞ (r k)) (j : Fin 2) :
    ContDiff ℝ ∞ (positiveBufferPoissonRepresentative A Q r j) := by
  change ContDiff ℝ ∞ (fun x => ∑ k, (sqrt (A j) * Q k j) * r k x)
  simp only [Fin.sum_univ_two]
  exact (contDiff_const.mul (hr 0)).add (contDiff_const.mul (hr 1))

theorem positiveBufferPoissonRepresentative_hasDerivAt
    (A : Fin 2 → ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → ℝ → ℝ)
    (hr : ∀ k, ContDiff ℝ ∞ (r k)) (j : Fin 2) (x : ℝ) :
    HasDerivAt (positiveBufferPoissonRepresentative A Q r j)
      (∑ k, (sqrt (A j) * Q k j) * deriv (r k) x) x := by
  change HasDerivAt (fun y => ∑ k, (sqrt (A j) * Q k j) * r k y) _ x
  simp only [Fin.sum_univ_two]
  exact (((hr 0).differentiable (by simp) x).hasDerivAt.const_mul
    (sqrt (A j) * Q 0 j)).fun_add
      (((hr 1).differentiable (by simp) x).hasDerivAt.const_mul (sqrt (A j) * Q 1 j))

theorem positiveBufferPoissonRepresentative_deriv
    (A : Fin 2 → ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → ℝ → ℝ)
    (hr : ∀ k, ContDiff ℝ ∞ (r k)) (j : Fin 2) (x : ℝ) :
    deriv (positiveBufferPoissonRepresentative A Q r j) x =
      ∑ k, (sqrt (A j) * Q k j) * deriv (r k) x :=
  (positiveBufferPoissonRepresentative_hasDerivAt A Q r hr j x).deriv

theorem positiveBufferPoissonRepresentative_deriv_deriv
    (A : Fin 2 → ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → ℝ → ℝ)
    (hr : ∀ k, ContDiff ℝ ∞ (r k)) (j : Fin 2) (x : ℝ) :
    deriv (deriv (positiveBufferPoissonRepresentative A Q r j)) x =
      ∑ k, (sqrt (A j) * Q k j) * deriv (deriv (r k)) x := by
  have heq : deriv (positiveBufferPoissonRepresentative A Q r j) =
      positiveBufferPoissonRepresentative A Q (fun k => deriv (r k)) j :=
    funext (positiveBufferPoissonRepresentative_deriv A Q r hr j)
  rw [heq]
  exact positiveBufferPoissonRepresentative_deriv A Q (fun k => deriv (r k))
    (fun k => (contDiff_infty_iff_deriv.mp (hr k)).2) j x

theorem positiveBufferPoissonRepresentative_boundary (B : BufferData)
    (A : Fin 2 → ℝ) (hA : ∀ i, 0 < A i)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → ℝ → ℝ)
    (hQ : positiveBufferPoissonTraceMatrix B A r * Q = 1) :
    ∀ i j, positiveBufferPoissonRepresentative A Q r j (bufferCut B i) =
      if i = j then 1 else 0 := by
  intro i j
  have hentry := congrFun (congrFun hQ i) j
  simp only [Matrix.mul_apply, Matrix.one_apply, positiveBufferPoissonTraceMatrix] at hentry
  have hmul : sqrt (A i) *
      positiveBufferPoissonRepresentative A Q r j (bufferCut B i) =
        sqrt (A j) * (if i = j then 1 else 0) := by
    calc
      _ = sqrt (A j) * ∑ k, (sqrt (A i) * r k (bufferCut B i)) * Q k j := by
        simp only [positiveBufferPoissonRepresentative, Fin.sum_univ_two]
        ring
      _ = _ := by rw [hentry]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, mul_one] at hmul
    rw [if_pos rfl]
    apply mul_left_cancel₀ (sqrt_pos.mpr (hA i)).ne'
    simpa only [mul_one] using hmul
  · rw [if_neg hij, mul_zero] at hmul
    rw [if_neg hij]
    exact (mul_eq_zero.mp hmul).resolve_left (sqrt_pos.mpr (hA i)).ne'

theorem positiveBufferPoissonRepresentative_equation {B : BufferData}
    {A αout : Fin 2 → ℝ} {K η : ℝ}
    (D : PositiveBufferCorrectedData B A αout K η)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) {x : ℝ} (hx : x ∈ Ioo B.l B.h) :
    -deriv (deriv (positiveBufferPoissonRepresentative A Q D.representative j)) x +
      B.potential x * positiveBufferPoissonRepresentative A Q D.representative j x +
      positiveBufferPoissonScalarCombination A Q
        (fun k => positiveBufferBorderedScalar B.potential B.bordered (D.column k)) j *
          B.borderFunction x = 0 := by
  rw [positiveBufferPoissonRepresentative_deriv_deriv A Q D.representative D.smooth j x]
  simp only [positiveBufferPoissonRepresentative, positiveBufferPoissonScalarCombination,
    Fin.sum_univ_two]
  calc
    _ = (sqrt (A j) * Q 0 j) *
        (-deriv (deriv (D.representative 0)) x + B.potential x * D.representative 0 x +
          positiveBufferBorderedScalar B.potential B.bordered (D.column 0) * B.borderFunction x) +
      (sqrt (A j) * Q 1 j) *
        (-deriv (deriv (D.representative 1)) x + B.potential x * D.representative 1 x +
          positiveBufferBorderedScalar B.potential B.bordered (D.column 1) * B.borderFunction x) := by ring
    _ = 0 := by rw [D.equation 0 x hx, D.equation 1 x hx, mul_zero, mul_zero, add_zero]

/-- The DN identity before any matrix estimate. -/
theorem positiveBufferPoissonRepresentative_conormal {B : BufferData}
    {A αout : Fin 2 → ℝ} {K η : ℝ}
    (D : PositiveBufferCorrectedData B A αout K η) (hA : ∀ i, 0 < A i)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : positiveBufferPoissonTraceMatrix B A D.representative * Q = 1) :
    ∀ i j, bufferSign i *
      deriv (positiveBufferPoissonRepresentative A Q D.representative j) (bufferCut B i) =
        sqrt (A i) * Q i j * sqrt (A j) - (if i = j then αout i else 0) := by
  intro i j
  have hraw : bufferSign i *
      deriv (positiveBufferPoissonRepresentative A Q D.representative j) (bufferCut B i) =
      sqrt (A i) * Q i j * sqrt (A j) -
        αout i * positiveBufferPoissonRepresentative A Q D.representative j (bufferCut B i) := by
    rw [positiveBufferPoissonRepresentative_deriv A Q D.representative D.smooth j (bufferCut B i),
      Finset.mul_sum]
    calc
      _ = ∑ k, (sqrt (A j) * Q k j) *
          (bufferSign i * deriv (D.representative k) (bufferCut B i)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ k, (sqrt (A j) * Q k j) *
          ((if i = k then sqrt (A i) else 0) -
            αout i * D.representative k (bufferCut B i)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [D.conormal i k]
      _ = _ := by
        fin_cases i <;> simp only [positiveBufferPoissonRepresentative, Fin.sum_univ_two]
        · norm_num
          <;> ring
        · norm_num
          <;> ring
  rw [hraw, positiveBufferPoissonRepresentative_boundary B A hA Q D.representative hQ]
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false, mul_one, mul_zero]

end ContinuousFlexibility.Radial
