import ContinuousFlexibility.Geometry.GraphEmbedding
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Coordinate surface geometry from actual derivatives

The first and second fundamental forms use the actual first and second
Fréchet derivatives. A specified unit normal determines the sign of the
shape operator, with convention `S = -dN`. The matrix definition below is
the equivalent relation `I * S = II`; its invertibility is proved for
immersions. Ambient orthogonal maps transport the supplied normal, including
reflections. No outward orientation or global surface integral is asserted.
-/

noncomputable section

namespace ContinuousFlexibility

open Matrix
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def surfaceBasis : Fin 2 → PolarPoint := ![(1, 0), (0, 1)]

@[simp] theorem surfaceBasis_zero : surfaceBasis 0 = (1, 0) := rfl
@[simp] theorem surfaceBasis_one : surfaceBasis 1 = (0, 1) := rfl

def surfaceFirstForm (F : PolarPoint → E3) (x u v : PolarPoint) : ℝ :=
  inner ℝ (fderiv ℝ F x u) (fderiv ℝ F x v)

def surfaceSecondForm (F : PolarPoint → E3) (N : E3)
    (x u v : PolarPoint) : ℝ :=
  inner ℝ (fderiv ℝ (fderiv ℝ F) x u v) N

def IsUnitSurfaceNormal (F : PolarPoint → E3) (x : PolarPoint) (N : E3) : Prop :=
  ‖N‖ = 1 ∧ ∀ v : PolarPoint, inner ℝ (fderiv ℝ F x v) N = 0

def surfaceGram (F : PolarPoint → E3) (x : PolarPoint) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => surfaceFirstForm F x (surfaceBasis i) (surfaceBasis j)

def surfaceSecondMatrix (F : PolarPoint → E3) (N : E3)
    (x : PolarPoint) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => surfaceSecondForm F N x (surfaceBasis i) (surfaceBasis j)

def surfaceShapeMatrix (F : PolarPoint → E3) (N : E3)
    (x : PolarPoint) : Matrix (Fin 2) (Fin 2) ℝ :=
  (surfaceGram F x)⁻¹ * surfaceSecondMatrix F N x

def surfaceGaussianCurvature (F : PolarPoint → E3) (N : E3) (x : PolarPoint) : ℝ :=
  (surfaceShapeMatrix F N x).det

def surfaceMeanCurvature (F : PolarPoint → E3) (N : E3) (x : PolarPoint) : ℝ :=
  (surfaceShapeMatrix F N x).trace / 2

theorem surfaceBasis_linearIndependent : LinearIndependent ℝ surfaceBasis := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have h0 := congrArg Prod.fst ha
  have h1 := congrArg Prod.snd ha
  intro i
  fin_cases i
  · simpa [Fin.sum_univ_two, surfaceBasis] using h0
  · simpa [Fin.sum_univ_two, surfaceBasis] using h1

theorem surfaceGram_dotProduct (F : PolarPoint → E3) (x : PolarPoint) (a : Fin 2 → ℝ) :
    star a ⬝ᵥ (surfaceGram F x *ᵥ a) =
      inner ℝ (fderiv ℝ F x (a 0, a 1)) (fderiv ℝ F x (a 0, a 1)) := by
  have heq : (a 0, a 1) = a 0 • ((1, 0) : PolarPoint) + a 1 • ((0, 1) : PolarPoint) := by
    ext <;> simp
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, surfaceGram, surfaceFirstForm,
    surfaceBasis_zero, surfaceBasis_one, Pi.star_apply, star_trivial]
  rw [heq, map_add, map_smul, map_smul]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right]
  ring

theorem surfaceGram_posDef {F : PolarPoint → E3} {x : PolarPoint}
    (hi : Function.Injective (fderiv ℝ F x)) : (surfaceGram F x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [Matrix.conjTranspose_apply, surfaceGram, surfaceFirstForm, real_inner_comm]
  · intro a ha
    rw [surfaceGram_dotProduct]
    apply real_inner_self_pos.mpr
    intro hz
    have heq : (a 0, a 1) = (0 : PolarPoint) := hi (by simpa using hz)
    apply ha
    funext i
    fin_cases i
    · exact congrArg Prod.fst heq
    · exact congrArg Prod.snd heq

theorem surfaceGram_det_pos {F : PolarPoint → E3} {x : PolarPoint}
    (hi : Function.Injective (fderiv ℝ F x)) : 0 < (surfaceGram F x).det :=
  (surfaceGram_posDef hi).det_pos

theorem surfaceGram_mul_shape {F : PolarPoint → E3} {x : PolarPoint}
    (hi : Function.Injective (fderiv ℝ F x)) (N : E3) :
    surfaceGram F x * surfaceShapeMatrix F N x = surfaceSecondMatrix F N x := by
  exact Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr
    (ne_of_gt (surfaceGram_det_pos hi)))

theorem surfaceShapeMatrix_unique {F : PolarPoint → E3} {x : PolarPoint}
    (hi : Function.Injective (fderiv ℝ F x)) (N : E3)
    {S : Matrix (Fin 2) (Fin 2) ℝ}
    (hS : surfaceGram F x * S = surfaceSecondMatrix F N x) :
    S = surfaceShapeMatrix F N x := by
  rw [surfaceShapeMatrix, ← hS]
  symm
  exact Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr
    (ne_of_gt (surfaceGram_det_pos hi)))

theorem surfaceFirstForm_symm (F : PolarPoint → E3) (x u v : PolarPoint) :
    surfaceFirstForm F x u v = surfaceFirstForm F x v u := real_inner_comm _ _

theorem surfaceSecondForm_symm {F : PolarPoint → E3}
    (hF : ContDiff ℝ ∞ F) (N : E3) (x u v : PolarPoint) :
    surfaceSecondForm F N x u v = surfaceSecondForm F N x v u := by
  unfold surfaceSecondForm
  rw [hF.contDiffAt.isSymmSndFDerivAt (by simp) u v]

/-- Differentiating actual normal orthogonality gives the Weingarten sign convention. -/
theorem surfaceSecondForm_eq_neg_normal_derivative {F : PolarPoint → E3}
    (hF : ContDiff ℝ ∞ F) {N : PolarPoint → E3} {x : PolarPoint}
    (hN : DifferentiableAt ℝ N x)
    (hnormal : ∀ y v, inner ℝ (fderiv ℝ F y v) (N y) = 0) (u v : PolarPoint) :
    surfaceSecondForm F (N x) x u v =
      -inner ℝ (fderiv ℝ F x v) (fderiv ℝ N x u) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by simp)).differentiable (by simp) x
  have heq : (fun y => inner ℝ (fderiv ℝ F y v) (N y)) = fun _ => (0 : ℝ) := by
    funext y
    exact hnormal y v
  have hzero : fderiv ℝ (fun y => inner ℝ (fderiv ℝ F y v) (N y)) x u = 0 := by
    rw [heq]
    simp
  rw [fderiv_inner_apply ℝ (hd.clm_apply (differentiableAt_const v)) hN u,
    fderiv_clm_apply hd (differentiableAt_const v)] at hzero
  simpa [surfaceSecondForm, eq_neg_iff_add_eq_zero, add_comm] using hzero

theorem surfaceSecondMatrix_neg_normal (F : PolarPoint → E3) (N : E3) (x : PolarPoint) :
    surfaceSecondMatrix F (-N) x = -surfaceSecondMatrix F N x := by
  ext i j
  simp [surfaceSecondMatrix, surfaceSecondForm]

theorem surfaceShapeMatrix_neg_normal (F : PolarPoint → E3) (N : E3) (x : PolarPoint) :
    surfaceShapeMatrix F (-N) x = -surfaceShapeMatrix F N x := by
  simp [surfaceShapeMatrix, surfaceSecondMatrix_neg_normal]

theorem surfaceGaussianCurvature_neg_normal (F : PolarPoint → E3) (N : E3)
    (x : PolarPoint) : surfaceGaussianCurvature F (-N) x = surfaceGaussianCurvature F N x := by
  simp [surfaceGaussianCurvature, surfaceShapeMatrix_neg_normal, Matrix.det_neg]

theorem surfaceMeanCurvature_neg_normal (F : PolarPoint → E3) (N : E3)
    (x : PolarPoint) : surfaceMeanCurvature F (-N) x = -surfaceMeanCurvature F N x := by
  simp [surfaceMeanCurvature, surfaceShapeMatrix_neg_normal]
  ring

def rigidSurfaceMap (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3) (F : PolarPoint → E3)
    (x : PolarPoint) : E3 := L (F x) + c

theorem fderiv_rigidSurfaceMap (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3)
    {F : PolarPoint → E3} {x : PolarPoint} (hF : DifferentiableAt ℝ F x) :
    fderiv ℝ (rigidSurfaceMap L c F) x =
      (L : E3 →L[ℝ] E3).comp (fderiv ℝ F x) := by
  exact ((L.hasFDerivAt.comp x hF.hasFDerivAt).add_const c).fderiv

theorem secondFDeriv_rigidSurfaceMap (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3)
    {F : PolarPoint → E3} (hF : ContDiff ℝ ∞ F) (x u v : PolarPoint) :
    fderiv ℝ (fderiv ℝ (rigidSurfaceMap L c F)) x u v =
      L (fderiv ℝ (fderiv ℝ F) x u v) := by
  have heq : fderiv ℝ (rigidSurfaceMap L c F) =
      fun y => (L : E3 →L[ℝ] E3).comp (fderiv ℝ F y) := by
    funext y
    exact fderiv_rigidSurfaceMap L c (hF.differentiable (by simp) y)
  rw [heq, fderiv_clm_comp (differentiableAt_const (L : E3 →L[ℝ] E3))
    ((hF.fderiv_right (m := 1) (by simp)).differentiable (by simp) x)]
  simp

theorem surfaceFirstForm_rigidSurfaceMap (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3)
    {F : PolarPoint → E3} {x : PolarPoint} (hF : DifferentiableAt ℝ F x)
    (u v : PolarPoint) :
    surfaceFirstForm (rigidSurfaceMap L c F) x u v = surfaceFirstForm F x u v := by
  simp [surfaceFirstForm, fderiv_rigidSurfaceMap L c hF, L.inner_map_map]

theorem surfaceSecondForm_rigidSurfaceMap (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3)
    {F : PolarPoint → E3} (hF : ContDiff ℝ ∞ F) (N : E3) (x u v : PolarPoint) :
    surfaceSecondForm (rigidSurfaceMap L c F) (L N) x u v =
      surfaceSecondForm F N x u v := by
  simp [surfaceSecondForm, secondFDeriv_rigidSurfaceMap L c hF, L.inner_map_map]

theorem IsUnitSurfaceNormal.rigidSurfaceMap {F : PolarPoint → E3} {x : PolarPoint}
    {N : E3} (hN : IsUnitSurfaceNormal F x N) (hF : DifferentiableAt ℝ F x)
    (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3) :
    IsUnitSurfaceNormal (rigidSurfaceMap L c F) x (L N) := by
  refine ⟨by simpa using hN.1, fun v => ?_⟩
  simpa [fderiv_rigidSurfaceMap L c hF] using hN.2 v

theorem surfaceGram_rigidSurfaceMap (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3)
    {F : PolarPoint → E3} {x : PolarPoint} (hF : DifferentiableAt ℝ F x) :
    surfaceGram (rigidSurfaceMap L c F) x = surfaceGram F x := by
  ext i j
  exact surfaceFirstForm_rigidSurfaceMap L c hF _ _

theorem surfaceSecondMatrix_rigidSurfaceMap (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3)
    {F : PolarPoint → E3} (hF : ContDiff ℝ ∞ F) (N : E3) (x : PolarPoint) :
    surfaceSecondMatrix (rigidSurfaceMap L c F) (L N) x = surfaceSecondMatrix F N x := by
  ext i j
  exact surfaceSecondForm_rigidSurfaceMap L c hF N x _ _

theorem surfaceShapeMatrix_rigidSurfaceMap (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3)
    {F : PolarPoint → E3} (hF : ContDiff ℝ ∞ F) (N : E3) (x : PolarPoint) :
    surfaceShapeMatrix (rigidSurfaceMap L c F) (L N) x = surfaceShapeMatrix F N x := by
  simp [surfaceShapeMatrix, surfaceGram_rigidSurfaceMap L c (hF.differentiable (by simp) x),
    surfaceSecondMatrix_rigidSurfaceMap L c hF]

theorem surfaceGaussianCurvature_rigidSurfaceMap (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3)
    {F : PolarPoint → E3} (hF : ContDiff ℝ ∞ F) (N : E3) (x : PolarPoint) :
    surfaceGaussianCurvature (rigidSurfaceMap L c F) (L N) x =
      surfaceGaussianCurvature F N x := by
  simp [surfaceGaussianCurvature, surfaceShapeMatrix_rigidSurfaceMap L c hF]

theorem surfaceMeanCurvature_rigidSurfaceMap (L : E3 ≃ₗᵢ[ℝ] E3) (c : E3)
    {F : PolarPoint → E3} (hF : ContDiff ℝ ∞ F) (N : E3) (x : PolarPoint) :
    surfaceMeanCurvature (rigidSurfaceMap L c F) (L N) x =
      surfaceMeanCurvature F N x := by
  simp [surfaceMeanCurvature, surfaceShapeMatrix_rigidSurfaceMap L c hF]

theorem affineSurfaceMap_eq_rigidSurfaceMap (A : E3 ≃ᵃⁱ[ℝ] E3)
    (F : PolarPoint → E3) :
    (fun x => A (F x)) = rigidSurfaceMap A.linearIsometryEquiv (A 0) F := by
  funext x
  simpa [rigidSurfaceMap] using A.map_vadd (0 : E3) (F x)

/-- Every ambient affine isometry, including a reflection, preserves the
shape matrix when the chosen normal is transported by its linear part. -/
theorem surfaceShapeMatrix_affineIsometry (A : E3 ≃ᵃⁱ[ℝ] E3)
    {F : PolarPoint → E3} (hF : ContDiff ℝ ∞ F) (N : E3) (x : PolarPoint) :
    surfaceShapeMatrix (fun y => A (F y)) (A.linearIsometryEquiv N) x =
      surfaceShapeMatrix F N x := by
  rw [affineSurfaceMap_eq_rigidSurfaceMap]
  exact surfaceShapeMatrix_rigidSurfaceMap _ _ hF N x

theorem surfaceGaussianCurvature_affineIsometry (A : E3 ≃ᵃⁱ[ℝ] E3)
    {F : PolarPoint → E3} (hF : ContDiff ℝ ∞ F) (N : E3) (x : PolarPoint) :
    surfaceGaussianCurvature (fun y => A (F y)) (A.linearIsometryEquiv N) x =
      surfaceGaussianCurvature F N x := by
  simp [surfaceGaussianCurvature, surfaceShapeMatrix_affineIsometry A hF]

theorem surfaceMeanCurvature_affineIsometry (A : E3 ≃ᵃⁱ[ℝ] E3)
    {F : PolarPoint → E3} (hF : ContDiff ℝ ∞ F) (N : E3) (x : PolarPoint) :
    surfaceMeanCurvature (fun y => A (F y)) (A.linearIsometryEquiv N) x =
      surfaceMeanCurvature F N x := by
  simp [surfaceMeanCurvature, surfaceShapeMatrix_affineIsometry A hF]

end ContinuousFlexibility
