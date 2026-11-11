import ContinuousFlexibility.Geometry.SurfaceGeometry

/-!
# Actual coordinate reparameterization of surface geometry

The second derivative chain rule is proved from derivatives on a neighborhood.
Its extra tangential term vanishes against the original geometric normal.
The coordinate Jacobian then conjugates the shape matrix. The normal is kept
fixed geometrically, including under orientation-reversing coordinate maps.
Only local `C²` hypotheses are needed; no second-form transformation law or
curvature invariance is assumed.
-/

noncomputable section

namespace ContinuousFlexibility

open Matrix Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def surfaceLinearMatrix (L : PolarPoint →L[ℝ] PolarPoint) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(L (surfaceBasis 0)).1, (L (surfaceBasis 1)).1;
     (L (surfaceBasis 0)).2, (L (surfaceBasis 1)).2]

def surfaceJacobian (φ : PolarPoint → PolarPoint) (x : PolarPoint) :
    Matrix (Fin 2) (Fin 2) ℝ := surfaceLinearMatrix (fderiv ℝ φ x)

theorem surfaceCLM_apply_decompose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : PolarPoint →L[ℝ] E) (v : PolarPoint) :
    L v = v.1 • L (surfaceBasis 0) + v.2 • L (surfaceBasis 1) := by
  have hv : v = v.1 • surfaceBasis 0 + v.2 • surfaceBasis 1 := by ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]

theorem surfaceLinearMatrix_mulVec (L : PolarPoint →L[ℝ] PolarPoint) (a : Fin 2 → ℝ) :
    surfaceLinearMatrix L *ᵥ a = ![(L (a 0, a 1)).1, (L (a 0, a 1)).2] := by
  rw [surfaceCLM_apply_decompose L (a 0, a 1)]
  ext i
  fin_cases i <;> simp [surfaceLinearMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    <;> ring

theorem surfaceLinearMatrix_isUnit {L : PolarPoint →L[ℝ] PolarPoint}
    (hi : Function.Injective L) : IsUnit (surfaceLinearMatrix L) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro a b hab
  rw [surfaceLinearMatrix_mulVec, surfaceLinearMatrix_mulVec] at hab
  have hL : L (a 0, a 1) = L (b 0, b 1) := by
    apply Prod.ext
    · simpa using congrFun hab 0
    · simpa using congrFun hab 1
  have h := hi hL
  funext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem surfaceJacobian_isUnit {φ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hi : Function.Injective (fderiv ℝ φ x)) : IsUnit (surfaceJacobian φ x) :=
  surfaceLinearMatrix_isUnit hi

theorem surfaceJacobian_det_ne_zero {φ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hi : Function.Injective (fderiv ℝ φ x)) : (surfaceJacobian φ x).det ≠ 0 :=
  isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (surfaceJacobian_isUnit hi))

/-- The actual second-order chain rule, with its extra tangential term. -/
theorem secondFDeriv_surface_comp
    {F : PolarPoint → E3} {φ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : ContDiffAt ℝ 2 F (φ x)) (hφ : ContDiffAt ℝ 2 φ x) (u v : PolarPoint) :
    fderiv ℝ (fderiv ℝ (F ∘ φ)) x u v =
      fderiv ℝ (fderiv ℝ F) (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) +
      fderiv ℝ F (φ x) (fderiv ℝ (fderiv ℝ φ) x u v) := by
  have hφd : DifferentiableAt ℝ φ x := hφ.differentiableAt (by norm_num)
  have hFdd : DifferentiableAt ℝ (fderiv ℝ F) (φ x) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφdd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (F ∘ φ) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ F (φ y)).comp (fderiv ℝ φ y) := by
    filter_upwards [hφ.eventually (by simp),
      hφ.continuousAt (hF.eventually (by simp))] with y hy hFy
    change ContDiffAt ℝ 2 F (φ y) at hFy
    exact fderiv_comp y (hFy.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num))
  have hA : DifferentiableAt ℝ (fun y => fderiv ℝ F (φ y)) x := hFdd.comp x hφd
  have hAc : fderiv ℝ (fun y => fderiv ℝ F (φ y)) x =
      (fderiv ℝ (fderiv ℝ F) (φ x)).comp (fderiv ℝ φ x) :=
    (hFdd.hasFDerivAt.comp x hφd.hasFDerivAt).fderiv
  rw [heq.fderiv_eq, fderiv_clm_comp hA hφdd, hAc]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem surfaceFirstForm_comp
    {F : PolarPoint → E3} {φ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F (φ x)) (hφ : DifferentiableAt ℝ φ x)
    (u v : PolarPoint) :
    surfaceFirstForm (F ∘ φ) x u v =
      surfaceFirstForm F (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) := by
  simp [surfaceFirstForm, fderiv_comp x hF hφ]

theorem IsUnitSurfaceNormal.comp
    {F : PolarPoint → E3} {φ : PolarPoint → PolarPoint} {x : PolarPoint} {N : E3}
    (hN : IsUnitSurfaceNormal F (φ x) N)
    (hF : DifferentiableAt ℝ F (φ x)) (hφ : DifferentiableAt ℝ φ x) :
    IsUnitSurfaceNormal (F ∘ φ) x N := by
  refine ⟨hN.1, fun v => ?_⟩
  simpa [fderiv_comp x hF hφ] using hN.2 (fderiv ℝ φ x v)

theorem surfaceSecondForm_comp
    {F : PolarPoint → E3} {φ : PolarPoint → PolarPoint} {x : PolarPoint} {N : E3}
    (hF : ContDiffAt ℝ 2 F (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (hN : IsUnitSurfaceNormal F (φ x) N) (u v : PolarPoint) :
    surfaceSecondForm (F ∘ φ) N x u v =
      surfaceSecondForm F N (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) := by
  rw [surfaceSecondForm, secondFDeriv_surface_comp hF hφ, inner_add_left, hN.2, add_zero]
  rfl

theorem surfaceFirstForm_coordinates (F : PolarPoint → E3) (x u v : PolarPoint) :
    surfaceFirstForm F x u v =
      u.1 * v.1 * surfaceGram F x 0 0 + u.1 * v.2 * surfaceGram F x 0 1 +
      u.2 * v.1 * surfaceGram F x 1 0 + u.2 * v.2 * surfaceGram F x 1 1 := by
  unfold surfaceFirstForm
  rw [surfaceCLM_apply_decompose (fderiv ℝ F x) u,
    surfaceCLM_apply_decompose (fderiv ℝ F x) v]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right]
  simp only [surfaceGram, surfaceFirstForm]
  ring

theorem surfaceSecondForm_coordinates (F : PolarPoint → E3) (N : E3)
    (x u v : PolarPoint) :
    surfaceSecondForm F N x u v =
      u.1 * v.1 * surfaceSecondMatrix F N x 0 0 +
      u.1 * v.2 * surfaceSecondMatrix F N x 0 1 +
      u.2 * v.1 * surfaceSecondMatrix F N x 1 0 +
      u.2 * v.2 * surfaceSecondMatrix F N x 1 1 := by
  unfold surfaceSecondForm
  rw [surfaceCLM_apply_decompose (fderiv ℝ (fderiv ℝ F) x) u]
  simp only [_root_.add_apply, _root_.smul_apply]
  rw [surfaceCLM_apply_decompose (fderiv ℝ (fderiv ℝ F) x (surfaceBasis 0)) v,
    surfaceCLM_apply_decompose (fderiv ℝ (fderiv ℝ F) x (surfaceBasis 1)) v]
  simp only [inner_add_left, real_inner_smul_left, smul_add, smul_smul]
  simp only [surfaceSecondMatrix, surfaceSecondForm]
  ring

theorem surfaceGram_comp
    {F : PolarPoint → E3} {φ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F (φ x)) (hφ : DifferentiableAt ℝ φ x) :
    surfaceGram (F ∘ φ) x =
      (surfaceJacobian φ x)ᵀ * surfaceGram F (φ x) * surfaceJacobian φ x := by
  ext i j
  change surfaceFirstForm (F ∘ φ) x (surfaceBasis i) (surfaceBasis j) = _
  rw [surfaceFirstForm_comp hF hφ, surfaceFirstForm_coordinates]
  fin_cases i <;> fin_cases j <;>
    simp [surfaceJacobian, surfaceLinearMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

/-- The actual induced area density squared transforms by the Jacobian squared. -/
theorem surfaceGram_det_comp
    {F : PolarPoint → E3} {φ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F (φ x)) (hφ : DifferentiableAt ℝ φ x) :
    (surfaceGram (F ∘ φ) x).det =
      (surfaceJacobian φ x).det ^ 2 * (surfaceGram F (φ x)).det := by
  rw [surfaceGram_comp hF hφ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem surfaceSecondMatrix_comp
    {F : PolarPoint → E3} {φ : PolarPoint → PolarPoint} {x : PolarPoint} {N : E3}
    (hF : ContDiffAt ℝ 2 F (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (hN : IsUnitSurfaceNormal F (φ x) N) :
    surfaceSecondMatrix (F ∘ φ) N x =
      (surfaceJacobian φ x)ᵀ * surfaceSecondMatrix F N (φ x) * surfaceJacobian φ x := by
  ext i j
  change surfaceSecondForm (F ∘ φ) N x (surfaceBasis i) (surfaceBasis j) = _
  rw [surfaceSecondForm_comp hF hφ hN, surfaceSecondForm_coordinates]
  fin_cases i <;> fin_cases j <;>
    simp [surfaceJacobian, surfaceLinearMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

theorem surfaceShapeMatrix_comp
    {F : PolarPoint → E3} {φ : PolarPoint → PolarPoint} {x : PolarPoint} {N : E3}
    (hF : ContDiffAt ℝ 2 F (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (hN : IsUnitSurfaceNormal F (φ x) N)
    (himm : Function.Injective (fderiv ℝ F (φ x)))
    (hφimm : Function.Injective (fderiv ℝ φ x)) :
    surfaceShapeMatrix (F ∘ φ) N x =
      (surfaceJacobian φ x)⁻¹ * surfaceShapeMatrix F N (φ x) * surfaceJacobian φ x := by
  have hFd := hF.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hφd := hφ.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hcomp : Function.Injective (fderiv ℝ (F ∘ φ) x) := by
    rw [fderiv_comp x hFd hφd]
    exact himm.comp hφimm
  have hJ : IsUnit (surfaceJacobian φ x).det :=
    isUnit_iff_ne_zero.mpr (surfaceJacobian_det_ne_zero hφimm)
  symm
  apply surfaceShapeMatrix_unique hcomp N
  rw [surfaceGram_comp hFd hφd, surfaceSecondMatrix_comp hF hφ hN]
  calc
    _ = (surfaceJacobian φ x)ᵀ * surfaceGram F (φ x) *
        (surfaceJacobian φ x * (surfaceJacobian φ x)⁻¹) *
        surfaceShapeMatrix F N (φ x) * surfaceJacobian φ x := by
          simp only [Matrix.mul_assoc]
    _ = (surfaceJacobian φ x)ᵀ *
        (surfaceGram F (φ x) * surfaceShapeMatrix F N (φ x)) * surfaceJacobian φ x := by
          rw [Matrix.mul_nonsing_inv _ hJ]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [surfaceGram_mul_shape himm]

theorem surfaceGaussianCurvature_comp
    {F : PolarPoint → E3} {φ : PolarPoint → PolarPoint} {x : PolarPoint} {N : E3}
    (hF : ContDiffAt ℝ 2 F (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (hN : IsUnitSurfaceNormal F (φ x) N)
    (himm : Function.Injective (fderiv ℝ F (φ x)))
    (hφimm : Function.Injective (fderiv ℝ φ x)) :
    surfaceGaussianCurvature (F ∘ φ) N x = surfaceGaussianCurvature F N (φ x) := by
  rw [surfaceGaussianCurvature, surfaceShapeMatrix_comp hF hφ hN himm hφimm]
  exact Matrix.det_conj' (surfaceJacobian_isUnit hφimm) _

theorem surfaceMeanCurvature_comp
    {F : PolarPoint → E3} {φ : PolarPoint → PolarPoint} {x : PolarPoint} {N : E3}
    (hF : ContDiffAt ℝ 2 F (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (hN : IsUnitSurfaceNormal F (φ x) N)
    (himm : Function.Injective (fderiv ℝ F (φ x)))
    (hφimm : Function.Injective (fderiv ℝ φ x)) :
    surfaceMeanCurvature (F ∘ φ) N x = surfaceMeanCurvature F N (φ x) := by
  rw [surfaceMeanCurvature, surfaceShapeMatrix_comp hF hφ hN himm hφimm,
    Matrix.trace_conj' (surfaceJacobian_isUnit hφimm)]
  rfl

end ContinuousFlexibility
