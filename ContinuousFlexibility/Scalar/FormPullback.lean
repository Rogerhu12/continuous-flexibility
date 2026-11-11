import ContinuousFlexibility.Geometry.Primitive

/-!
# Actual coordinate pullback of planar one-forms

The pullback uses the actual Fréchet derivative of the coordinate map.
Exterior differentiation commutes with this pullback: the second derivative
terms cancel by symmetry of the genuine second derivative. No independent
coordinate jets or assumed pullback differentiation rule are used.
-/

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The determinant of the actual derivative in the ordered coordinate
basis `(1,0), (0,1)`. -/
def planeJacobian (F : PolarPoint → PolarPoint) (x : PolarPoint) : ℝ :=
  (fderiv ℝ F x (1, 0)).1 * (fderiv ℝ F x (0, 1)).2 -
    (fderiv ℝ F x (1, 0)).2 * (fderiv ℝ F x (0, 1)).1

/-- Pullback of an actual one-form by the actual derivative of a map. -/
def pullbackPlaneOneForm (F : PolarPoint → PolarPoint) (α : PlaneOneForm) : PlaneOneForm :=
  ⟨fun x => α.toCLM (F x) (fderiv ℝ F x (1, 0)),
   fun x => α.toCLM (F x) (fderiv ℝ F x (0, 1))⟩

/-- The coefficient definition is the usual composition of linear maps
on every tangent vector, not only on the coordinate basis. -/
theorem toCLM_pullbackPlaneOneForm (F : PolarPoint → PolarPoint) (α : PlaneOneForm)
    (x : PolarPoint) :
    (pullbackPlaneOneForm F α).toCLM x = (α.toCLM (F x)).comp (fderiv ℝ F x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [PlaneOneForm.toCLM_apply,
    polarCLM_apply_decompose ((α.toCLM (F x)).comp (fderiv ℝ F x)) v]
  simp only [formValue, pullbackPlaneOneForm, ContinuousLinearMap.comp_apply]
  ring

theorem formValue_pullbackPlaneOneForm (F : PolarPoint → PolarPoint) (α : PlaneOneForm)
    (x v : PolarPoint) :
    formValue (pullbackPlaneOneForm F α) x v =
      formValue α (F x) (fderiv ℝ F x v) := by
  rw [← PlaneOneForm.toCLM_apply, toCLM_pullbackPlaneOneForm,
    ContinuousLinearMap.comp_apply, PlaneOneForm.toCLM_apply]

/-- Wedges transform by the actual Jacobian determinant. The algebraic
identity also holds for the totalized derivative at a nonsmooth point. -/
theorem wedgeCoefficient_pullbackPlaneOneForm
    (F : PolarPoint → PolarPoint) (α β : PlaneOneForm) (x : PolarPoint) :
    wedgeCoefficient (pullbackPlaneOneForm F α) (pullbackPlaneOneForm F β) x =
      wedgeCoefficient α β (F x) * planeJacobian F x := by
  simp only [wedgeCoefficient, pullbackPlaneOneForm, PlaneOneForm.toCLM_apply,
    formValue, planeJacobian]
  ring

/-- The full actual derivative of a pullback coefficient. This displays
the genuine second-derivative term before it cancels in the exterior
derivative. -/
theorem fderiv_pullbackPlaneOneForm_coefficient
    {F : PolarPoint → PolarPoint} {α : PlaneOneForm} {x : PolarPoint}
    (hF : ContDiffAt ℝ 2 F x)
    (hαr : DifferentiableAt ℝ α.radial (F x))
    (hαθ : DifferentiableAt ℝ α.angular (F x)) (u v : PolarPoint) :
    fderiv ℝ (fun y => α.toCLM (F y) (fderiv ℝ F y v)) x u =
      fderiv ℝ α.toCLM (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) +
        α.toCLM (F x) (fderiv ℝ (fderiv ℝ F) x u v) := by
  have hdF : DifferentiableAt ℝ F x := hF.differentiableAt (by norm_num)
  have hdDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdα := α.differentiableAt_toCLM hαr hαθ
  have hcomp : DifferentiableAt ℝ (fun y => α.toCLM (F y)) x := hdα.comp x hdF
  have hdv : DifferentiableAt ℝ (fun y => fderiv ℝ F y v) x :=
    hdDF.clm_apply (differentiableAt_const v)
  have hsecond : fderiv ℝ (fun y => fderiv ℝ F y v) x u =
      fderiv ℝ (fderiv ℝ F) x u v := by
    rw [fderiv_clm_apply hdDF (differentiableAt_const v)]
    simp
  rw [fderiv_clm_apply hcomp hdv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hsecond]
  rw [fderiv_fun_comp x hdα hdF]
  simp only [ContinuousLinearMap.comp_apply]
  ring

/-- The true coordinate exterior derivative transforms by the actual
Jacobian. Only differentiability of the form coefficients at the image
point and actual `C²` regularity of the coordinate map are required. -/
theorem exteriorCoefficient_pullbackPlaneOneForm
    {F : PolarPoint → PolarPoint} {α : PlaneOneForm} {x : PolarPoint}
    (hF : ContDiffAt ℝ 2 F x)
    (hαr : DifferentiableAt ℝ α.radial (F x))
    (hαθ : DifferentiableAt ℝ α.angular (F x)) :
    exteriorCoefficient (pullbackPlaneOneForm F α) x =
      exteriorCoefficient α (F x) * planeJacobian F x := by
  change fderiv ℝ (fun y => α.toCLM (F y) (fderiv ℝ F y (0, 1))) x (1, 0) -
    fderiv ℝ (fun y => α.toCLM (F y) (fderiv ℝ F y (1, 0))) x (0, 1) = _
  rw [fderiv_pullbackPlaneOneForm_coefficient hF hαr hαθ,
    fderiv_pullbackPlaneOneForm_coefficient hF hαr hαθ]
  calc
    _ = fderiv ℝ α.toCLM (F x) (fderiv ℝ F x (1, 0)) (fderiv ℝ F x (0, 1)) -
        fderiv ℝ α.toCLM (F x) (fderiv ℝ F x (0, 1)) (fderiv ℝ F x (1, 0)) := by
      rw [(hF.isSymmSndFDerivAt (by norm_num)) (1, 0) (0, 1)]
      ring
    _ = _ := α.fderiv_toCLM_skew hαr hαθ _ _

/-- An invertible coordinate change reflects as well as preserves the
vanishing of the actual exterior coefficient. -/
theorem exteriorCoefficient_pullback_closed_iff
    {F : PolarPoint → PolarPoint} {α : PlaneOneForm} {x : PolarPoint}
    (hF : ContDiffAt ℝ 2 F x)
    (hαr : DifferentiableAt ℝ α.radial (F x))
    (hαθ : DifferentiableAt ℝ α.angular (F x)) (hJ : planeJacobian F x ≠ 0) :
    exteriorCoefficient (pullbackPlaneOneForm F α) x = 0 ↔ exteriorCoefficient α (F x) = 0 := by
  rw [exteriorCoefficient_pullbackPlaneOneForm hF hαr hαθ]
  simp only [mul_eq_zero, hJ, or_false]

/-- Actual smooth coordinate maps and form coefficients give actual smooth
pullback coefficients. This is useful when constructing smooth Cartesian
coframes from polar formulas away from the origin. -/
theorem contDiffAt_pullbackPlaneOneForm
    {F : PolarPoint → PolarPoint} {α : PlaneOneForm} {x : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F x)
    (hαr : ContDiffAt ℝ ∞ α.radial (F x))
    (hαθ : ContDiffAt ℝ ∞ α.angular (F x)) :
    ContDiffAt ℝ ∞ (pullbackPlaneOneForm F α).radial x ∧
      ContDiffAt ℝ ∞ (pullbackPlaneOneForm F α).angular x := by
  have hcomp := (α.contDiffAt_toCLM hαr hαθ).comp x hF
  have hDF : ContDiffAt ℝ ∞ (fderiv ℝ F) x := hF.fderiv_right (by simp)
  constructor
  · exact hcomp.clm_apply (hDF.clm_apply contDiffAt_const)
  · exact hcomp.clm_apply (hDF.clm_apply contDiffAt_const)

end ContinuousFlexibility
