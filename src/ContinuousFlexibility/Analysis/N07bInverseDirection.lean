import ContinuousFlexibility.Analysis.N07bCanonicalInverseAngle
import ContinuousFlexibility.Analysis.BoundaryMixedJets

/-!
# Differentiation in every actual inverse chart direction

The matrix inverse is computed from the actual forward derivative. Both
coordinate directions, and arbitrary linear combinations of them, use the
same inverse-germ proof. This is the coordinate calculus needed when the
reference differential expression is pulled back through a current chart.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The actual inverse derivative applied to a prescribed plane vector. -/
def n07bInverseDirection (Ψ : PolarPoint → PolarPoint) (x e : PolarPoint) : PolarPoint :=
  (((fderiv ℝ Ψ x (0, 1)).2 * e.1 - (fderiv ℝ Ψ x (0, 1)).1 * e.2) /
      planeJacobian Ψ x,
    ((fderiv ℝ Ψ x (1, 0)).1 * e.2 - (fderiv ℝ Ψ x (1, 0)).2 * e.1) /
      planeJacobian Ψ x)

/-- The forward derivative sends the computed inverse direction to the
prescribed vector. No formula for an inverse map is an assumption. -/
theorem n07b_fderiv_inverseDirection
    {Ψ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hJ : planeJacobian Ψ x ≠ 0) (e : PolarPoint) :
    fderiv ℝ Ψ x (n07bInverseDirection Ψ x e) = e := by
  rw [planeCLM_apply_decompose]
  apply Prod.ext <;> dsimp only [n07bInverseDirection] <;>
    field_simp [hJ] <;> simp only [planeJacobian] <;> ring

/-- A genuine local left inverse has the computed derivative in every
direction, not just the coordinate directions. -/
theorem n07b_fderiv_inverse_direction
    {Ψ G : PolarPoint → PolarPoint} {U : Set PolarPoint} {x : PolarPoint}
    (hU : IsOpen U) (hx : x ∈ U)
    (hleft : ∀ y ∈ U, G (Ψ y) = y)
    (hΨ : DifferentiableAt ℝ Ψ x)
    (hG : DifferentiableAt ℝ G (Ψ x))
    (hJ : planeJacobian Ψ x ≠ 0) (e : PolarPoint) :
    fderiv ℝ G (Ψ x) e = n07bInverseDirection Ψ x e := by
  have hgerm : (G ∘ Ψ) =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hleft y hy
  have hchain : (fderiv ℝ G (Ψ x)).comp (fderiv ℝ Ψ x) =
      ContinuousLinearMap.id ℝ PolarPoint := by
    rw [← fderiv_comp x hG hΨ, hgerm.fderiv_eq, fderiv_id]
  calc
    fderiv ℝ G (Ψ x) e =
        fderiv ℝ G (Ψ x) (fderiv ℝ Ψ x (n07bInverseDirection Ψ x e)) :=
      congrArg (fderiv ℝ G (Ψ x)) (n07b_fderiv_inverseDirection hJ e).symm
    _ = n07bInverseDirection Ψ x e :=
      congrArg (fun L : PolarPoint →L[ℝ] PolarPoint =>
        L (n07bInverseDirection Ψ x e)) hchain

/-- Chain rule in an arbitrary actual inverse direction. -/
theorem n07b_directional_comp_inverse
    {Ψ G : PolarPoint → PolarPoint} {U : Set PolarPoint} {x : PolarPoint}
    (hU : IsOpen U) (hx : x ∈ U)
    (hleft : ∀ y ∈ U, G (Ψ y) = y)
    (hΨ : DifferentiableAt ℝ Ψ x)
    (hG : DifferentiableAt ℝ G (Ψ x))
    (hJ : planeJacobian Ψ x ≠ 0)
    {F : PolarPoint → ℝ} (hF : DifferentiableAt ℝ F x) (e : PolarPoint) :
    fderiv ℝ (F ∘ G) (Ψ x) e =
      (n07bInverseDirection Ψ x e).1 * radialPartial F x +
        (n07bInverseDirection Ψ x e).2 * angularPartial F x := by
  have hinv : G (Ψ x) = x := hleft x hx
  have hFG : DifferentiableAt ℝ F (G (Ψ x)) := by
    rw [hinv]
    exact hF
  rw [fderiv_comp (Ψ x) hFG hG, ContinuousLinearMap.comp_apply, hinv,
    n07b_fderiv_inverse_direction hU hx hleft hΨ hG hJ]
  exact polarCLM_apply_decompose (fderiv ℝ F x) (n07bInverseDirection Ψ x e)

/-- The angular formula is exactly the previous actual inverse vector. -/
theorem n07bInverseDirection_angular (Ψ : PolarPoint → PolarPoint) (x : PolarPoint) :
    n07bInverseDirection Ψ x (0, 1) = n07bInverseAngleVector Ψ x := by
  simp [n07bInverseDirection, n07bInverseAngleVector, canonicalInverseAngularVector]

/-- Smooth charts and a nonzero actual Jacobian give a smooth inverse
direction field for any fixed direction. -/
theorem n07b_contDiffAt_inverseDirection
    {Ψ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hΨ : ContDiffAt ℝ ∞ Ψ x) (hJ : planeJacobian Ψ x ≠ 0)
    (e : PolarPoint) :
    ContDiffAt ℝ ∞ (fun y => n07bInverseDirection Ψ y e) x := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ Ψ) x := hΨ.fderiv_right (by simp)
  have hr := hd.clm_apply (contDiffAt_const (c := ((1, 0) : PolarPoint)))
  have hθ := hd.clm_apply (contDiffAt_const (c := ((0, 1) : PolarPoint)))
  have hj := ContinuousFlexibility.contDiffAt_planeJacobian hΨ
  exact (((hθ.snd.mul contDiffAt_const).sub
    (hθ.fst.mul contDiffAt_const)).div hj hJ).prodMk
    (((hr.fst.mul contDiffAt_const).sub
      (hr.snd.mul contDiffAt_const)).div hj hJ)

/-- Directional differentiation by a geometric vector field. -/
def n07bDirectionalDerivative (X : PolarPoint → PolarPoint)
    (f : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  (X x).1 * radialPartial f x + (X x).2 * angularPartial f x

theorem n07bDirectionalDerivative_eq_fderiv
    (X : PolarPoint → PolarPoint) (f : PolarPoint → ℝ) (x : PolarPoint) :
    n07bDirectionalDerivative X f x = fderiv ℝ f x (X x) :=
  (polarCLM_apply_decompose (fderiv ℝ f x) (X x)).symm

theorem n07b_contDiffAt_directionalDerivative
    {X : PolarPoint → PolarPoint} {f : PolarPoint → ℝ} {x : PolarPoint}
    (hX : ContDiffAt ℝ ∞ X x) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (n07bDirectionalDerivative X f) x :=
  (hX.fst.mul (contDiffAt_radialPartial hf (by simp))).add
    (hX.snd.mul (contDiffAt_angularPartial hf (by simp)))

theorem n07bDirectionalDerivative_congr
    (X : PolarPoint → PolarPoint) {f g : PolarPoint → ℝ} {x : PolarPoint}
    (hfg : f =ᶠ[𝓝 x] g) :
    n07bDirectionalDerivative X f x = n07bDirectionalDerivative X g x := by
  rw [n07bDirectionalDerivative_eq_fderiv, n07bDirectionalDerivative_eq_fderiv]
  exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (X x)) (hfg.fderiv_eq (𝕜 := ℝ))

theorem n07bDirectionalDerivative_mul
    (X : PolarPoint → PolarPoint) {f g : PolarPoint → ℝ} {x : PolarPoint}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    n07bDirectionalDerivative X (fun y => f y * g y) x =
      n07bDirectionalDerivative X f x * g x + f x * n07bDirectionalDerivative X g x := by
  unfold n07bDirectionalDerivative
  rw [radialPartial_mul hf hg, angularPartial_mul hf hg]
  ring

theorem n07bDirectionalDerivative_finset_sum {ι : Type*}
    (X : PolarPoint → PolarPoint) (s : Finset ι) {f : ι → PolarPoint → ℝ}
    {x : PolarPoint} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    n07bDirectionalDerivative X (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, n07bDirectionalDerivative X (f i) x := by
  classical
  rw [n07bDirectionalDerivative_eq_fderiv, fderiv_fun_sum hf]
  simp only [sum_apply]
  exact Finset.sum_congr rfl (fun i _ =>
    (n07bDirectionalDerivative_eq_fderiv X (f i) x).symm)

end ContinuousFlexibility.Analysis
