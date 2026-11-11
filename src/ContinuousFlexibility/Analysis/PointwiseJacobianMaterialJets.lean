import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations
import ContinuousFlexibility.Geometry.EuclideanRigidity

/-!
# Actual planar Jacobian jets from actual chart jets

Taking the four entries of the true derivative costs one order. The two
products in the determinant then use the common product interpolation
loss. No Jacobian jet estimate is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem planeDerivativeEntry_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ}
    {z : E} {F : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F x) (hjet : PointwiseMaterialJetBound p loss A z F x)
    (v : PolarPoint) (hv : ‖v‖ ≤ 1) (L : PolarPoint →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ContDiffAt ℝ ∞ (fun y => L (fderiv ℝ F y v)) x ∧
      PointwiseMaterialJetBound p (loss + 1) (fun n => A (n + 1)) z
        (fun y => L (fderiv ℝ F y v)) x := by
  have hD : ContDiffAt ℝ ∞ (fun y => fderiv ℝ F y v) x :=
    (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have hb := hjet.directionalPartial hF v hv
  have hcomp := hb.contractive_clm_comp hD L hL
  have he : (L : PolarPoint → ℝ) ∘ (fun y => fderiv ℝ F y v) =
      (fun y => L (fderiv ℝ F y v)) := by
    funext y
    exact Function.comp_apply
  rw [he] at hcomp
  have hsmooth := L.contDiff.contDiffAt.comp x hD
  rw [he] at hsmooth
  exact ⟨hsmooth, hcomp⟩

theorem planeJacobian_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ F : PolarPoint → PolarPoint, ∀ x : PolarPoint,
      ContDiffAt ℝ ∞ F x → PointwiseMaterialJetBound p inputLoss A z F x →
      PointwiseMaterialJetBound p loss B z (planeJacobian F) x := by
  obtain ⟨base, loss, hproducts⟩ :=
    pointwiseProduct_fixed_loss_material_bound (X := PolarPoint) hp hI (inputLoss + 1)
  refine ⟨base, loss, ?_⟩
  intro A hA
  obtain ⟨D, hD, hbound⟩ := hproducts (fun n => A (n + 1)) (fun n => hA (n + 1))
  refine ⟨fun n => D n + D n, fun n => add_pos (hD n) (hD n), ?_⟩
  intro z hz F x hF hjet
  let a : PolarPoint → ℝ := fun y => (fderiv ℝ F y (1, 0)).1
  let b : PolarPoint → ℝ := fun y => (fderiv ℝ F y (0, 1)).1
  let c : PolarPoint → ℝ := fun y => (fderiv ℝ F y (1, 0)).2
  let d : PolarPoint → ℝ := fun y => (fderiv ℝ F y (0, 1)).2
  have ha := planeDerivativeEntry_material_bound hF hjet (1, 0) (by simp)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  have hb := planeDerivativeEntry_material_bound hF hjet (0, 1) (by simp)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  have hc := planeDerivativeEntry_material_bound hF hjet (1, 0) (by simp)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  have hd := planeDerivativeEntry_material_bound hF hjet (0, 1) (by simp)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  have had : PointwiseMaterialJetBound p loss D z (fun y => a y * d y) x :=
    hbound z hz a d x ha.1 hd.1 ha.2 hd.2
  have hcb : PointwiseMaterialJetBound p loss D z (fun y => c y * b y) x :=
    hbound z hz c b x hc.1 hb.1 hc.2 hb.2
  exact had.sub (ha.1.mul hd.1) (hc.1.mul hb.1) hcb

end ContinuousFlexibility.Analysis
