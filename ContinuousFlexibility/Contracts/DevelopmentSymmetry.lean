import ContinuousFlexibility.Contracts.IsometricGraph
import Mathlib.Topology.Algebra.Group.ContinuousInv

/-!
# Reflection of the actual normalized development

Half-turn symmetry of the supplied height is transported through its
actual derivative to the Cartesian remainder metric. Hence `-P(-x)` is
another development of the same metric with the same exterior normalization.
This prepares the uniqueness argument for oddness; uniqueness is not an
assumption of the constructed reflected development.
-/

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

@[simp] theorem cartesianRadius_neg (x : PolarPoint) : cartesianRadius (-x) = cartesianRadius x := by
  simp [cartesianRadius]

theorem coordinateEuclideanPair_neg_neg (u v : PolarPoint) :
    coordinateEuclideanPair (-u) (-v) = coordinateEuclideanPair u v := by
  simp [coordinateEuclideanPair]

theorem cartesianMetric_neg_neg (w : ℝ → ℝ) (x u v : PolarPoint) :
    cartesianMetric w (-x) (-u) (-v) = cartesianMetric w x u v := by
  simp only [cartesianMetric, cartesianProfileFactor, cartesianRadius_neg,
    coordinateEuclideanPair_neg_neg]

theorem fderiv_even_apply_neg
    {Z : PolarPoint → ℝ} (heven : ∀ x, Z (-x) = Z x) {x : PolarPoint}
    (hZ : DifferentiableAt ℝ Z (-x)) (v : PolarPoint) :
    fderiv ℝ Z (-x) (-v) = fderiv ℝ Z x v := by
  have hn : HasFDerivAt (Neg.neg : PolarPoint → PolarPoint)
      (-ContinuousLinearMap.id ℝ PolarPoint) x := (hasFDerivAt_id x).neg
  have hc := hZ.hasFDerivAt.comp x hn
  have heq : (Z ∘ Neg.neg) = Z := funext heven
  rw [heq] at hc
  simpa only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply] using
    congrArg (fun L : PolarPoint →L[ℝ] ℝ => L v) hc.fderiv.symm

theorem FlatAnnularCore.cartesianRemainder_neg_neg
    (A : FlatAnnularCore) (x u v : PolarPoint) :
    cartesianRemainder A.w A.cartesianHeight (-x) (-u) (-v) =
      cartesianRemainder A.w A.cartesianHeight x u v := by
  unfold cartesianRemainder
  rw [cartesianMetric_neg_neg,
    fderiv_even_apply_neg A.cartesianHeight_even
      (A.contDiff_cartesianHeight.differentiable (by simp) (-x)),
    fderiv_even_apply_neg A.cartesianHeight_even
      (A.contDiff_cartesianHeight.differentiable (by simp) (-x))]

def reflectedPlaneHomeomorph (P : PolarPoint ≃ₜ PolarPoint) : PolarPoint ≃ₜ PolarPoint :=
  (Homeomorph.neg PolarPoint).trans (P.trans (Homeomorph.neg PolarPoint))

@[simp] theorem reflectedPlaneHomeomorph_apply (P : PolarPoint ≃ₜ PolarPoint)
    (x : PolarPoint) : reflectedPlaneHomeomorph P x = -P (-x) := rfl

@[simp] theorem reflectedPlaneHomeomorph_symm_apply (P : PolarPoint ≃ₜ PolarPoint)
    (x : PolarPoint) : (reflectedPlaneHomeomorph P).symm x = -P.symm (-x) := rfl

theorem contDiff_reflectedPlaneHomeomorph {P : PolarPoint ≃ₜ PolarPoint}
    (hP : ContDiff ℝ ∞ (P : PolarPoint → PolarPoint)) :
    ContDiff ℝ ∞ (reflectedPlaneHomeomorph P : PolarPoint → PolarPoint) :=
  (hP.comp contDiff_id.neg).neg

theorem fderiv_reflectedPlaneHomeomorph_apply
    (P : PolarPoint ≃ₜ PolarPoint) {x : PolarPoint}
    (hP : DifferentiableAt ℝ (P : PolarPoint → PolarPoint) (-x)) (v : PolarPoint) :
    fderiv ℝ (reflectedPlaneHomeomorph P : PolarPoint → PolarPoint) x v =
      -fderiv ℝ (P : PolarPoint → PolarPoint) (-x) (-v) := by
  have hn : HasFDerivAt (Neg.neg : PolarPoint → PolarPoint)
      (-ContinuousLinearMap.id ℝ PolarPoint) x := (hasFDerivAt_id x).neg
  have hc := (hP.hasFDerivAt.comp x hn).neg
  change HasFDerivAt (reflectedPlaneHomeomorph P : PolarPoint → PolarPoint)
    (-((fderiv ℝ (P : PolarPoint → PolarPoint) (-x)).comp
      (-ContinuousLinearMap.id ℝ PolarPoint))) x at hc
  rw [hc.fderiv]
  simp only [neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]

def IsometricGraphDevelopment.reflected
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) : IsometricGraphDevelopment A := by
  let P := reflectedPlaneHomeomorph D.planar
  have hs : ContDiff ℝ ∞ (P : PolarPoint → PolarPoint) :=
    contDiff_reflectedPlaneHomeomorph D.smooth_planar
  have hsi : ContDiff ℝ ∞ (P.symm : PolarPoint → PolarPoint) :=
    (D.smooth_inverse.comp contDiff_id.neg).neg
  have hout : ∀ x, A.b < cartesianRadius x → P x = x := by
    intro x hx
    change -D.planar (-x) = x
    rw [D.normalized_outside (-x) (by simpa only [cartesianRadius_neg] using hx), neg_neg]
  have hm : ∀ x u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ (P : PolarPoint → PolarPoint) x u)
        (fderiv ℝ (P : PolarPoint → PolarPoint) x v) =
          cartesianRemainder A.w A.cartesianHeight x u v := by
    intro x u v
    change coordinateEuclideanPair
      (fderiv ℝ (reflectedPlaneHomeomorph D.planar : PolarPoint → PolarPoint) x u)
      (fderiv ℝ (reflectedPlaneHomeomorph D.planar : PolarPoint → PolarPoint) x v) = _
    rw [fderiv_reflectedPlaneHomeomorph_apply D.planar
        (D.smooth_planar.differentiable (by simp) (-x)),
      fderiv_reflectedPlaneHomeomorph_apply D.planar
        (D.smooth_planar.differentiable (by simp) (-x)),
      coordinateEuclideanPair_neg_neg, D.remainder_metric, A.cartesianRemainder_neg_neg]
  obtain ⟨hG, hGe, hGi, hGm⟩ :=
    graphMap_smooth_embedding_with_metric P hs A.contDiff_cartesianHeight hm
  exact {
    planar := P
    smooth_planar := hs
    smooth_inverse := hsi
    normalized_outside := hout
    preserves_disk := image_larger_disk_of_normalized_homeomorph P le_rfl hout
    remainder_metric := hm
    smooth_graph := hG
    embedding_graph := hGe
    immersion_graph := hGi
    graph_metric := hGm }

@[simp] theorem IsometricGraphDevelopment.reflected_planar_apply
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) :
    D.reflected.planar x = -D.planar (-x) := rfl

end ContinuousFlexibility
