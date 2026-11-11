import ContinuousFlexibility.Contracts.IsometricGraph
import Mathlib.Topology.Order.IntermediateValue

/-!
# Orientation of a normalized smooth planar development

A smooth planar homeomorphism with smooth inverse has nonzero actual
Jacobian everywhere, by the inverse chain rule. Its Jacobian is continuous.
If the map is the identity outside a Euclidean disk, its Jacobian equals
one there; connectedness of the plane then forces it to be positive
everywhere. Orientation is a proved conclusion, not an additional field
of the graph-development interface.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Actual coordinate decomposition of any planar continuous linear map. -/
theorem planeCLM_apply_decompose (L : PolarPoint →L[ℝ] PolarPoint) (u : PolarPoint) :
    L u =
      (u.1 * (L (1, 0)).1 + u.2 * (L (0, 1)).1,
       u.1 * (L (1, 0)).2 + u.2 * (L (0, 1)).2) := by
  have hu : u = u.1 • (1, 0) + u.2 • (0, 1) := by
    ext <;> simp [smul_eq_mul]
  rw [hu, map_add, map_smul, map_smul]
  ext <;> simp [smul_eq_mul]

/-- The chain rule for the determinant of the actual coordinate derivative. -/
theorem planeJacobian_comp {F G : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G (F x)) :
    planeJacobian (G ∘ F) x = planeJacobian G (F x) * planeJacobian F x := by
  unfold planeJacobian
  rw [fderiv_comp x hG hF]
  simp only [ContinuousLinearMap.comp_apply]
  rw [planeCLM_apply_decompose (fderiv ℝ G (F x)) (fderiv ℝ F x (1, 0)),
    planeCLM_apply_decompose (fderiv ℝ G (F x)) (fderiv ℝ F x (0, 1))]
  dsimp only
  ring

/-- The inverse chain rule gives a genuine left inverse of the actual
derivative; finite dimensionality then gives bijectivity. -/
theorem fderiv_bijective_of_homeomorph_smooth_inverse
    (P : PolarPoint ≃ₜ PolarPoint) {x : PolarPoint}
    (hP : DifferentiableAt ℝ (P : PolarPoint → PolarPoint) x)
    (hPi : DifferentiableAt ℝ (P.symm : PolarPoint → PolarPoint) (P x)) :
    Function.Bijective (fderiv ℝ (P : PolarPoint → PolarPoint) x) := by
  have hc := hPi.hasFDerivAt.comp x hP.hasFDerivAt
  have hid : ((P.symm : PolarPoint → PolarPoint) ∘ (P : PolarPoint → PolarPoint)) =
      (id : PolarPoint → PolarPoint) := by funext y; simp
  rw [hid] at hc
  have heq := hc.fderiv
  rw [fderiv_id] at heq
  have hleft : Function.LeftInverse (fderiv ℝ (P.symm : PolarPoint → PolarPoint) (P x))
      (fderiv ℝ (P : PolarPoint → PolarPoint) x) := by
    intro v
    simpa using congrArg (fun L : PolarPoint →L[ℝ] PolarPoint => L v) heq.symm
  exact ⟨hleft.injective, (LinearMap.injective_iff_surjective
    (f := (fderiv ℝ (P : PolarPoint → PolarPoint) x).toLinearMap)).mp hleft.injective⟩

theorem planeJacobian_inverse_mul
    (P : PolarPoint ≃ₜ PolarPoint) {x : PolarPoint}
    (hP : DifferentiableAt ℝ (P : PolarPoint → PolarPoint) x)
    (hPi : DifferentiableAt ℝ (P.symm : PolarPoint → PolarPoint) (P x)) :
    planeJacobian (P.symm : PolarPoint → PolarPoint) (P x) *
      planeJacobian (P : PolarPoint → PolarPoint) x = 1 := by
  have hc := planeJacobian_comp hP hPi
  have hid : ((P.symm : PolarPoint → PolarPoint) ∘ (P : PolarPoint → PolarPoint)) =
      (id : PolarPoint → PolarPoint) := by funext y; simp
  rw [hid] at hc
  simpa [planeJacobian] using hc.symm

theorem planeJacobian_ne_zero_of_homeomorph_smooth_inverse
    (P : PolarPoint ≃ₜ PolarPoint) {x : PolarPoint}
    (hP : DifferentiableAt ℝ (P : PolarPoint → PolarPoint) x)
    (hPi : DifferentiableAt ℝ (P.symm : PolarPoint → PolarPoint) (P x)) :
    planeJacobian (P : PolarPoint → PolarPoint) x ≠ 0 := by
  intro hz
  have hc := planeJacobian_inverse_mul P hP hPi
  rw [hz, mul_zero] at hc
  exact zero_ne_one hc

theorem continuous_planeJacobian {P : PolarPoint → PolarPoint} (hP : ContDiff ℝ ∞ P) :
    Continuous (planeJacobian P) := by
  have hd := hP.continuous_fderiv (by simp)
  have hr : Continuous (fun x => fderiv ℝ P x (1, 0)) := hd.clm_apply continuous_const
  have hθ : Continuous (fun x => fderiv ℝ P x (0, 1)) := hd.clm_apply continuous_const
  exact (hr.fst.mul hθ.snd).sub (hr.snd.mul hθ.fst)

/-- Exterior identity normalization makes the actual Jacobian positive on
the whole plane. The radius uses the Euclidean complex norm already used
for the graph disk. -/
theorem planeJacobian_pos_of_normalized_homeomorph
    (P : PolarPoint ≃ₜ PolarPoint)
    (hP : ContDiff ℝ ∞ (P : PolarPoint → PolarPoint))
    (hPi : ContDiff ℝ ∞ (P.symm : PolarPoint → PolarPoint))
    {R : ℝ} (hR : 0 ≤ R)
    (hout : ∀ x, R < cartesianRadius x → P x = x) (x : PolarPoint) :
    0 < planeJacobian (P : PolarPoint → PolarPoint) x := by
  have hne (y : PolarPoint) : planeJacobian (P : PolarPoint → PolarPoint) y ≠ 0 :=
    planeJacobian_ne_zero_of_homeomorph_smooth_inverse P
      (hP.differentiable (by simp) y) (hPi.differentiable (by simp) (P y))
  let y₀ : PolarPoint := polarPosition (R + 1) 0
  have hrad : R < cartesianRadius y₀ := by
    rw [show cartesianRadius y₀ = R + 1 from
      cartesianRadius_polarPosition (by linarith) 0]
    linarith
  have hn : {y : PolarPoint | R < cartesianRadius y} ∈ 𝓝 y₀ :=
    (isOpen_lt continuous_const continuous_cartesianRadius).mem_nhds hrad
  have hgerm : (P : PolarPoint → PolarPoint) =ᶠ[𝓝 y₀] id := by
    filter_upwards [hn] with y hy
    exact hout y hy
  have hJ : planeJacobian (P : PolarPoint → PolarPoint) y₀ = 1 := by
    unfold planeJacobian
    rw [hgerm.fderiv_eq]
    simp
  by_contra hpos
  obtain ⟨y, hy⟩ := intermediate_value_univ₂
    (a := x) (b := y₀) (g := fun _ : PolarPoint => (0 : ℝ))
    (continuous_planeJacobian hP) continuous_const (not_lt.mp hpos)
    (by rw [hJ]; norm_num)
  exact hne y hy

theorem IsometricGraphDevelopment.planar_orientation
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) :
    0 < planeJacobian (D.planar : PolarPoint → PolarPoint) x :=
  planeJacobian_pos_of_normalized_homeomorph D.planar D.smooth_planar D.smooth_inverse
    A.b_pos.le D.normalized_outside x

theorem FlatAnnularCore.graphDevelopment_orientation (A : FlatAnnularCore) (x : PolarPoint) :
    0 < planeJacobian (A.graphDevelopment.planar : PolarPoint → PolarPoint) x :=
  A.graphDevelopment.planar_orientation x

end ContinuousFlexibility
