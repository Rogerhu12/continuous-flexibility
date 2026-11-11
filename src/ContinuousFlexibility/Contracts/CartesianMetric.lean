import ContinuousFlexibility.Contracts.CartesianHeight
import ContinuousFlexibility.Geometry.FlatDevelopment
import ContinuousFlexibility.Geometry.CartesianCoframe

/-!
# The actual rotational metric in Cartesian coordinates

The metric uses explicit Euclidean coordinate pairings, not the max norm
on the product coordinate space. Its polar pullback and the height pullback
are proved for actual derivatives, so the Cartesian remainder is the same
tensor as the positive polar remainder of the analytic core.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def polarMap (p : PolarPoint) : PolarPoint := polarPosition p.1 p.2

def polarJacobian (p : PolarPoint) : PolarPoint →L[ℝ] PolarPoint :=
  ((Real.cos p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ -
    (p.1 * Real.sin p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
  ((Real.sin p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (p.1 * Real.cos p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem polarJacobian_apply (p v : PolarPoint) :
    polarJacobian p v =
      (Real.cos p.2 * v.1 - p.1 * Real.sin p.2 * v.2,
        Real.sin p.2 * v.1 + p.1 * Real.cos p.2 * v.2) := by
  simp [polarJacobian, smul_eq_mul]

theorem hasFDerivAt_polarMap (p : PolarPoint) :
    HasFDerivAt polarMap (polarJacobian p) p := by
  have hfst : HasFDerivAt (Prod.fst : PolarPoint → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : PolarPoint → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  have hc := (Real.hasDerivAt_cos p.2).hasFDerivAt.comp p hsnd
  have hs := (Real.hasDerivAt_sin p.2).hasFDerivAt.comp p hsnd
  have h := (hfst.mul hc).prodMk (hfst.mul hs)
  convert h using 1
  · funext q
    simp [polarMap, polarPosition, Function.comp_apply, Pi.mul_apply]
  · apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext <;>
      simp [polarJacobian, smul_eq_mul, ContinuousLinearMap.comp_apply] <;> ring

theorem polarJacobian_bijective {p : PolarPoint} (hr : p.1 ≠ 0) :
    Function.Bijective (polarJacobian p) := by
  let η₁ : PlaneOneForm := ⟨fun _ => Real.cos p.2, fun _ => -p.1 * Real.sin p.2⟩
  let η₂ : PlaneOneForm := ⟨fun _ => Real.sin p.2, fun _ => p.1 * Real.cos p.2⟩
  have hJ : polarJacobian p = coframeLinearMap η₁ η₂ p := by
    apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext <;> simp [polarJacobian, coframeLinearMap, PlaneOneForm.toCLM, η₁, η₂,
      smul_eq_mul]; ring
  have hw : wedgeCoefficient η₁ η₂ p = p.1 := by
    change Real.cos p.2 * (p.1 * Real.cos p.2) -
      (-p.1 * Real.sin p.2) * Real.sin p.2 = p.1
    calc
      _ = p.1 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
  rw [hJ]
  apply coframeLinearMap_bijective
  rw [hw]
  exact hr

def cartesianProfileFactor (w : ℝ → ℝ) (x : PolarPoint) : ℝ :=
  w (cartesianRadius x) / cartesianRadius x

def cartesianMetric (w : ℝ → ℝ) (x u v : PolarPoint) : ℝ :=
  coordinateEuclideanPair u v + cartesianProfileFactor w x ^ 2 *
    coordinateEuclideanPair x u * coordinateEuclideanPair x v

def cartesianRemainder (w : ℝ → ℝ) (Z : PolarPoint → ℝ) (x u v : PolarPoint) : ℝ :=
  cartesianMetric w x u v - fderiv ℝ Z x u * fderiv ℝ Z x v

def cartesianRemainderA (w : ℝ → ℝ) (Z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  cartesianRemainder w Z x (1, 0) (1, 0)

def cartesianRemainderB (w : ℝ → ℝ) (Z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  cartesianRemainder w Z x (1, 0) (0, 1)

def cartesianRemainderC (w : ℝ → ℝ) (Z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  cartesianRemainder w Z x (0, 1) (0, 1)

theorem coordinate_pair_polarJacobian (p u v : PolarPoint) :
    coordinateEuclideanPair (polarJacobian p u) (polarJacobian p v) =
      u.1 * v.1 + p.1 ^ 2 * u.2 * v.2 := by
  rw [polarJacobian_apply, polarJacobian_apply]
  unfold coordinateEuclideanPair
  dsimp only
  calc
    _ = (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) *
        (u.1 * v.1 + p.1 ^ 2 * u.2 * v.2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, one_mul]

theorem coordinate_pair_position_polarJacobian (p v : PolarPoint) :
    coordinateEuclideanPair (polarMap p) (polarJacobian p v) = p.1 * v.1 := by
  rw [polarJacobian_apply]
  unfold coordinateEuclideanPair polarMap polarPosition
  dsimp only
  calc
    _ = p.1 * v.1 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

theorem cartesianMetric_polar_pullback (w : ℝ → ℝ) {p : PolarPoint}
    (hr : 0 < p.1) (u v : PolarPoint) :
    cartesianMetric w (polarMap p) (polarJacobian p u) (polarJacobian p v) =
      profileEnergy w p * u.1 * v.1 + p.1 ^ 2 * u.2 * v.2 := by
  unfold cartesianMetric cartesianProfileFactor
  rw [coordinate_pair_polarJacobian, coordinate_pair_position_polarJacobian,
    coordinate_pair_position_polarJacobian,
    show cartesianRadius (polarMap p) = p.1 from cartesianRadius_polarPosition hr p.2]
  unfold profileEnergy radialEnergy
  field_simp [hr.ne']
  ring

theorem FlatAnnularCore.cartesianHeight_polar_derivative (A : FlatAnnularCore)
    {p : PolarPoint} (hr : 0 < p.1) (v : PolarPoint) :
    fderiv ℝ A.cartesianHeight (polarMap p) (polarJacobian p v) = fderiv ℝ A.z p v := by
  have hn : {q : PolarPoint | 0 < q.1} ∈ 𝓝 p :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hr
  have heq : (A.cartesianHeight ∘ polarMap) =ᶠ[𝓝 p] A.z := by
    filter_upwards [hn] with q hq
    exact A.cartesianHeight_polarPosition hq q.2
  have hd := (A.contDiff_cartesianHeight.differentiable (by simp) (polarMap p)).hasFDerivAt.comp p
    (hasFDerivAt_polarMap p)
  have hh := heq.fderiv_eq (𝕜 := ℝ)
  rw [hd.fderiv] at hh
  exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L v) hh

theorem FlatAnnularCore.cartesianRemainder_polar_pullback (A : FlatAnnularCore)
    {p : PolarPoint} (hr : 0 < p.1) (u v : PolarPoint) :
    cartesianRemainder A.w A.cartesianHeight (polarMap p) (polarJacobian p u) (polarJacobian p v) =
      remainderBilinear p.1 (profileEnergy A.w p) (heightRadial A.z p) (heightAngular A.z p) u v := by
  unfold cartesianRemainder
  rw [cartesianMetric_polar_pullback A.w hr,
    A.cartesianHeight_polar_derivative hr, A.cartesianHeight_polar_derivative hr,
    polarCLM_apply_decompose (fderiv ℝ A.z p) u,
    polarCLM_apply_decompose (fderiv ℝ A.z p) v]
  unfold remainderBilinear heightRadial heightAngular radialPartial angularPartial
  field_simp [hr.ne']
  ring

end ContinuousFlexibility
