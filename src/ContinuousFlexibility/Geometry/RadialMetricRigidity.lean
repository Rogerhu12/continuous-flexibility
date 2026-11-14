module

public import ContinuousFlexibility.Geometry.MetricIsometryRigidity
public import ContinuousFlexibility.Geometry.PlanarRotations
public import ContinuousFlexibility.Contracts.CartesianMetricRegularity
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Intrinsic rigidity of the actual radial Cartesian metric

The tensor is the genuine `cartesianMetric`, including its smooth extension
at the center. The one-jet ODE theorem is applied to its constructed tensor;
no isometry rigidity or connection preservation is added as an assumption.
The closed-disk conclusion includes the actual boundary continuity argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

local instance radialMetricTensor_normedAddCommGroup : NormedAddCommGroup PlaneMetricTensor :=
  inferInstanceAs (NormedAddCommGroup (PolarPoint →L[ℝ] (PolarPoint →L[ℝ] ℝ)))

local instance radialMetricTensor_normedSpace : NormedSpace ℝ PlaneMetricTensor :=
  inferInstanceAs (NormedSpace ℝ (PolarPoint →L[ℝ] (PolarPoint →L[ℝ] ℝ)))

def euclideanPlaneMetricTensor : PlaneMetricTensor :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)

def coordinateMetricCovector (x : PolarPoint) : PolarPoint →L[ℝ] ℝ :=
  x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

def rankOnePlaneMetric (β : PolarPoint → ℝ) (x : PolarPoint) : PlaneMetricTensor :=
  euclideanPlaneMetricTensor + β x ^ 2 •
    (coordinateMetricCovector x).smulRight (coordinateMetricCovector x)

theorem rankOnePlaneMetric_apply (β : PolarPoint → ℝ) (x u v : PolarPoint) :
    rankOnePlaneMetric β x u v = coordinateEuclideanPair u v +
      β x ^ 2 * coordinateEuclideanPair x u * coordinateEuclideanPair x v := by
  simp [rankOnePlaneMetric, euclideanPlaneMetricTensor, coordinateMetricCovector,
    coordinateEuclideanPair, smul_eq_mul]
  ring

theorem rankOnePlaneMetric_symmetric (β : PolarPoint → ℝ) (x u v : PolarPoint) :
    rankOnePlaneMetric β x u v = rankOnePlaneMetric β x v u := by
  rw [rankOnePlaneMetric_apply, rankOnePlaneMetric_apply]
  unfold coordinateEuclideanPair
  ring

theorem planeMetricDet_rankOne (β : PolarPoint → ℝ) (x : PolarPoint) :
    planeMetricDet (rankOnePlaneMetric β) x = 1 + β x ^ 2 * (x.1 ^ 2 + x.2 ^ 2) := by
  simp [planeMetricDet, planeMetricA, planeMetricB, planeMetricC,
    rankOnePlaneMetric_apply, coordinateEuclideanPair]
  ring

theorem planeMetricDet_rankOne_pos (β : PolarPoint → ℝ) (x : PolarPoint) :
    0 < planeMetricDet (rankOnePlaneMetric β) x := by
  rw [planeMetricDet_rankOne]
  have hn := mul_nonneg (sq_nonneg (β x)) (add_nonneg (sq_nonneg x.1) (sq_nonneg x.2))
  linarith

theorem contDiff_coordinateMetricCovector : ContDiff ℝ ∞ coordinateMetricCovector :=
  (contDiff_fst.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
    (contDiff_snd.smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))

theorem contDiff_rankOnePlaneMetric {β : PolarPoint → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (rankOnePlaneMetric β) :=
  contDiff_const.add ((hβ.pow 2).smul
    (contDiff_coordinateMetricCovector.smulRight contDiff_coordinateMetricCovector))

def cartesianMetricTensor (w : ℝ → ℝ) : PlaneMetricField :=
  rankOnePlaneMetric (cartesianProfileFactor w)

theorem cartesianMetricTensor_apply (w : ℝ → ℝ) (x u v : PolarPoint) :
    cartesianMetricTensor w x u v = cartesianMetric w x u v :=
  rankOnePlaneMetric_apply (cartesianProfileFactor w) x u v

theorem contDiff_cartesianMetricTensor (w : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (cartesianProfileFactor w)) : ContDiff ℝ ∞ (cartesianMetricTensor w) :=
  contDiff_rankOnePlaneMetric hf

theorem FlatAnnularCore.contDiff_metricTensor (A : FlatAnnularCore) :
    ContDiff ℝ ∞ (cartesianMetricTensor A.w) :=
  contDiff_cartesianMetricTensor A.w A.contDiff_cartesianProfileFactor

theorem cartesianMetricTensor_pos (w : ℝ → ℝ) (x : PolarPoint) {v : PolarPoint} (hv : v ≠ 0) :
    0 < cartesianMetricTensor w x v v := by
  rw [cartesianMetricTensor_apply]
  have hq := coordinateEuclideanPair_self_pos hv
  have hs := sq_nonneg (cartesianProfileFactor w x * coordinateEuclideanPair x v)
  unfold cartesianMetric
  nlinarith

theorem FlatAnnularCore.metricTensor_inner (A : FlatAnnularCore) {x : PolarPoint}
    (hx : cartesianRadius x ≤ A.a) (u v : PolarPoint) :
    cartesianMetricTensor A.w x u v = coordinateEuclideanPair u v := by
  rw [cartesianMetricTensor_apply]
  simp [cartesianMetric, cartesianProfileFactor, A.w_zero _ (Or.inl hx)]

theorem contDiff_cartesianMetricInverse (w : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (cartesianProfileFactor w)) :
    ContDiff ℝ ∞ (fun x => planeMetricInverse (cartesianMetricTensor w) x) := by
  let g := cartesianMetricTensor w
  have hg : ContDiff ℝ ∞ g := contDiff_cartesianMetricTensor w hf
  have hdet : ∀ x, planeMetricDet g x ≠ 0 :=
    fun x => (planeMetricDet_rankOne_pos (cartesianProfileFactor w) x).ne'
  have h1 : ContDiff ℝ ∞ (fun x => planeMetricInverse g x (1, 0)) :=
    contDiff_iff_contDiffAt.mpr (fun x => contDiffAt_planeMetricInverse_apply
      (f := id) (p := fun _ : PolarPoint => (1, 0)) hg.contDiffAt contDiffAt_id contDiffAt_const (hdet x))
  have h2 : ContDiff ℝ ∞ (fun x => planeMetricInverse g x (0, 1)) :=
    contDiff_iff_contDiffAt.mpr (fun x => contDiffAt_planeMetricInverse_apply
      (f := id) (p := fun _ : PolarPoint => (0, 1)) hg.contDiffAt contDiffAt_id contDiffAt_const (hdet x))
  have h : ContDiff ℝ ∞ (fun x =>
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (planeMetricInverse g x (1, 0)) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (planeMetricInverse g x (0, 1))) :=
    (contDiff_const.smulRight h1).add (contDiff_const.smulRight h2)
  have heq : (fun x =>
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (planeMetricInverse g x (1, 0)) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (planeMetricInverse g x (0, 1))) =
      fun x => planeMetricInverse g x := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    change v.1 • planeMetricInverse g x (1, 0) + v.2 • planeMetricInverse g x (0, 1) =
      planeMetricInverse g x v
    have hv : v = v.1 • ((1, 0) : PolarPoint) + v.2 • ((0, 1) : PolarPoint) := by
      ext <;> simp [smul_eq_mul]
    rw [← map_smul, ← map_smul, ← map_add, ← hv]
  rw [heq] at h
  exact h

/-- Genuine metric identity and an identity germ force the map to be the identity.
The smooth profile factor is an already proved property of the actual analytic core. -/
theorem cartesianMetric_isometry_eq_id_on_convex
    (w : ℝ → ℝ) (hf : ContDiff ℝ ∞ (cartesianProfileFactor w))
    {H : PolarPoint → PolarPoint} {U : Set PolarPoint}
    (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hH : ∀ x ∈ U, ContDiffAt ℝ ∞ H x)
    (hm : ∀ x ∈ U, ∀ u v : PolarPoint,
      cartesianMetric w (H x) (fderiv ℝ H x u) (fderiv ℝ H x v) = cartesianMetric w x u v)
    {a : PolarPoint} (ha : a ∈ U) (hfix : H =ᶠ[𝓝 a] id) : Set.EqOn H id U := by
  apply metric_isometry_eq_id_of_identity_germ_on_convex hU hconvex
    (contDiff_cartesianMetricTensor w hf)
    (rankOnePlaneMetric_symmetric (cartesianProfileFactor w))
    (fun x => (planeMetricDet_rankOne_pos (cartesianProfileFactor w) x).ne') hH
    (fun x hx u v => by simpa only [cartesianMetricTensor_apply] using hm x hx u v) ha hfix

/-- A real rotation germ fixes the same intrinsic radial isometry on a convex domain. -/
theorem cartesianMetric_isometry_eq_rotation_on_convex
    (w : ℝ → ℝ) (hf : ContDiff ℝ ∞ (cartesianProfileFactor w))
    {H : PolarPoint → PolarPoint} {U : Set PolarPoint}
    (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hH : ∀ x ∈ U, ContDiffAt ℝ ∞ H x)
    (hm : ∀ x ∈ U, ∀ u v : PolarPoint,
      cartesianMetric w (H x) (fderiv ℝ H x u) (fderiv ℝ H x v) = cartesianMetric w x u v)
    (t : ℝ) {a : PolarPoint} (ha : a ∈ U)
    (hfix : H =ᶠ[𝓝 a] (planarRotation t : PolarPoint → PolarPoint)) :
    Set.EqOn H (planarRotation t) U := by
  let K : PolarPoint → PolarPoint := fun x => planarRotation (-t) (H x)
  have hs : ∀ x ∈ U, ContDiffAt ℝ ∞ K x := by
    intro x hx
    exact (planarRotation (-t)).contDiff.contDiffAt.comp x (hH x hx)
  have hd : ∀ x ∈ U, fderiv ℝ K x = (planarRotation (-t)).comp (fderiv ℝ H x) := by
    intro x hx
    exact ((planarRotation (-t)).hasFDerivAt.comp x
      ((hH x hx).differentiableAt (by simp)).hasFDerivAt).fderiv
  have hKm : ∀ x ∈ U, ∀ u v : PolarPoint,
      cartesianMetric w (K x) (fderiv ℝ K x u) (fderiv ℝ K x v) = cartesianMetric w x u v := by
    intro x hx u v
    rw [hd x hx]
    change cartesianMetric w (planarRotation (-t) (H x))
      (planarRotation (-t) (fderiv ℝ H x u)) (planarRotation (-t) (fderiv ℝ H x v)) = _
    rw [cartesianMetric_planarRotation]
    exact hm x hx u v
  have hgerm : K =ᶠ[𝓝 a] id := by
    filter_upwards [hfix] with x hx
    change planarRotation (-t) (H x) = x
    rw [hx, planarRotation_cancel_neg]
  have hid := cartesianMetric_isometry_eq_id_on_convex w hf hU hconvex hs hKm ha hgerm
  intro x hx
  have h := congrArg (planarRotation t) (hid hx)
  simpa only [K, planarRotation_neg_cancel, id_eq] using h

/-- G10's closed-disk rigidity: normalization on a genuine open interior collar
forces the actual intrinsic isometry to be that same rotation on the whole closed disk. -/
theorem cartesianMetric_isometry_eq_rotation_on_closed_disk
    (w : ℝ → ℝ) (hf : ContDiff ℝ ∞ (cartesianProfileFactor w))
    {H : PolarPoint → PolarPoint} (hH : ContDiff ℝ ∞ H)
    {b R : ℝ} (hb : 0 ≤ b) (hbR : b < R)
    (hm : ∀ x : PolarPoint, cartesianRadius x < R → ∀ u v : PolarPoint,
      cartesianMetric w (H x) (fderiv ℝ H x u) (fderiv ℝ H x v) = cartesianMetric w x u v)
    (t : ℝ)
    (hcollar : ∀ x : PolarPoint, b < cartesianRadius x → cartesianRadius x < R →
      H x = planarRotation t x) :
    ∀ x : PolarPoint, cartesianRadius x ≤ R → H x = planarRotation t x := by
  have hR : 0 < R := hb.trans_lt hbR
  let U : Set PolarPoint := {x | cartesianRadius x < R}
  have hopen : IsOpen U := isOpen_lt continuous_cartesianRadius continuous_const
  have hconvex : Convex ℝ U := by
    have h := (convex_ball (0 : ℂ) R).linear_preimage Complex.equivRealProdCLM.symm.toLinearMap
    have heq : Complex.equivRealProdCLM.symm.toLinearMap ⁻¹' Metric.ball (0 : ℂ) R = U := by
      ext x
      simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
      rfl
    rwa [heq] at h
  let r := (b + R) / 2
  let a := polarPosition r 0
  have hr : 0 < r := by dsimp [r]; linarith
  have hra : cartesianRadius a = r := cartesianRadius_polarPosition hr 0
  have ha : a ∈ U := by change cartesianRadius a < R; rw [hra]; dsimp [r]; linarith
  have hab : b < cartesianRadius a := by rw [hra]; dsimp [r]; linarith
  have hcollarOpen : IsOpen {x : PolarPoint | b < cartesianRadius x ∧ cartesianRadius x < R} :=
    (isOpen_lt continuous_const continuous_cartesianRadius).inter hopen
  have hgerm : H =ᶠ[𝓝 a] (planarRotation t : PolarPoint → PolarPoint) := by
    filter_upwards [hcollarOpen.mem_nhds ⟨hab, ha⟩] with x hx
    exact hcollar x hx.1 hx.2
  have heq := cartesianMetric_isometry_eq_rotation_on_convex w hf hopen hconvex
    (fun _ _ => hH.contDiffAt) hm t ha hgerm
  have hclosed := heq.closure hH.continuous (planarRotation t).continuous
  have hclosure : closure U = {x : PolarPoint | cartesianRadius x ≤ R} := by
    have h := Complex.equivRealProdCLM.symm.toHomeomorph.preimage_closure (Metric.ball (0 : ℂ) R)
    rw [closure_ball (0 : ℂ) hR.ne'] at h
    have hball : Complex.equivRealProdCLM.symm.toHomeomorph ⁻¹' Metric.ball (0 : ℂ) R = U := by
      ext x
      simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
      rfl
    have hclosed : Complex.equivRealProdCLM.symm.toHomeomorph ⁻¹' Metric.closedBall (0 : ℂ) R =
        {x : PolarPoint | cartesianRadius x ≤ R} := by
      ext x
      simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
      rfl
    simpa only [hball, hclosed] using h.symm
  rw [hclosure] at hclosed
  exact fun x hx => hclosed hx

theorem FlatAnnularCore.metric_isometry_eq_rotation_on_closed_disk
    (A : FlatAnnularCore) {H : PolarPoint → PolarPoint} (hH : ContDiff ℝ ∞ H)
    {R : ℝ} (hR : A.b < R)
    (hm : ∀ x : PolarPoint, cartesianRadius x < R → ∀ u v : PolarPoint,
      cartesianMetric A.w (H x) (fderiv ℝ H x u) (fderiv ℝ H x v) = cartesianMetric A.w x u v)
    (t : ℝ)
    (hcollar : ∀ x : PolarPoint, A.b < cartesianRadius x → cartesianRadius x < R →
      H x = planarRotation t x) :
    ∀ x : PolarPoint, cartesianRadius x ≤ R → H x = planarRotation t x :=
  cartesianMetric_isometry_eq_rotation_on_closed_disk A.w A.contDiff_cartesianProfileFactor
    hH A.b_pos.le hR hm t hcollar

end ContinuousFlexibility
