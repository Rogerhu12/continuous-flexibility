import ContinuousFlexibility.Geometry.EuclideanRigidity
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual metric differentiation toward intrinsic isometry rigidity

The metric tensor and every derivative below are actual functions and Frechet
derivatives. In particular, the Hessian transformation law is deduced from the
metric identity; it is not a connection-preservation assumption.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

abbrev PlaneMetricTensor := PolarPoint →L[ℝ] PolarPoint →L[ℝ] ℝ
abbrev PlaneMetricField := PolarPoint → PlaneMetricTensor

local instance planeMetricTensor_normedAddCommGroup : NormedAddCommGroup PlaneMetricTensor :=
  inferInstanceAs (NormedAddCommGroup (PolarPoint →L[ℝ] (PolarPoint →L[ℝ] ℝ)))

local instance planeMetricTensor_normedSpace : NormedSpace ℝ PlaneMetricTensor :=
  inferInstanceAs (NormedSpace ℝ (PolarPoint →L[ℝ] (PolarPoint →L[ℝ] ℝ)))

local instance planeMetricDerivative_normedAddCommGroup :
    NormedAddCommGroup (PolarPoint →L[ℝ] PlaneMetricTensor) := inferInstance

local instance planeMetricDerivative_normedSpace :
    NormedSpace ℝ (PolarPoint →L[ℝ] PlaneMetricTensor) := inferInstance

/-- Differentiation of a metric evaluated on two genuine derivatives of a map. -/
theorem fderiv_metric_pullback_apply
    {g : PlaneMetricField} {H : PolarPoint → PolarPoint} {x : PolarPoint}
    (hg : DifferentiableAt ℝ g (H x)) (hH : ContDiffAt ℝ 2 H x)
    (u v w : PolarPoint) :
    fderiv ℝ (fun y => g (H y) (fderiv ℝ H y u) (fderiv ℝ H y v)) x w =
      fderiv ℝ g (H x) (fderiv ℝ H x w) (fderiv ℝ H x u) (fderiv ℝ H x v) +
        g (H x) (fderiv ℝ (fderiv ℝ H) x w u) (fderiv ℝ H x v) +
        g (H x) (fderiv ℝ H x u) (fderiv ℝ (fderiv ℝ H) x w v) := by
  have hH₀ := hH.differentiableAt two_ne_zero
  have hDH := (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDu : HasFDerivAt (fun y => fderiv ℝ H y u)
      ((fderiv ℝ (fderiv ℝ H) x).flip u) x := by
    simpa using hDH.hasFDerivAt.clm_apply (hasFDerivAt_const u x)
  have hDv : HasFDerivAt (fun y => fderiv ℝ H y v)
      ((fderiv ℝ (fderiv ℝ H) x).flip v) x := by
    simpa using hDH.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hG : HasFDerivAt (fun y => g (H y))
      ((fderiv ℝ g (H x)).comp (fderiv ℝ H x)) x :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := PolarPoint) (F := PolarPoint) (G := PlaneMetricTensor)
      (g := g) (f := H) x hg.hasFDerivAt hH₀.hasFDerivAt
  have h := (hG.clm_apply hDu).clm_apply hDv
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  ring

theorem fderiv_metric_evaluation_apply
    {g : PlaneMetricField} {x : PolarPoint} (hg : DifferentiableAt ℝ g x)
    (u v w : PolarPoint) :
    fderiv ℝ (fun y => g y u v) x w = fderiv ℝ g x w u v := by
  have h := (hg.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x)
  rw [h.fderiv]
  simp

/-- The actual first derivative of the intrinsic metric identity. -/
theorem differentiated_metric_identity
    {g : PlaneMetricField} {H : PolarPoint → PolarPoint} {x : PolarPoint}
    (hg₀ : DifferentiableAt ℝ g x) (hgH : DifferentiableAt ℝ g (H x))
    (hH : ContDiffAt ℝ 2 H x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : PolarPoint,
      g (H y) (fderiv ℝ H y u) (fderiv ℝ H y v) = g y u v)
    (u v w : PolarPoint) :
    fderiv ℝ g (H x) (fderiv ℝ H x w) (fderiv ℝ H x u) (fderiv ℝ H x v) +
        g (H x) (fderiv ℝ (fderiv ℝ H) x w u) (fderiv ℝ H x v) +
        g (H x) (fderiv ℝ H x u) (fderiv ℝ (fderiv ℝ H) x w v) =
      fderiv ℝ g x w u v := by
  have heq : (fun y => g (H y) (fderiv ℝ H y u) (fderiv ℝ H y v)) =ᶠ[𝓝 x]
      fun y => g y u v := hmetric.mono (fun y hy => hy u v)
  have hd := congrArg (fun L : PolarPoint →L[ℝ] ℝ => L w) (heq.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_metric_pullback_apply hgH hH, fderiv_metric_evaluation_apply hg₀] at hd
  exact hd

/-- Koszul's three-term cancellation determines the true Hessian pairing from
the actual metric and its first derivative. No connection law is assumed. -/
theorem metric_hessian_koszul
    {g : PlaneMetricField} {H : PolarPoint → PolarPoint} {x : PolarPoint}
    (hg₀ : DifferentiableAt ℝ g x) (hgH : DifferentiableAt ℝ g (H x))
    (hH : ContDiffAt ℝ 2 H x)
    (hsym : ∀ a b : PolarPoint, g (H x) a b = g (H x) b a)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : PolarPoint,
      g (H y) (fderiv ℝ H y u) (fderiv ℝ H y v) = g y u v)
    (u v w : PolarPoint) :
    2 * g (H x) (fderiv ℝ (fderiv ℝ H) x u v) (fderiv ℝ H x w) =
      fderiv ℝ g x u v w + fderiv ℝ g x v u w - fderiv ℝ g x w u v -
        fderiv ℝ g (H x) (fderiv ℝ H x u) (fderiv ℝ H x v) (fderiv ℝ H x w) -
        fderiv ℝ g (H x) (fderiv ℝ H x v) (fderiv ℝ H x u) (fderiv ℝ H x w) +
        fderiv ℝ g (H x) (fderiv ℝ H x w) (fderiv ℝ H x u) (fderiv ℝ H x v) := by
  have h1 := differentiated_metric_identity hg₀ hgH hH hmetric v w u
  have h2 := differentiated_metric_identity hg₀ hgH hH hmetric u w v
  have h3 := differentiated_metric_identity hg₀ hgH hH hmetric u v w
  have hswap := hH.isSymmSndFDerivAt (by norm_num)
  rw [hswap v u] at h2
  rw [hswap w u, hswap w v] at h3
  rw [hsym (fderiv ℝ H x v) (fderiv ℝ (fderiv ℝ H) x u w)] at h1
  rw [hsym (fderiv ℝ H x u) (fderiv ℝ (fderiv ℝ H) x v w)] at h2 h3
  linear_combination h1 + h2 - h3

def planeMetricA (g : PlaneMetricField) (x : PolarPoint) : ℝ := g x (1, 0) (1, 0)
def planeMetricB (g : PlaneMetricField) (x : PolarPoint) : ℝ := g x (1, 0) (0, 1)
def planeMetricC (g : PlaneMetricField) (x : PolarPoint) : ℝ := g x (0, 1) (0, 1)

def planeMetricDet (g : PlaneMetricField) (x : PolarPoint) : ℝ :=
  planeMetricA g x * planeMetricC g x - planeMetricB g x ^ 2

/-- The inverse metric is constructed from its actual matrix entries. -/
def planeMetricInverse (g : PlaneMetricField) (x : PolarPoint) : PolarPoint →L[ℝ] PolarPoint :=
  ((planeMetricC g x / planeMetricDet g x) • ContinuousLinearMap.fst ℝ ℝ ℝ -
    (planeMetricB g x / planeMetricDet g x) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
  ((-planeMetricB g x / planeMetricDet g x) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (planeMetricA g x / planeMetricDet g x) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem planeMetricInverse_apply (g : PlaneMetricField) (x p : PolarPoint) :
    planeMetricInverse g x p =
      (planeMetricC g x / planeMetricDet g x * p.1 -
        planeMetricB g x / planeMetricDet g x * p.2,
       -planeMetricB g x / planeMetricDet g x * p.1 +
        planeMetricA g x / planeMetricDet g x * p.2) := by
  simp [planeMetricInverse, smul_eq_mul]

theorem planeMetricTensor_coordinates (G : PlaneMetricTensor)
    (hsym : ∀ u v : PolarPoint, G u v = G v u) (u v : PolarPoint) :
    G u v = G (1, 0) (1, 0) * u.1 * v.1 +
      G (1, 0) (0, 1) * (u.1 * v.2 + u.2 * v.1) + G (0, 1) (0, 1) * u.2 * v.2 := by
  have hu : u = u.1 • ((1, 0) : PolarPoint) + u.2 • ((0, 1) : PolarPoint) := by
    ext <;> simp [smul_eq_mul]
  have hv : v = v.1 • ((1, 0) : PolarPoint) + v.2 • ((0, 1) : PolarPoint) := by
    ext <;> simp [smul_eq_mul]
  calc
    G u v = G (u.1 • (1, 0) + u.2 • (0, 1)) (v.1 • (1, 0) + v.2 • (0, 1)) := by
      rw [← hu, ← hv]
    _ = _ := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      rw [hsym (0, 1) (1, 0)]
      ring

theorem inverse_metric_pairing_algebra {A B C D : ℝ}
    (hD : D = A * C - B ^ 2) (hne : D ≠ 0) (p q u v : ℝ) :
    A * (C / D * p - B / D * q) * u +
      B * ((C / D * p - B / D * q) * v + (-B / D * p + A / D * q) * u) +
      C * (-B / D * p + A / D * q) * v = p * u + q * v := by
  field_simp [hne]
  linear_combination -(p * u + q * v) * hD

theorem planeMetricInverse_pairing {g : PlaneMetricField} {x : PolarPoint}
    (hsym : ∀ u v : PolarPoint, g x u v = g x v u) (hdet : planeMetricDet g x ≠ 0)
    (p w : PolarPoint) :
    g x (planeMetricInverse g x p) w = p.1 * w.1 + p.2 * w.2 := by
  rw [planeMetricTensor_coordinates (g x) hsym, planeMetricInverse_apply]
  exact inverse_metric_pairing_algebra rfl hdet p.1 p.2 w.1 w.2

theorem planeMetricTensor_left_injective {g : PlaneMetricField} {x : PolarPoint}
    (hsym : ∀ u v : PolarPoint, g x u v = g x v u) (hdet : planeMetricDet g x ≠ 0)
    {a b : PolarPoint} (h : ∀ w : PolarPoint, g x a w = g x b w) : a = b := by
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  rw [planeMetricTensor_coordinates (g x) hsym a (1, 0),
    planeMetricTensor_coordinates (g x) hsym b (1, 0)] at h1
  rw [planeMetricTensor_coordinates (g x) hsym a (0, 1),
    planeMetricTensor_coordinates (g x) hsym b (0, 1)] at h2
  simp only [mul_one, mul_zero, zero_add, add_zero] at h1 h2
  have hr : planeMetricDet g x * (a.1 - b.1) = 0 := by
    unfold planeMetricDet planeMetricA planeMetricB planeMetricC
    linear_combination g x (0, 1) (0, 1) * h1 - g x (1, 0) (0, 1) * h2
  have hθ : planeMetricDet g x * (a.2 - b.2) = 0 := by
    unfold planeMetricDet planeMetricA planeMetricB planeMetricC
    linear_combination g x (1, 0) (1, 0) * h2 - g x (1, 0) (0, 1) * h1
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left hdet))
    (sub_eq_zero.mp ((mul_eq_zero.mp hθ).resolve_left hdet))

def metricKoszulValue (g : PlaneMetricField) (x u v w : PolarPoint) : ℝ :=
  (fderiv ℝ g x u v w + fderiv ℝ g x v u w - fderiv ℝ g x w u v) / 2

/-- Christoffel's bilinear expression, computed from the real metric and its derivative. -/
def metricChristoffel (g : PlaneMetricField) (x u v : PolarPoint) : PolarPoint :=
  planeMetricInverse g x (metricKoszulValue g x u v (1, 0), metricKoszulValue g x u v (0, 1))

theorem metricKoszulValue_decompose_last (g : PlaneMetricField) (x u v w : PolarPoint) :
    metricKoszulValue g x u v w =
      w.1 * metricKoszulValue g x u v (1, 0) + w.2 * metricKoszulValue g x u v (0, 1) := by
  have hw : w = w.1 • ((1, 0) : PolarPoint) + w.2 • ((0, 1) : PolarPoint) := by
    ext <;> simp [smul_eq_mul]
  calc
    metricKoszulValue g x u v w =
        metricKoszulValue g x u v (w.1 • (1, 0) + w.2 • (0, 1)) := congrArg _ hw
    _ = _ := by
      simp only [metricKoszulValue, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      ring

theorem metricChristoffel_pairing {g : PlaneMetricField} {x : PolarPoint}
    (hsym : ∀ u v : PolarPoint, g x u v = g x v u) (hdet : planeMetricDet g x ≠ 0)
    (u v w : PolarPoint) :
    g x (metricChristoffel g x u v) w = metricKoszulValue g x u v w := by
  rw [metricChristoffel, planeMetricInverse_pairing hsym hdet]
  rw [metricKoszulValue_decompose_last g x u v w]
  ring

/-- The genuine Hessian transformation law of a smooth intrinsic isometry.
It is derived from the metric equation and Koszul cancellation, with the
Christoffel expression explicitly constructed above. -/
theorem metric_hessian_transformation
    {g : PlaneMetricField} {H : PolarPoint → PolarPoint} {x : PolarPoint}
    (hg₀ : DifferentiableAt ℝ g x) (hgH : DifferentiableAt ℝ g (H x))
    (hH : ContDiffAt ℝ 2 H x)
    (hsym₀ : ∀ a b : PolarPoint, g x a b = g x b a)
    (hsymH : ∀ a b : PolarPoint, g (H x) a b = g (H x) b a)
    (hdet₀ : planeMetricDet g x ≠ 0) (hdetH : planeMetricDet g (H x) ≠ 0)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : PolarPoint,
      g (H y) (fderiv ℝ H y u) (fderiv ℝ H y v) = g y u v)
    (hsurj : Function.Surjective (fderiv ℝ H x)) (u v : PolarPoint) :
    fderiv ℝ (fderiv ℝ H) x u v =
      fderiv ℝ H x (metricChristoffel g x u v) -
        metricChristoffel g (H x) (fderiv ℝ H x u) (fderiv ℝ H x v) := by
  have hp : ∀ w : PolarPoint,
      g (H x) (fderiv ℝ (fderiv ℝ H) x u v) (fderiv ℝ H x w) =
        g (H x) (fderiv ℝ H x (metricChristoffel g x u v) -
          metricChristoffel g (H x) (fderiv ℝ H x u) (fderiv ℝ H x v)) (fderiv ℝ H x w) := by
    intro w
    have hk := metric_hessian_koszul hg₀ hgH hH hsymH hmetric u v w
    have hsource := metricChristoffel_pairing hsym₀ hdet₀ u v w
    have htarget := metricChristoffel_pairing hsymH hdetH
      (fderiv ℝ H x u) (fderiv ℝ H x v) (fderiv ℝ H x w)
    have hmetric₀ := Filter.Eventually.self_of_nhds hmetric
    have htransport := hmetric₀ (metricChristoffel g x u v) w
    have hs := htransport.trans hsource
    rw [map_sub, sub_apply, hs, htarget]
    unfold metricKoszulValue
    linear_combination (1 / 2 : ℝ) * hk
  apply planeMetricTensor_left_injective hsymH hdetH
  intro z
  obtain ⟨w, rfl⟩ := hsurj z
  exact hp w

theorem metric_derivative_bijective
    {g : PlaneMetricField} {H : PolarPoint → PolarPoint} {x : PolarPoint}
    (hsym : ∀ u v : PolarPoint, g x u v = g x v u) (hdet : planeMetricDet g x ≠ 0)
    (hm : ∀ u v : PolarPoint,
      g (H x) (fderiv ℝ H x u) (fderiv ℝ H x v) = g x u v) :
    Function.Bijective (fderiv ℝ H x) := by
  have hker : ∀ u : PolarPoint, fderiv ℝ H x u = 0 → u = 0 := by
    intro u hu
    apply planeMetricTensor_left_injective hsym hdet
    intro v
    simpa [hu] using (hm u v).symm
  have hi : Function.Injective (fderiv ℝ H x) := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, huv, sub_self]
  exact ⟨hi, (LinearMap.injective_iff_surjective
    (f := (fderiv ℝ H x).toLinearMap)).mp hi⟩

theorem metricKoszulValue_decompose_second (g : PlaneMetricField) (x u v w : PolarPoint) :
    metricKoszulValue g x u v w =
      v.1 * metricKoszulValue g x u (1, 0) w + v.2 * metricKoszulValue g x u (0, 1) w := by
  have hv : v = v.1 • ((1, 0) : PolarPoint) + v.2 • ((0, 1) : PolarPoint) := by
    ext <;> simp [smul_eq_mul]
  calc
    metricKoszulValue g x u v w =
        metricKoszulValue g x u (v.1 • (1, 0) + v.2 • (0, 1)) w :=
      congrArg (fun z => metricKoszulValue g x u z w) hv
    _ = _ := by
      simp only [metricKoszulValue, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      ring

theorem metricChristoffel_decompose_second (g : PlaneMetricField) (x u v : PolarPoint) :
    metricChristoffel g x u v = v.1 • metricChristoffel g x u (1, 0) +
      v.2 • metricChristoffel g x u (0, 1) := by
  have hp : (metricKoszulValue g x u v (1, 0), metricKoszulValue g x u v (0, 1)) =
      v.1 • (metricKoszulValue g x u (1, 0) (1, 0), metricKoszulValue g x u (1, 0) (0, 1)) +
      v.2 • (metricKoszulValue g x u (0, 1) (1, 0), metricKoszulValue g x u (0, 1) (0, 1)) := by
    apply Prod.ext
    · change metricKoszulValue g x u v (1, 0) =
        v.1 * metricKoszulValue g x u (1, 0) (1, 0) + v.2 * metricKoszulValue g x u (0, 1) (1, 0)
      exact metricKoszulValue_decompose_second g x u v (1, 0)
    · change metricKoszulValue g x u v (0, 1) =
        v.1 * metricKoszulValue g x u (1, 0) (0, 1) + v.2 * metricKoszulValue g x u (0, 1) (0, 1)
      exact metricKoszulValue_decompose_second g x u v (0, 1)
  simp only [metricChristoffel, hp, map_add, map_smul]

def metricChristoffelLinear (g : PlaneMetricField) (x u : PolarPoint) : PolarPoint →L[ℝ] PolarPoint :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (metricChristoffel g x u (1, 0)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (metricChristoffel g x u (0, 1))

theorem metricChristoffelLinear_apply (g : PlaneMetricField) (x u v : PolarPoint) :
    metricChristoffelLinear g x u v = metricChristoffel g x u v := by
  simpa [metricChristoffelLinear] using (metricChristoffel_decompose_second g x u v).symm

section SmoothMetric

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem contDiffAt_metricKoszulValue
    {g : PlaneMetricField} {f u v w : X → PolarPoint} {x : X}
    (hg : ContDiffAt ℝ ∞ g (f x))
    (hf : ContDiffAt ℝ ∞ f x) (hu : ContDiffAt ℝ ∞ u x)
    (hv : ContDiffAt ℝ ∞ v x) (hw : ContDiffAt ℝ ∞ w x) :
    ContDiffAt ℝ ∞ (fun y => metricKoszulValue g (f y) (u y) (v y) (w y)) x := by
  have hdg : ContDiffAt ℝ ∞ (fderiv ℝ g) (f x) := hg.fderiv_right (by simp)
  have hd : ContDiffAt ℝ ∞ (fun y => fderiv ℝ g (f y)) x := hdg.comp x hf
  have h1 := ((hd.clm_apply hu).clm_apply hv).clm_apply hw
  have h2 := ((hd.clm_apply hv).clm_apply hu).clm_apply hw
  have h3 := ((hd.clm_apply hw).clm_apply hu).clm_apply hv
  exact ((h1.add h2).sub h3).div contDiffAt_const (by norm_num)

theorem contDiffAt_planeMetricInverse_apply
    {g : PlaneMetricField} {f p : X → PolarPoint} {x : X}
    (hg : ContDiffAt ℝ ∞ g (f x)) (hf : ContDiffAt ℝ ∞ f x)
    (hp : ContDiffAt ℝ ∞ p x) (hdet : planeMetricDet g (f x) ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => planeMetricInverse g (f y) (p y)) x := by
  have hgf : ContDiffAt ℝ ∞ (fun y => g (f y)) x := hg.comp x hf
  have hA : ContDiffAt ℝ ∞ (fun y => planeMetricA g (f y)) x :=
    (hgf.clm_apply (contDiffAt_const (c := ((1, 0) : PolarPoint)))).clm_apply contDiffAt_const
  have hB : ContDiffAt ℝ ∞ (fun y => planeMetricB g (f y)) x :=
    (hgf.clm_apply (contDiffAt_const (c := ((1, 0) : PolarPoint)))).clm_apply contDiffAt_const
  have hC : ContDiffAt ℝ ∞ (fun y => planeMetricC g (f y)) x :=
    (hgf.clm_apply (contDiffAt_const (c := ((0, 1) : PolarPoint)))).clm_apply contDiffAt_const
  have hD : ContDiffAt ℝ ∞ (fun y => planeMetricDet g (f y)) x :=
    (hA.mul hC).sub (hB.pow 2)
  have h1 := ((hC.div hD hdet).mul hp.fst).sub ((hB.div hD hdet).mul hp.snd)
  have h2 := (((hB.neg).div hD hdet).mul hp.fst).add ((hA.div hD hdet).mul hp.snd)
  simpa only [planeMetricInverse_apply, Pi.div_apply] using h1.prodMk h2

theorem contDiffAt_metricChristoffel
    {g : PlaneMetricField} {f u v : X → PolarPoint} {x : X}
    (hg : ContDiffAt ℝ ∞ g (f x)) (hf : ContDiffAt ℝ ∞ f x)
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x)
    (hdet : planeMetricDet g (f x) ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => metricChristoffel g (f y) (u y) (v y)) x := by
  have h1 := contDiffAt_metricKoszulValue hg hf hu hv
    (contDiffAt_const (c := ((1, 0) : PolarPoint)))
  have h2 := contDiffAt_metricKoszulValue hg hf hu hv
    (contDiffAt_const (c := ((0, 1) : PolarPoint)))
  exact contDiffAt_planeMetricInverse_apply hg hf (h1.prodMk h2) hdet

theorem contDiffAt_metricChristoffelLinear
    {g : PlaneMetricField} {f u : X → PolarPoint} {x : X}
    (hg : ContDiffAt ℝ ∞ g (f x)) (hf : ContDiffAt ℝ ∞ f x)
    (hu : ContDiffAt ℝ ∞ u x) (hdet : planeMetricDet g (f x) ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => metricChristoffelLinear g (f y) (u y)) x := by
  have h1 := contDiffAt_metricChristoffel hg hf hu
    (contDiffAt_const (c := ((1, 0) : PolarPoint))) hdet
  have h2 := contDiffAt_metricChristoffel hg hf hu
    (contDiffAt_const (c := ((0, 1) : PolarPoint))) hdet
  exact (contDiffAt_const.smulRight h1).add (contDiffAt_const.smulRight h2)

end SmoothMetric

abbrev PlaneFirstJet := PolarPoint × (PolarPoint →L[ℝ] PolarPoint)

local instance planeEndomorphism_finiteDimensional :
    FiniteDimensional ℝ (PolarPoint →L[ℝ] PolarPoint) :=
  FiniteDimensional.of_injective (ContinuousLinearMap.coeLM ℝ) ContinuousLinearMap.coe_injective

def metricLine (a d : PolarPoint) (t : ℝ) : PolarPoint := a + t • d

theorem contDiff_metricLine (a d : PolarPoint) : ContDiff ℝ ∞ (metricLine a d) :=
  contDiff_const.add (contDiff_id.smul_const d)

theorem hasDerivAt_metricLine (a d : PolarPoint) (t : ℝ) :
    HasDerivAt (metricLine a d) d t := by
  unfold metricLine
  have h := (hasDerivAt_const t a).add ((hasDerivAt_id t).smul_const d)
  change HasDerivAt (fun s : ℝ => a + s • d) (0 + (1 : ℝ) • d) t at h
  simpa only [zero_add, one_smul] using h

/-- The actual first-jet transport equation forced by the metric Hessian law. -/
def metricJetRHS (g : PlaneMetricField) (a d : PolarPoint) (t : ℝ) (j : PlaneFirstJet) : PlaneFirstJet :=
  (j.2 d,
    j.2.comp (metricChristoffelLinear g (metricLine a d t) d) -
      (metricChristoffelLinear g j.1 (j.2 d)).comp j.2)

theorem contDiff_metricJetRHS (g : PlaneMetricField)
    (hg : ContDiff ℝ ∞ g) (hdet : ∀ x, planeMetricDet g x ≠ 0) (a d : PolarPoint) :
    ContDiff ℝ ∞ (fun q : ℝ × PlaneFirstJet => metricJetRHS g a d q.1 q.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  have ht : ContDiffAt ℝ ∞ (fun p : ℝ × PlaneFirstJet => p.1) q := contDiffAt_fst
  have hy : ContDiffAt ℝ ∞ (fun p : ℝ × PlaneFirstJet => p.2.1) q := contDiffAt_snd.fst
  have hL : ContDiffAt ℝ ∞ (fun p : ℝ × PlaneFirstJet => p.2.2) q := contDiffAt_snd.snd
  have hv : ContDiffAt ℝ ∞ (fun p : ℝ × PlaneFirstJet => p.2.2 d) q :=
    hL.clm_apply contDiffAt_const
  have hsrc : ContDiffAt ℝ ∞ (fun p : ℝ × PlaneFirstJet => metricLine a d p.1) q :=
    contDiffAt_const.add (ht.smul_const d)
  have hΓsrc := contDiffAt_metricChristoffelLinear hg.contDiffAt hsrc
    (contDiffAt_const (c := d)) (hdet _)
  have hΓtarget := contDiffAt_metricChristoffelLinear hg.contDiffAt hy hv (hdet _)
  exact hv.prodMk ((hL.clm_comp hΓsrc).sub (hΓtarget.clm_comp hL))

/-- This derives the jet ODE from the true metric identity, using no prescribed
connection-preservation or jet-transport hypothesis. -/
theorem hasDerivAt_metricJet_along_line
    {g : PlaneMetricField} {H : PolarPoint → PolarPoint} {U : Set PolarPoint}
    (hU : IsOpen U) (hg : ContDiff ℝ ∞ g)
    (hsym : ∀ x u v, g x u v = g x v u) (hdet : ∀ x, planeMetricDet g x ≠ 0)
    (hH : ∀ x ∈ U, ContDiffAt ℝ ∞ H x)
    (hm : ∀ x ∈ U, ∀ u v : PolarPoint,
      g (H x) (fderiv ℝ H x u) (fderiv ℝ H x v) = g x u v)
    (a d : PolarPoint) {t : ℝ} (ht : metricLine a d t ∈ U) :
    HasDerivAt (fun s => (H (metricLine a d s), fderiv ℝ H (metricLine a d s)))
      (metricJetRHS g a d t (H (metricLine a d t), fderiv ℝ H (metricLine a d t))) t := by
  let x := metricLine a d t
  have hx : x ∈ U := ht
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : PolarPoint,
      g (H y) (fderiv ℝ H y u) (fderiv ℝ H y v) = g y u v := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hm y hy
  have hb := metric_derivative_bijective (hsym x) (hdet x) (hm x hx)
  have hsecond : fderiv ℝ (fderiv ℝ H) x d =
      (fderiv ℝ H x).comp (metricChristoffelLinear g x d) -
        (metricChristoffelLinear g (H x) (fderiv ℝ H x d)).comp (fderiv ℝ H x) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sub_apply, ContinuousLinearMap.comp_apply, metricChristoffelLinear_apply]
    exact metric_hessian_transformation
      (hg.differentiable (by simp) x) (hg.differentiable (by simp) (H x))
      ((hH x hx).of_le (by simp)) (hsym x) (hsym (H x)) (hdet x) (hdet (H x)) hmetric hb.2 d v
  have h₀ := ((hH x hx).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_metricLine a d t)
  have h₁ := (((hH x hx).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_metricLine a d t)
  have hj := h₀.prodMk h₁
  change HasDerivAt (fun s => (H (metricLine a d s), fderiv ℝ H (metricLine a d s)))
    (fderiv ℝ H x d, fderiv ℝ (fderiv ℝ H) x d) t at hj
  rw [hsecond] at hj
  exact hj

theorem hasDerivAt_identityMetricJet (g : PlaneMetricField) (a d : PolarPoint) (t : ℝ) :
    HasDerivAt (fun s => (metricLine a d s, ContinuousLinearMap.id ℝ PolarPoint))
      (metricJetRHS g a d t (metricLine a d t, ContinuousLinearMap.id ℝ PolarPoint)) t := by
  simpa [metricJetRHS] using (hasDerivAt_metricLine a d t).prodMk
    (hasDerivAt_const t (ContinuousLinearMap.id ℝ PolarPoint))

/-- Smoothness on the full finite-dimensional state space supplies a uniform
Lipschitz bound on an actual compact tube containing both trajectories. -/
theorem smooth_ode_unique_on_unit_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V : ℝ → E → E} {f k : ℝ → E}
    (hV : ContDiff ℝ ∞ (fun q : ℝ × E => V q.1 q.2))
    (hf : ContinuousOn f (Icc 0 1))
    (hf' : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt f (V t (f t)) (Ici t) t)
    (hk : ContinuousOn k (Icc 0 1))
    (hk' : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt k (V t (k t)) (Ici t) t)
    (hzero : f 0 = k 0) : Set.EqOn f k (Icc 0 1) := by
  have hcompact : IsCompact (f '' Icc (0 : ℝ) 1 ∪ k '' Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hf).union (isCompact_Icc.image_of_continuousOn hk)
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall (0 : E)
  have hconvex : Convex ℝ (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : E) R) :=
    (convex_Icc (0 : ℝ) 1).prod (convex_closedBall (0 : E) R)
  have hS : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : E) R) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : E) R)
  obtain ⟨K, hK⟩ := hV.contDiffOn.exists_lipschitzOnWith (by simp) hconvex hS
  have hslice : ∀ t ∈ Ico (0 : ℝ) 1, LipschitzOnWith K (V t) (Metric.closedBall (0 : E) R) := by
    intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    have h := hK.dist_le_mul (t, a) ⟨⟨ht.1, ht.2.le⟩, ha⟩ (t, b) ⟨⟨ht.1, ht.2.le⟩, hb⟩
    simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using h
  exact ODE_solution_unique_of_mem_Icc_right hslice hf hf'
    (fun t ht => hR (Or.inl ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩)) hk hk'
    (fun t ht => hR (Or.inr ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩)) hzero

/-- A smooth intrinsic isometry of a nondegenerate metric on a convex open domain
is determined by its actual value and derivative at one point. -/
theorem metric_isometry_oneJet_rigidity_on_convex
    {g : PlaneMetricField} {H : PolarPoint → PolarPoint} {U : Set PolarPoint}
    (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hg : ContDiff ℝ ∞ g) (hsym : ∀ x u v, g x u v = g x v u)
    (hdet : ∀ x, planeMetricDet g x ≠ 0)
    (hH : ∀ x ∈ U, ContDiffAt ℝ ∞ H x)
    (hm : ∀ x ∈ U, ∀ u v : PolarPoint,
      g (H x) (fderiv ℝ H x u) (fderiv ℝ H x v) = g x u v)
    {a : PolarPoint} (ha : a ∈ U) (hvalue : H a = a)
    (hder : fderiv ℝ H a = ContinuousLinearMap.id ℝ PolarPoint) :
    ∀ x ∈ U, H x = x ∧ fderiv ℝ H x = ContinuousLinearMap.id ℝ PolarPoint := by
  intro x hx
  let d := x - a
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, metricLine a d t ∈ U := by
    intro t ht
    have heq : metricLine a d t = (1 - t) • a + t • x := by
      apply Prod.ext <;> simp [metricLine, d, smul_eq_mul] <;> ring
    rw [heq]
    exact hconvex ha hx (sub_nonneg.mpr ht.2) ht.1 (by ring)
  let f : ℝ → PlaneFirstJet := fun t => (H (metricLine a d t), fderiv ℝ H (metricLine a d t))
  let k : ℝ → PlaneFirstJet := fun t => (metricLine a d t, ContinuousLinearMap.id ℝ PolarPoint)
  have hf : ContinuousOn f (Icc 0 1) := by
    intro t ht
    have hj : ContDiffAt ℝ ∞ (fun y => (H y, fderiv ℝ H y)) (metricLine a d t) :=
      (hH _ (hline t ht)).prodMk ((hH _ (hline t ht)).fderiv_right (by simp))
    exact (hj.continuousAt.comp (contDiff_metricLine a d).continuous.continuousAt).continuousWithinAt
  have hk : ContinuousOn k (Icc 0 1) :=
    ((contDiff_metricLine a d).prodMk contDiff_const).continuous.continuousOn
  have hf' : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt f (metricJetRHS g a d t (f t)) (Ici t) t := by
    intro t ht
    exact (hasDerivAt_metricJet_along_line hU hg hsym hdet hH hm a d
      (hline t ⟨ht.1, ht.2.le⟩)).hasDerivWithinAt
  have hk' : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt k (metricJetRHS g a d t (k t)) (Ici t) t := by
    intro t _
    exact (hasDerivAt_identityMetricJet g a d t).hasDerivWithinAt
  have hzero : f 0 = k 0 := by simp [f, k, metricLine, hvalue, hder]
  have hfg := smooth_ode_unique_on_unit_interval (contDiff_metricJetRHS g hg hdet a d)
    hf hf' hk hk' hzero
  have hline₁ : metricLine a d 1 = x := by
    change a + (1 : ℝ) • (x - a) = x
    rw [one_smul, ← add_sub_assoc, add_sub_cancel_left]
  have h := hfg (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  change (H (metricLine a d 1), fderiv ℝ H (metricLine a d 1)) =
    (metricLine a d 1, ContinuousLinearMap.id ℝ PolarPoint) at h
  rw [hline₁] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem metric_isometry_eq_id_of_identity_germ_on_convex
    {g : PlaneMetricField} {H : PolarPoint → PolarPoint} {U : Set PolarPoint}
    (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hg : ContDiff ℝ ∞ g) (hsym : ∀ x u v, g x u v = g x v u)
    (hdet : ∀ x, planeMetricDet g x ≠ 0)
    (hH : ∀ x ∈ U, ContDiffAt ℝ ∞ H x)
    (hm : ∀ x ∈ U, ∀ u v : PolarPoint,
      g (H x) (fderiv ℝ H x u) (fderiv ℝ H x v) = g x u v)
    {a : PolarPoint} (ha : a ∈ U) (hfix : H =ᶠ[𝓝 a] id) : Set.EqOn H id U := by
  have hd : fderiv ℝ H a = ContinuousLinearMap.id ℝ PolarPoint := by
    simpa using hfix.fderiv_eq (𝕜 := ℝ)
  intro x hx
  exact (metric_isometry_oneJet_rigidity_on_convex hU hconvex hg hsym hdet hH hm ha
    (by simpa using hfix.eq_of_nhds) hd x hx).1

end ContinuousFlexibility
