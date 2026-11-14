module

public import ContinuousFlexibility.Analysis.N06AiryNormalForm

/-!
# The actual physical orientation of the new reference Airy germ

The raw root chart has physical derivative `ι * Ξ'`, whereas its absolute
Jacobian is the positive slope `Ξ'`. The coordinate used at an endpoint
of a positive component includes a second factor `ι` and has derivative
`Ξ'`. The physical height uses that same absolute Jacobian. Unit reflection
and translation preserve all ordinary scalar jet bounds below.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Real
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n06AiryRootCoordinate (c : ℝ → ℝ) (r ι u : ℝ) : ℝ :=
  n06AiryRadialCoordinate c (ι * (u - r))

def n06AiryEndpointCoordinate (c : ℝ → ℝ) (r ι v u : ℝ) : ℝ :=
  v + ι * n06AiryRootCoordinate c r ι u

def n06AiryPhysicalSlope (c : ℝ → ℝ) (r ι u : ℝ) : ℝ :=
  n06AiryRadialSlope c (ι * (u - r))

def n06AiryPhysicalHeight (c w : ℝ → ℝ) (r ι u : ℝ) : ℝ :=
  (w u * n06AiryPhysicalSlope c r ι u) ^ (-1 / 2 : ℝ)

/-- A unit orientation changes no absolute ordinary jet. -/
theorem n06_abs_iteratedDeriv_oriented_center
    (f : ℝ → ℝ) (r ι : ℝ) (hι : ι = 1 ∨ ι = -1) (k : ℕ) (u : ℝ) :
    |iteratedDeriv k (fun t => f (ι * (t - r))) u| =
      |iteratedDeriv k f (ι * (u - r))| := by
  rcases hι with rfl | rfl
  · simp only [one_mul, iteratedDeriv_comp_sub_const]
  · simp only [neg_one_mul, neg_sub, iteratedDeriv_comp_const_sub,
      smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

theorem N06ScalarJetTwoBound.oriented_center {f : ℝ → ℝ} {r ι u B : ℝ}
    (h : N06ScalarJetTwoBound f (ι * (u - r)) B) (hι : ι = 1 ∨ ι = -1) :
    N06ScalarJetTwoBound (fun t => f (ι * (t - r))) u B := by
  apply n06_scalarJetTwoBound_iff.mpr
  intro k hk
  rw [n06_abs_iteratedDeriv_oriented_center f r ι hι]
  exact n06_scalarJetTwoBound_iff.mp h k hk

theorem n06_airyPhysicalHeight_eq_radial
    (c w : ℝ → ℝ) (r ι u : ℝ) (hι : ι = 1 ∨ ι = -1) :
    n06AiryPhysicalHeight c w r ι u =
      n06AiryRadialHeight c (fun t => w (r + ι * t)) (ι * (u - r)) := by
  have hback : r + ι * (ι * (u - r)) = u := by
    rcases hι with rfl | rfl <;> ring
  simp only [n06AiryPhysicalHeight, n06AiryPhysicalSlope, n06AiryRadialHeight, hback]

theorem n06_airyPhysicalHeight_fun_eq_radial
    (c w : ℝ → ℝ) (r ι : ℝ) (hι : ι = 1 ∨ ι = -1) :
    n06AiryPhysicalHeight c w r ι =
      fun u => n06AiryRadialHeight c (fun t => w (r + ι * t)) (ι * (u - r)) :=
  funext fun u => n06_airyPhysicalHeight_eq_radial c w r ι u hι

/-- The physical derivative of the raw root chart retains its orientation. -/
theorem n06_hasDerivAt_airyRootCoordinate {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hp : ∀ x : ℝ, 0 < n06AiryAverage c x)
    (r ι u : ℝ) :
    HasDerivAt (n06AiryRootCoordinate c r ι)
      (ι * n06AiryPhysicalSlope c r ι u) u := by
  have hi : HasDerivAt (fun t : ℝ => ι * (t - r)) ι u := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id u).sub_const r).const_mul ι
  have h := (n06_hasDerivAt_airyRadialCoordinate hc (ι * (u - r)) (hp _)).comp u hi
  convert h using 1
  · rfl
  · dsimp only [n06AiryPhysicalSlope]
    ring

/-- The second orientation in the positive endpoint coordinate cancels
the raw chart orientation. This coordinate is increasing at both endpoints. -/
theorem n06_hasDerivAt_airyEndpointCoordinate {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hp : ∀ x : ℝ, 0 < n06AiryAverage c x)
    (r ι v u : ℝ) (hι : ι = 1 ∨ ι = -1) :
    HasDerivAt (n06AiryEndpointCoordinate c r ι v)
      (n06AiryPhysicalSlope c r ι u) u := by
  have hunit : ι * ι = 1 := by rcases hι with rfl | rfl <;> norm_num
  have h := ((n06_hasDerivAt_airyRootCoordinate hc hp r ι u).const_mul ι).const_add v
  convert h using 1
  · rfl
  · rw [← mul_assoc, hunit, one_mul]

@[simp] theorem n06_airyEndpointCoordinate_at_root (c : ℝ → ℝ) (r ι v : ℝ) :
    n06AiryEndpointCoordinate c r ι v r = v := by
  simp only [n06AiryEndpointCoordinate, n06AiryRootCoordinate, sub_self,
    mul_zero, n06_airyRadialCoordinate_zero, add_zero]

theorem n06_contDiff_airyPhysicalSlope {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hp : ∀ x : ℝ, 0 < n06AiryAverage c x) (r ι : ℝ) :
    ContDiff ℝ ∞ (n06AiryPhysicalSlope c r ι) :=
  (n06_contDiff_airyRadialSlope hc hp).comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))

/-- The positive physical slope is the absolute Jacobian of the raw chart. -/
theorem n06_abs_deriv_airyRootCoordinate {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hp : ∀ x : ℝ, 0 < n06AiryAverage c x)
    (r ι u : ℝ) (hι : ι = 1 ∨ ι = -1)
    (hs : 0 < n06AiryPhysicalSlope c r ι u) :
    |deriv (n06AiryRootCoordinate c r ι) u| = n06AiryPhysicalSlope c r ι u := by
  have hιabs : |ι| = 1 := by rcases hι with rfl | rfl <;> norm_num
  rw [(n06_hasDerivAt_airyRootCoordinate hc hp r ι u).deriv,
    abs_mul, hιabs, one_mul, abs_of_pos hs]

/-- This is the actual physical height normalization, using the absolute
Jacobian of the raw root chart and the original physical profile. -/
theorem n06_airyPhysicalHeight_eq_normalization {c w : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hp : ∀ x : ℝ, 0 < n06AiryAverage c x)
    (r ι u : ℝ) (hι : ι = 1 ∨ ι = -1)
    (hw : 0 < w u) (hs : 0 < n06AiryPhysicalSlope c r ι u) :
    n06AiryPhysicalHeight c w r ι u =
      (Real.sqrt (w u * |deriv (n06AiryRootCoordinate c r ι) u|))⁻¹ := by
  rw [n06_abs_deriv_airyRootCoordinate hc hp r ι u hι hs]
  unfold n06AiryPhysicalHeight
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg (mul_pos hw hs).le, ← Real.sqrt_eq_rpow]

/-- The exact physical principal densities, with the true absolute
Jacobian, follow from the same divided profile and the same extension. -/
theorem n06_airyPhysical_principal_normal_form
    {w g : ℝ → ℝ} {r ι δ u : ℝ} (hι : ι = 1 ∨ ι = -1)
    (hδ : 0 < δ) (huδ : |u - r| ≤ δ / 4)
    (hu : 0 < u) (hw : 0 < w u) (hg : 0 < g (ι * (u - r)))
    (hdivide : -deriv w u = (ι * (u - r)) * g (ι * (u - r)))
    (hext : ContDiff ℝ ∞
      (n06RootSpeedExtension δ (referenceRootSpeedFactor w g r ι)))
    (havg : ∀ x : ℝ, 0 < n06AiryAverage
      (n06RootSpeedExtension δ (referenceRootSpeedFactor w g r ι)) x) :
    let c := n06RootSpeedExtension δ (referenceRootSpeedFactor w g r ι)
    let H := n06AiryPhysicalHeight c w r ι
    let J := |deriv (n06AiryRootCoordinate c r ι) u|
    0 < J ∧ H u ^ 2 * w u * J = 1 ∧
      H u ^ 2 * (deriv w u / u) / J = -n06AiryRootCoordinate c r ι u := by
  let c := n06RootSpeedExtension δ (referenceRootSpeedFactor w g r ι)
  have hback : r + ι * (ι * (u - r)) = u := by
    rcases hι with rfl | rfl <;> ring
  have hιabs : |ι| = 1 := by rcases hι with rfl | rfl <;> norm_num
  have hx : |ι * (u - r)| ≤ δ / 4 := by
    rw [abs_mul, hιabs, one_mul]
    exact huδ
  have hn := n06_airyRoot_principal_normal_form hδ hx
    (by simpa only [hback] using hu) (by simpa only [hback] using hw) hg
    (by simpa only [hback] using hdivide) hext havg
  change 0 < deriv (n06AiryRadialCoordinate c) (ι * (u - r)) ∧
    n06AiryRadialHeight c (fun t => w (r + ι * t)) (ι * (u - r)) ^ 2 *
      w (r + ι * (ι * (u - r))) * deriv (n06AiryRadialCoordinate c) (ι * (u - r)) = 1 ∧
    n06AiryRadialHeight c (fun t => w (r + ι * t)) (ι * (u - r)) ^ 2 *
      (deriv w (r + ι * (ι * (u - r))) / (r + ι * (ι * (u - r)))) /
        deriv (n06AiryRadialCoordinate c) (ι * (u - r)) =
          -n06AiryRadialCoordinate c (ι * (u - r)) at hn
  rw [n06_deriv_airyRadialCoordinate hext havg, hback,
    ← n06_airyPhysicalHeight_eq_radial c w r ι u hι] at hn
  have hs : 0 < n06AiryPhysicalSlope c r ι u := hn.1
  change 0 < |deriv (n06AiryRootCoordinate c r ι) u| ∧
    n06AiryPhysicalHeight c w r ι u ^ 2 * w u *
      |deriv (n06AiryRootCoordinate c r ι) u| = 1 ∧
    n06AiryPhysicalHeight c w r ι u ^ 2 * (deriv w u / u) /
      |deriv (n06AiryRootCoordinate c r ι) u| = -n06AiryRootCoordinate c r ι u
  rw [n06_abs_deriv_airyRootCoordinate hext havg r ι u hι hs]
  exact hn

end ContinuousFlexibility.Analysis
