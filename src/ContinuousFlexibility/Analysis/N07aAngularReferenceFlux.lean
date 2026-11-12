import ContinuousFlexibility.Analysis.N07aAngularFirstJetGluing
import ContinuousFlexibility.Analysis.N07aAngularReferenceSource
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The true reference flux has a right derivative at every interface

A C¹ field which has an actual smooth representative on the closed right
side has the same radial first derivative there. Consequently its actual
reference flux has a genuine right derivative at every radius, including
the roots and middle cuts. This is the derivative used by FTC2; no global
second normal derivative is postulated.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology ContDiff

def n07aReferenceNormalFlux (D : ReferenceData) (v : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  D.w p.1 * radialPartial v p

def n07aReferenceRightFluxDerivative (D : ReferenceData) (v : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  derivWithin (fun r => n07aReferenceNormalFlux D v (r, p.2)) (Ioi p.1) p.1

theorem n07a_referenceRightFluxDerivative_measurable_slice
    (D : ReferenceData) (v : PolarPoint → ℝ) (θ : ℝ) :
    Measurable (fun r => n07aReferenceRightFluxDerivative D v (r, θ)) :=
  measurable_derivWithin_Ioi (fun r => n07aReferenceNormalFlux D v (r, θ))

theorem n07a_referenceRightFluxDerivative_eq {D : ReferenceData}
    {v : PolarPoint → ℝ} {p : PolarPoint}
    (hw : DifferentiableAt ℝ D.w p.1) (hv : ContDiffAt ℝ ∞ v p) :
    n07aReferenceRightFluxDerivative D v p =
      deriv D.w p.1 * radialPartial v p + D.w p.1 * radialPartial (radialPartial v) p := by
  have hvr := (contDiffAt_radialPartial hv (m := 1) (by simp)).differentiableAt one_ne_zero
  have h := hw.hasDerivAt.mul (Radial.hasDerivAt_radialSlice hvr)
  exact h.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi p.1)

/-- Restricting a genuine closed-side germ to the interface circle gives
all actual angular derivatives, even where the normal second derivative
of the globally glued field may jump. -/
theorem n07a_reference_circle_contDiff {D : ReferenceData} {v : PolarPoint → ℝ}
    (hright : ∀ p ∈ annularOpen D, ∃ u : PolarPoint → ℝ,
      ContDiffAt ℝ ∞ u p ∧ ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → v q = u q)
    {r : ℝ} (hr : r ∈ radialCore D) :
    ContDiff ℝ ∞ (fun θ => v (r, θ)) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  obtain ⟨u, hu, he⟩ := hright (r, θ) ⟨hr, mem_univ _⟩
  have hpath : Tendsto (fun t : ℝ => (r, t)) (𝓝 θ) (𝓝 (r, θ)) :=
    (continuous_const.prodMk continuous_id).continuousAt.tendsto
  apply (hu.comp θ (contDiffAt_const.prodMk contDiffAt_id)).congr_of_eventuallyEq
  filter_upwards [hpath.eventually he] with t ht
  exact ht le_rfl

theorem n07a_referenceNormalFlux_hasDerivWithinAt_right {D : ReferenceData}
    {v : PolarPoint → ℝ} {p : PolarPoint}
    (hw : DifferentiableAt ℝ D.w p.1)
    (hv : ContDiffOn ℝ 1 v (annularOpen D)) (hp : p ∈ annularOpen D)
    (hright : ∃ u : PolarPoint → ℝ, ContDiffAt ℝ ∞ u p ∧
      ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → v q = u q) :
    HasDerivWithinAt (fun r => n07aReferenceNormalFlux D v (r, p.2))
      (n07aReferenceRightFluxDerivative D v p) (Ioi p.1) p.1 := by
  obtain ⟨u, hu, he⟩ := hright
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hvd : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ v q := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact (hv.contDiffAt (hopen.mem_nhds hq)).differentiableAt one_ne_zero
  have hu1 : ContDiffAt ℝ 1 u p := hu.of_le (by simp)
  have hud : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ u q :=
    (hu1.eventually (by simp)).mono fun _ hq => hq.differentiableAt one_ne_zero
  have hdf := n07a_fderiv_eventually_eq_on_set
    ((uniqueDiffOn_Ici p.1).prod uniqueDiffOn_univ) hvd hud
    (he.mono fun q hq hqs => hq hqs.1)
  have hflux : ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 →
      n07aReferenceNormalFlux D v q = n07aReferenceNormalFlux D u q := by
    filter_upwards [hdf] with q hq hqr
    have hd := congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0))
      (hq ⟨hqr, mem_univ _⟩)
    exact congrArg (D.w q.1 * ·) hd
  have hpath : Tendsto (fun r : ℝ => (r, p.2)) (𝓝 p.1) (𝓝 p) :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto
  have hpathflux := hpath.eventually hflux
  have hwithin : (fun r => n07aReferenceNormalFlux D v (r, p.2)) =ᶠ[𝓝[>] p.1]
      (fun r => n07aReferenceNormalFlux D u (r, p.2)) := by
    filter_upwards [hpathflux.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hr hrgt
    exact hr hrgt.le
  have hpoint : n07aReferenceNormalFlux D v p = n07aReferenceNormalFlux D u p :=
    hflux.self_of_nhds le_rfl
  have hur := (contDiffAt_radialPartial hu (m := 1) (by simp)).differentiableAt one_ne_zero
  have hd := hw.hasDerivAt.mul (Radial.hasDerivAt_radialSlice hur)
  have htransfer := hd.hasDerivWithinAt.congr_of_eventuallyEq hwithin hpoint
  exact htransfer.differentiableWithinAt.hasDerivWithinAt

/-- The radial Green identity uses the genuine one-sided flux derivative.
It needs no second derivative of the field at an interface. The actual
compact test will supply both endpoint zero conditions. -/
theorem n07a_radial_green_of_right_flux
    {a b : ℝ} {w u ur g φ : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hφ : ContDiff ℝ ∞ φ)
    (hu : ContinuousOn u (uIcc a b))
    (hq : ContinuousOn (fun r => w r * ur r) (uIcc a b))
    (hdu : ∀ r ∈ Ioo (min a b) (max a b), HasDerivAt u (ur r) r)
    (hdq : ∀ r ∈ Ioo (min a b) (max a b),
      HasDerivWithinAt (fun s => w s * ur s) (g r) (Ioi r) r)
    (hur : IntervalIntegrable ur volume a b) (hg : IntervalIntegrable g volume a b)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hφa' : deriv φ a = 0) (hφb' : deriv φ b = 0) :
    (∫ r in a..b, u r * deriv (fun s => w s * deriv φ s) r) =
      ∫ r in a..b, g r * φ r := by
  let q : ℝ → ℝ := fun r => w r * deriv φ r
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hqs : ContDiff ℝ ∞ q := hw.mul hφ'
  have hq' : Continuous (deriv q) := (contDiff_infty_iff_deriv.mp hqs).2.continuous
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu hqs.continuous.continuousOn hdu
    (fun r _ => (hqs.differentiable (by simp) r).hasDerivAt)
    hur (hq'.intervalIntegrable a b)
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hq hφ.continuous.continuousOn hdq
    (fun r _ => (hφ.differentiable (by simp) r).hasDerivAt.hasDerivWithinAt)
    hg (hφ'.continuous.intervalIntegrable a b)
  have hqa : q a = 0 := by dsimp only [q]; rw [hφa', mul_zero]
  have hqb : q b = 0 := by dsimp only [q]; rw [hφb', mul_zero]
  have hfirst' : (∫ r in a..b, u r * deriv q r) =
      -(∫ r in a..b, ur r * q r) := by
    simpa only [hqa, hqb, mul_zero, sub_self, zero_sub] using hfirst
  have hsecond' : (∫ r in a..b, (w r * ur r) * deriv φ r) =
      -(∫ r in a..b, g r * φ r) := by
    simpa only [hφa, hφb, mul_zero, sub_self, zero_sub] using hsecond
  have heq : (∫ r in a..b, ur r * q r) =
      ∫ r in a..b, (w r * ur r) * deriv φ r := by
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [q]
    ring
  calc
    _ = -(∫ r in a..b, ur r * q r) := hfirst'
    _ = ∫ r in a..b, g r * φ r := by rw [heq, hsecond', neg_neg]

end ContinuousFlexibility.Analysis
