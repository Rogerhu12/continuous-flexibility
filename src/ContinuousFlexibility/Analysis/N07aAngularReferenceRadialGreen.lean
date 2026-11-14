module

public import ContinuousFlexibility.Analysis.N07aAngularReferenceFlux
public import ContinuousFlexibility.Analysis.IntervalWeakDivergence
public import ContinuousFlexibility.Radial.R11bRadialTests

/-!
# Compact-test Green identity for the genuine right flux

An interior compact test is localized to one finite closed subinterval.
FTC2 only needs the actual continuous flux and its integrable right
derivative there. Thus interfaces with unequal second normal derivatives
produce no unproved integration-by-parts boundary term.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped Topology ContDiff

theorem n07a_radial_green_compact_of_right_flux
    {a b : ℝ} (hab : a < b) {w u ur g φ : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b)
    (hu : ContinuousOn u (Ioo a b)) (hur : ContinuousOn ur (Ioo a b))
    (hdu : ∀ r ∈ Ioo a b, HasDerivAt u (ur r) r)
    (hdq : ∀ r ∈ Ioo a b, HasDerivWithinAt (fun s => w s * ur s) (g r) (Ioi r) r)
    (hg : IntervalIntegrable g volume a b) :
    (∫ r in a..b, u r * deriv (fun s => w s * deriv φ s) r) =
      ∫ r in a..b, g r * φ r := by
  obtain ⟨l, h, hal, hlh, hhb, hsupport⟩ :=
    exists_inner_interval_of_isCompact_subset_Ioo hab hφc hφs
  have hsub : uIcc l h ⊆ Ioo a b := by
    rw [uIcc_of_le hlh.le]
    exact fun _ hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hhb⟩
  have hφl : φ l = 0 := image_eq_zero_of_notMem_tsupport
    (fun hl => (lt_irrefl l) (hsupport hl).1)
  have hφh : φ h = 0 := image_eq_zero_of_notMem_tsupport
    (fun hh => (lt_irrefl h) (hsupport hh).2)
  have hφl' : deriv φ l = 0 := image_eq_zero_of_notMem_tsupport
    (fun hl => (lt_irrefl l) (hsupport (tsupport_deriv_subset hl)).1)
  have hφh' : deriv φ h = 0 := image_eq_zero_of_notMem_tsupport
    (fun hh => (lt_irrefl h) (hsupport (tsupport_deriv_subset hh)).2)
  have hgi : IntervalIntegrable g volume l h := hg.mono_set (by
    rw [uIcc_of_le hab.le]
    exact fun r hr => Ioo_subset_Icc_self (hsub hr))
  have hgreen := n07a_radial_green_of_right_flux hw hφ (hu.mono hsub)
    ((hw.continuous.continuousOn.mul hur).mono hsub)
    (fun r hr => hdu r (hsub (Ioo_subset_Icc_self hr)))
    (fun r hr => hdq r (hsub (Ioo_subset_Icc_self hr)))
    (hur.mono hsub).intervalIntegrable hgi hφl hφh hφl' hφh'
  have hsleft : Function.support (fun r => u r * deriv (fun s => w s * deriv φ s) r)
      ⊆ tsupport φ :=
    (Function.support_mul_subset_right _ _).trans
      (support_deriv_subset.trans (tsupport_mul_subset_right.trans tsupport_deriv_subset))
  have hsright : Function.support (fun r => g r * φ r) ⊆ tsupport φ :=
    (Function.support_mul_subset_right _ _).trans (subset_tsupport φ)
  rw [intervalIntegral.integral_eq_integral_of_support_subset
      (hsleft.trans (hφs.trans Ioo_subset_Ioc_self)),
    intervalIntegral.integral_eq_integral_of_support_subset
      (hsright.trans (hφs.trans Ioo_subset_Ioc_self))]
  rwa [intervalIntegral.integral_eq_integral_of_support_subset
      (hsleft.trans (hsupport.trans Ioo_subset_Ioc_self)),
    intervalIntegral.integral_eq_integral_of_support_subset
      (hsright.trans (hsupport.trans Ioo_subset_Ioc_self))] at hgreen

theorem n07a_radialTest_slice {D : ReferenceData} {φ : PolarPoint → ℝ}
    (hφ : RadialTest D φ) (θ : ℝ) :
    ContDiff ℝ ∞ (fun r => φ (r, θ)) ∧
    HasCompactSupport (fun r => φ (r, θ)) ∧
    tsupport (fun r => φ (r, θ)) ⊆ radialCore D := by
  obtain ⟨K, hK, hKD, hzero⟩ := hφ.2.2
  have hs : tsupport (fun r => φ (r, θ)) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro r hr
    by_contra hrK
    exact hr (hzero r hrK θ)
  exact ⟨hφ.1.comp (contDiff_id.prodMk contDiff_const),
    hK.of_isClosed_subset isClosed_closure hs, hs.trans hKD⟩

/-- The radial part of every original two-period test satisfies the
actual reference Green identity at each integrable angular section. -/
theorem n07a_reference_radial_green_slice {D : ReferenceData}
    {v φ : PolarPoint → ℝ} (hab : D.a < D.b) (hw : EndpointFlat D D.w)
    (hv : ContDiffOn ℝ 1 v (annularOpen D))
    (hright : ∀ p ∈ annularOpen D, ∃ u : PolarPoint → ℝ,
      ContDiffAt ℝ ∞ u p ∧ ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → v q = u q)
    (hφ : RadialTest D φ) (θ : ℝ)
    (hg : IntervalIntegrable (fun r => n07aReferenceRightFluxDerivative D v (r, θ))
      volume D.a D.b) :
    (∫ r in D.a..D.b, v (r, θ) *
      deriv (fun s => D.w s * deriv (fun t => φ (t, θ)) s) r) =
      ∫ r in D.a..D.b, n07aReferenceRightFluxDerivative D v (r, θ) * φ (r, θ) := by
  have hpath : Continuous (fun r : ℝ => (r, θ)) := continuous_id.prodMk continuous_const
  have hm : MapsTo (fun r : ℝ => (r, θ)) (radialCore D) (annularOpen D) :=
    fun _ hr => ⟨hr, mem_univ _⟩
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hdf : ContinuousOn (fderiv ℝ v) (annularOpen D) :=
    hv.continuousOn_fderiv_of_isOpen hopen le_rfl
  obtain ⟨hφs, hφc, hφsupp⟩ := n07a_radialTest_slice hφ θ
  exact n07a_radial_green_compact_of_right_flux hab hw.1 hφs hφc hφsupp
    (hv.continuousOn.comp hpath.continuousOn hm)
    ((hdf.clm_apply continuousOn_const).comp hpath.continuousOn hm)
    (fun r hr => hasDerivAt_radialSlice
      ((hv.contDiffAt (hopen.mem_nhds (hm hr))).differentiableAt one_ne_zero))
    (fun r hr => n07a_referenceNormalFlux_hasDerivWithinAt_right
      (hw.1.differentiable (by simp) r) hv (hm hr) (hright (r, θ) (hm hr))) hg

end ContinuousFlexibility.Analysis
