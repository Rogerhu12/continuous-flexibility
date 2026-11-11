import ContinuousFlexibility.Analysis.N07aAngularBoundaryInverse
import ContinuousFlexibility.Analysis.N07aAngularInterfaceJets

/-!
# Aligned actual chart derivatives determine one transport derivative

Only the forward normal coordinate is translated or reversed. This
linear algebra identifies the derivatives of the two true inverse germs
after reference pullback, including the normal covector needed by the
height jump cancellation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements CanonicalGeometry

def n07aNormalAlignment (s : ℝ) : PolarPoint →L[ℝ] PolarPoint :=
  (s • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem n07aNormalAlignment_apply (s : ℝ) (v : PolarPoint) :
    n07aNormalAlignment s v = (s * v.1, v.2) := by
  simp only [n07aNormalAlignment, ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]

theorem n07aNormalAlignment_injective {s : ℝ} (hs : s ≠ 0) :
    Function.Injective (n07aNormalAlignment s) := by
  intro p q h
  rw [n07aNormalAlignment_apply, n07aNormalAlignment_apply] at h
  apply Prod.ext
  · exact mul_left_cancel₀ hs (congrArg Prod.fst h)
  · have h₂ := congrArg (fun v : PolarPoint => v.2) h
    exact h₂

theorem n07a_endpointAlignedChart_hasFDerivAt {S : PhysicalSpacesData}
    {K : CanonicalData S} {z : AnnularState S × ℝ} {m : ℕ} {p : PolarPoint}
    (h : DifferentiableAt ℝ (K.chart z m) p) (endpoint orientation : ℝ) :
    HasFDerivAt (endpointAlignedChart K z m endpoint orientation)
      ((n07aNormalAlignment orientation).comp (fderiv ℝ (K.chart z m) p)) p := by
  have hd := ((h.hasFDerivAt.fst.sub_const endpoint).const_mul orientation).prodMk
    h.hasFDerivAt.snd
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.prod_apply, smul_apply, ContinuousLinearMap.comp_apply,
    n07aNormalAlignment_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul]

theorem n07a_endpointAlignedChart_injective {S : PhysicalSpacesData}
    {K : CanonicalData S} {z z' : AnnularState S × ℝ} {m : ℕ}
    {p q : PolarPoint} {endpoint orientation : ℝ} (hs : orientation ≠ 0)
    (he : endpointAlignedChart K z m endpoint orientation p =
      endpointAlignedChart K z' m endpoint orientation q) :
    K.chart z m p = K.chart z' m q := by
  apply Prod.ext
  · have h := congrArg Prod.fst he
    change orientation * ((K.chart z m p).1 - endpoint) =
      orientation * ((K.chart z' m q).1 - endpoint) at h
    exact sub_left_inj.mp (mul_left_cancel₀ hs h)
  · have h₂ := congrArg (fun v : PolarPoint => v.2) he
    exact h₂

theorem n07a_aligned_inverse_transport_derivative
    (A₀ A₁ R₀ R₁ : PolarPoint →L[ℝ] PolarPoint)
    (B₀ B₁ : PolarPoint ≃L[ℝ] PolarPoint) {s₀ s₁ : ℝ}
    (hs₀ : s₀ ≠ 0)
    (hA₀ : A₀ = (B₀ : PolarPoint →L[ℝ] PolarPoint))
    (hA₁ : A₁ = (B₁ : PolarPoint →L[ℝ] PolarPoint))
    (hA : (n07aNormalAlignment s₀).comp A₀ = (n07aNormalAlignment s₁).comp A₁)
    (hR : (n07aNormalAlignment s₀).comp R₀ = (n07aNormalAlignment s₁).comp R₁) :
    (B₀.symm : PolarPoint →L[ℝ] PolarPoint).comp R₀ =
      (B₁.symm : PolarPoint →L[ℝ] PolarPoint).comp R₁ := by
  apply ContinuousLinearMap.ext
  intro v
  apply B₀.injective
  apply n07aNormalAlignment_injective hs₀
  have hAv := congrArg (fun A : PolarPoint →L[ℝ] PolarPoint => A (B₁.symm (R₁ v))) hA
  have hRv := congrArg (fun A : PolarPoint →L[ℝ] PolarPoint => A v) hR
  simp only [hA₀, hA₁, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hAv hRv
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using hRv.trans hAv.symm

/-- The first raw coordinate covector pulls back exactly under its true
inverse transport; there is no scale or sign error at a cut. -/
theorem n07a_inverse_transport_normal_covector
    (B : PolarPoint ≃L[ℝ] PolarPoint) (R : PolarPoint →L[ℝ] PolarPoint) :
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (B : PolarPoint →L[ℝ] PolarPoint)).comp
        ((B.symm : PolarPoint →L[ℝ] PolarPoint).comp R) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp R := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

end ContinuousFlexibility.Analysis
