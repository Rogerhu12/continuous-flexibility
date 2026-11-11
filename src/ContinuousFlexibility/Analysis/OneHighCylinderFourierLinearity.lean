import ContinuousFlexibility.Analysis.OneHighCylinderPlancherel
import ContinuousFlexibility.Analysis.OneHighCircleFourierProduct

/-!
# Linearity of the actual mixed Fourier transform

The physical transform is linear as an almost-everywhere frequency function.
This follows from the actual angular coefficient functional and the radial
L2 Fourier map. In particular, Plancherel applies to differences without
assuming physical or frequency L1 integrability.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal FourierTransform

variable {P : ℝ} [Fact (0 < P)]

theorem cylinderAngularCoefficient_sub (f g : ℝ × AddCircle P → ℂ)
    (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    cylinderAngularCoefficient (fun p => f p - g p) n =
      fun r => cylinderAngularCoefficient f n r - cylinderAngularCoefficient g n r := by
  funext r
  let fr : C(AddCircle P, ℂ) :=
    ⟨fun θ => f (r, θ), hf.comp (continuous_const.prodMk continuous_id)⟩
  let gr : C(AddCircle P, ℂ) :=
    ⟨fun θ => g (r, θ), hg.comp (continuous_const.prodMk continuous_id)⟩
  simpa only [circleFourierCoeffCLM_apply, ContinuousMap.coe_sub, Pi.sub_apply] using
    (circleFourierCoeffCLM (P := P) n).map_sub fr gr

theorem cylinderFourierMode_sub (f g : ℝ × AddCircle P → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hg2 : MemLp g 2 (cylinderPhysicalMeasure P)) (n : ℤ) :
    cylinderFourierMode (fun p => f p - g p) (hf.sub hg) (hf2.sub hg2) n =
      cylinderFourierMode f hf hf2 n - cylinderFourierMode g hg hg2 n := by
  have hsub := cylinderAngularCoefficient_memLp (hf.sub hg) (hf2.sub hg2) n
  have hfc := cylinderAngularCoefficient_memLp hf hf2 n
  have hgc := cylinderAngularCoefficient_memLp hg hg2 n
  have hl : hsub.toLp (cylinderAngularCoefficient (fun p => f p - g p) n) =
      hfc.toLp (cylinderAngularCoefficient f n) -
        hgc.toLp (cylinderAngularCoefficient g n) := by
    apply Lp.ext
    filter_upwards [hsub.coeFn_toLp, hfc.coeFn_toLp, hgc.coeFn_toLp,
      Lp.coeFn_sub (hfc.toLp (cylinderAngularCoefficient f n))
        (hgc.toLp (cylinderAngularCoefficient g n))] with r hsr hfr hgr hdiff
    rw [hsr, hdiff]
    simp only [Pi.sub_apply, hfr, hgr]
    exact congrFun (cylinderAngularCoefficient_sub f g hf hg n) r
  unfold cylinderFourierMode
  rw [hl]
  simp only [sub_eq_add_neg, FourierTransform.fourier_add, FourierTransform.fourier_neg]

theorem cylinderFourier_sub_ae (f g : ℝ × AddCircle P → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hg2 : MemLp g 2 (cylinderPhysicalMeasure P)) :
    cylinderFourier (fun p => f p - g p) (hf.sub hg) (hf2.sub hg2) =ᵐ[cylinderFrequencyMeasure]
      fun ζ => cylinderFourier f hf hf2 ζ - cylinderFourier g hg hg2 ζ := by
  have hmode (n : ℤ) :
      (cylinderFourierMode (fun p => f p - g p) (hf.sub hg) (hf2.sub hg2) n : ℝ → ℂ) =ᵐ[volume]
        fun ξ => cylinderFourierMode f hf hf2 n ξ - cylinderFourierMode g hg hg2 n ξ := by
    rw [cylinderFourierMode_sub f g hf hg hf2 hg2 n]
    exact Lp.coeFn_sub _ _
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_cylinderFourier _ (hf.sub hg) (hf2.sub hg2))
    ((measurable_cylinderFourier f hf hf2).sub
      (measurable_cylinderFourier g hg hg2)))).mpr
  have hall : ∀ᵐ ξ : ℝ ∂volume, ∀ n : ℤ,
      cylinderFourierMode (fun p => f p - g p) (hf.sub hg) (hf2.sub hg2) n ξ =
        cylinderFourierMode f hf hf2 n ξ - cylinderFourierMode g hg hg2 n ξ :=
    ae_all_iff.mpr hmode
  filter_upwards [hall] with ξ hξ
  exact Eventually.of_forall hξ

theorem cylinderFourier_sub_eLpNorm_two (f g : ℝ × AddCircle P → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hg2 : MemLp g 2 (cylinderPhysicalMeasure P)) :
    eLpNorm (fun p => f p - g p) 2 (cylinderPhysicalMeasure P) =
      eLpNorm (fun ζ => cylinderFourier f hf hf2 ζ - cylinderFourier g hg hg2 ζ)
        2 cylinderFrequencyMeasure := by
  rw [← cylinderFourier_eLpNorm_two _ (hf.sub hg) (hf2.sub hg2)]
  exact eLpNorm_congr_ae (cylinderFourier_sub_ae f g hf hg hf2 hg2)

end ContinuousFlexibility.Analysis
