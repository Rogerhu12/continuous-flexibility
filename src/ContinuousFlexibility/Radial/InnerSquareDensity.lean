import ContinuousFlexibility.Radial.InnerRadialL2Mass
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# The exact square-density isometry in real L²

Multiplication by a measurable, almost everywhere nonzero amplitude
changes a square-density measure into the base measure. No boundedness
of the amplitude or its reciprocal is required for this isometry.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (A : α → ℝ) (hA : Measurable A) (hne : ∀ᵐ x ∂μ, A x ≠ 0)

include hA hne

theorem innerSquareDensity_base_ac :
    μ ≪ μ.withDensity (fun x => ENNReal.ofReal (A x ^ 2)) := by
  apply withDensity_absolutelyContinuous' (hA.pow_const 2).ennreal_ofReal.aemeasurable
  filter_upwards [hne] with x hx
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hx))

theorem innerSquareDensity_memLp_iff (f : α → ℝ) :
    MemLp f 2 (μ.withDensity (fun x => ENNReal.ofReal (A x ^ 2))) ↔
      MemLp (fun x => A x * f x) 2 μ := by
  have hd : Measurable (fun x => ENNReal.ofReal (A x ^ 2)) :=
    (hA.pow_const 2).ennreal_ofReal
  have hfinite : ∀ᵐ x ∂μ, ENNReal.ofReal (A x ^ 2) < (∞ : ℝ≥0∞) := by simp
  constructor
  · intro hf
    have hfm := AEStronglyMeasurable.mono_ac (innerSquareDensity_base_ac μ A hA hne)
      hf.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq (hA.aestronglyMeasurable.mul hfm)).mpr
    have h := (integrable_withDensity_iff_integrable_smul' hd hfinite).mp hf.integrable_sq
    convert h using 1
    funext x
    rw [ENNReal.toReal_ofReal (sq_nonneg (A x))]
    simp only [smul_eq_mul]
    ring
  · intro hf
    have hfm : AEStronglyMeasurable f μ := by
      have h := hA.inv.aestronglyMeasurable.mul hf.aestronglyMeasurable
      apply h.congr
      filter_upwards [hne] with x hx
      exact inv_mul_cancel_left₀ hx (f x)
    have hfd := AEStronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous μ (fun x => ENNReal.ofReal (A x ^ 2))) hfm
    apply (memLp_two_iff_integrable_sq hfd).mpr
    apply (integrable_withDensity_iff_integrable_smul' hd hfinite).mpr
    convert hf.integrable_sq using 1
    funext x
    rw [ENNReal.toReal_ofReal (sq_nonneg (A x))]
    simp only [smul_eq_mul]
    ring

/-- The forward isometry acts on the existing Lp quotient. -/
def innerSquareDensityPullback :
    Lp ℝ 2 (μ.withDensity (fun x => ENNReal.ofReal (A x ^ 2))) →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toFun u := ((innerSquareDensity_memLp_iff μ A hA hne u).mp (Lp.memLp u)).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards
      [((innerSquareDensity_memLp_iff μ A hA hne
          ((u + v : Lp ℝ 2 (μ.withDensity (fun x => ENNReal.ofReal (A x ^ 2)))) :
            α → ℝ)).mp (Lp.memLp (u + v))).coeFn_toLp,
        ((innerSquareDensity_memLp_iff μ A hA hne u).mp (Lp.memLp u)).coeFn_toLp,
        ((innerSquareDensity_memLp_iff μ A hA hne v).mp (Lp.memLp v)).coeFn_toLp,
        Lp.coeFn_add
          (((innerSquareDensity_memLp_iff μ A hA hne u).mp (Lp.memLp u)).toLp _)
          (((innerSquareDensity_memLp_iff μ A hA hne v).mp (Lp.memLp v)).toLp _),
        (innerSquareDensity_base_ac μ A hA hne).ae_eq (Lp.coeFn_add u v)] with
          x hx hu hv hadd ha
    simp only [Pi.add_apply] at hadd ha
    rw [hx, hadd, hu, hv, ha]
    ring
  map_smul' c u := by
    apply Lp.ext
    filter_upwards
      [((innerSquareDensity_memLp_iff μ A hA hne
          ((c • u : Lp ℝ 2 (μ.withDensity (fun x => ENNReal.ofReal (A x ^ 2)))) :
            α → ℝ)).mp (Lp.memLp (c • u))).coeFn_toLp,
        ((innerSquareDensity_memLp_iff μ A hA hne u).mp (Lp.memLp u)).coeFn_toLp,
        Lp.coeFn_smul c
          (((innerSquareDensity_memLp_iff μ A hA hne u).mp (Lp.memLp u)).toLp _),
        (innerSquareDensity_base_ac μ A hA hne).ae_eq (Lp.coeFn_smul c u)] with
          x hx hu hsmul ha
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul ha
    simp only [RingHom.id_apply]
    rw [hx, hsmul, hu, ha]
    ring
  norm_map' u := by
    have ht : ‖((innerSquareDensity_memLp_iff μ A hA hne u).mp (Lp.memLp u)).toLp _‖ ^ 2 =
        ∫ x, (A x * u x) ^ 2 ∂μ := by
      rw [innerL2_norm_sq_eq_integral]
      apply integral_congr_ae
      filter_upwards [((innerSquareDensity_memLp_iff μ A hA hne u).mp
        (Lp.memLp u)).coeFn_toLp] with x hx
      rw [hx]
    have hu := innerL2_norm_sq_eq_integral
      (μ.withDensity (fun x => ENNReal.ofReal (A x ^ 2))) u
    rw [integral_withDensity_eq_integral_toReal_smul
      (hA.pow_const 2).ennreal_ofReal (by simp)] at hu
    have heq : (fun x => (ENNReal.ofReal (A x ^ 2)).toReal • u x ^ 2) =
        (fun x => (A x * u x) ^ 2) := by
      funext x
      rw [ENNReal.toReal_ofReal (sq_nonneg (A x))]
      simp only [smul_eq_mul]
      ring
    rw [heq] at hu
    nlinarith only [ht, hu, norm_nonneg u,
      norm_nonneg (((innerSquareDensity_memLp_iff μ A hA hne u).mp (Lp.memLp u)).toLp _)]

theorem innerSquareDensityPullback_ae
    (u : Lp ℝ 2 (μ.withDensity (fun x => ENNReal.ofReal (A x ^ 2)))) :
    (innerSquareDensityPullback μ A hA hne u : α → ℝ) =ᵐ[μ] (fun x => A x * u x) :=
  ((innerSquareDensity_memLp_iff μ A hA hne u).mp (Lp.memLp u)).coeFn_toLp

theorem innerSquareDensityPullback_surjective :
    Function.Surjective (innerSquareDensityPullback μ A hA hne) := by
  intro f
  have hprod : (fun x => A x * (f x / A x)) =ᵐ[μ] (f : α → ℝ) := by
    filter_upwards [hne] with x hx
    field_simp [hx]
  have hm : MemLp (fun x => f x / A x) 2
      (μ.withDensity (fun x => ENNReal.ofReal (A x ^ 2))) :=
    (innerSquareDensity_memLp_iff μ A hA hne _).mpr
      (MemLp.ae_eq hprod.symm (Lp.memLp f))
  refine ⟨hm.toLp _, ?_⟩
  apply Lp.ext
  filter_upwards [innerSquareDensityPullback_ae μ A hA hne (hm.toLp _),
    (innerSquareDensity_base_ac μ A hA hne).ae_eq hm.coeFn_toLp, hne] with x hx hu hn
  rw [hx, hu]
  field_simp [hn]

def innerSquareDensityEquiv :
    Lp ℝ 2 (μ.withDensity (fun x => ENNReal.ofReal (A x ^ 2))) ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (innerSquareDensityPullback μ A hA hne)
    (innerSquareDensityPullback_surjective μ A hA hne)

theorem innerSquareDensityEquiv_ae
    (u : Lp ℝ 2 (μ.withDensity (fun x => ENNReal.ofReal (A x ^ 2)))) :
    (innerSquareDensityEquiv μ A hA hne u : α → ℝ) =ᵐ[μ] (fun x => A x * u x) := by
  unfold innerSquareDensityEquiv
  rw [LinearIsometryEquiv.coe_ofSurjective]
  exact innerSquareDensityPullback_ae μ A hA hne u

theorem innerSquareDensityEquiv_symm_ae (f : Lp ℝ 2 μ) :
    ((innerSquareDensityEquiv μ A hA hne).symm f : α → ℝ) =ᵐ[μ]
      (fun x => f x / A x) := by
  have h := innerSquareDensityEquiv_ae μ A hA hne
    ((innerSquareDensityEquiv μ A hA hne).symm f)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  filter_upwards [h, hne] with x hx hn
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using hx.symm

end ContinuousFlexibility.Radial
