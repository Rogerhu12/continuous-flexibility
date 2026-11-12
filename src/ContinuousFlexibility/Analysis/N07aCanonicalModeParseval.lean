import ContinuousFlexibility.Analysis.N07aAngularEvenRepresentative
import ContinuousFlexibility.Analysis.N07aAngularRadialParseval
import ContinuousFlexibility.Analysis.N07aCanonicalUnitModes
import ContinuousFlexibility.Analysis.N07aPeriodicRadialPairing

/-!
# Partial Parseval for the actual canonical L² classes

The true cosine coefficients of a reflection-fixed canonical class form
an exact radial L² Parseval series. The normalization includes both the
canonical half period and the affine radial interval length.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aCanonicalRadialMode_norm_sq (u : CanonicalL2 S K m) (n : ℕ) :
    ‖n07aCanonicalRadialMode u n‖ ^ 2 =
      ∫ r in Ioo (K.left m) (K.right m), n07aHalfRadialCoefficient u n r ^ 2 :=
  reference_memLp_norm_sq_eq_integral (n07aCanonicalRadialCoefficient_memLp u n)

theorem n07aCanonicalRadialMode_hasSum (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (hu : n07aAngularReflection m u = u) :
    HasSum (fun n : ℕ => ‖n07aCanonicalRadialMode u n‖ ^ 2) (Real.pi⁻¹ * ‖u‖ ^ 2) := by
  let μ := volume.restrict (Ioo (K.left m) (K.right m))
  let f : PolarPoint → ℝ := u
  let g := n07aAngularEvenRepresentative f
  have hg : g =ᵐ[canonicalMeasure S K m] f := n07aCanonicalEvenRepresentative_ae u hu
  have hgprod : g =ᵐ[μ.prod angleMeasure] f := by
    simpa only [μ, n07aCanonicalMeasure_eq_prod] using hg
  have hgLp : MemLp g 2 (μ.prod angleMeasure) := by
    have hhalf : MemLp g 2 (canonicalMeasure S K m) := (memLp_congr_ae hg).mpr (Lp.memLp u)
    simpa only [μ, n07aCanonicalMeasure_eq_prod] using hhalf
  have hfull := n07aCanonicalEvenRepresentative_memLp u hu
  have hp : ∀ᵐ r ∂μ, Function.Periodic (fun θ => g (r, θ)) Real.pi :=
    Eventually.of_forall (n07aAngularEvenRepresentative_periodic f)
  have he : ∀ᵐ r ∂μ, Function.Even (fun θ => g (r, θ)) :=
    Eventually.of_forall (n07aAngularEvenRepresentative_even f)
  have hcoeff (n : ℕ) : n07aHalfRadialCoefficient f n =ᵐ[μ] referenceRadialCoefficient g n := by
    filter_upwards [Measure.ae_ae_of_ae_prod hgprod, memLp_two_prod_sections hfull] with r hr hri
    have hhalf : n07aHalfRadialCoefficient f n r = n07aHalfRadialCoefficient g n r := by
      unfold n07aHalfRadialCoefficient
      congr 1
      apply integral_congr_ae
      exact hr.mono fun θ hθ => congrArg (· * referenceAngularBasis n θ) hθ.symm
    refine hhalf.trans (n07aHalfRadialCoefficient_eq_reference n r
      (n07aAngularEvenRepresentative_periodic f r) ?_)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr
      (hri.integrable (by norm_num))
  have hterms : (fun n : ℕ => ‖n07aCanonicalRadialMode u n‖ ^ 2) =
      fun n => ∫ r, referenceRadialCoefficient g n r ^ 2 ∂μ := by
    funext n
    rw [n07aCanonicalRadialMode_norm_sq]
    exact integral_congr_ae ((hcoeff n).mono fun r hr => congrArg (· ^ 2) hr)
  have hvalue : (2 * Real.pi)⁻¹ *
      ∫ p, g p ^ 2 ∂μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) =
        Real.pi⁻¹ * ‖u‖ ^ 2 := by
    have hfullSq : Integrable (fun p => g p ^ 2)
        (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := hfull.integrable_sq
    have hline : (∫ r in K.left m..K.right m, radialAngularMean (fun θ => g (r, θ) ^ 2)) =
        ∫ r, radialAngularMean (fun θ => g (r, θ) ^ 2) ∂μ := by
      change _ = ∫ r in Ioo (K.left m) (K.right m), radialAngularMean (fun θ => g (r, θ) ^ 2)
      rw [intervalIntegral.integral_of_le hm.le, restrict_Ioo_eq_restrict_Ioc]
    calc
      _ = ∫ r, radialAngularMean (fun θ => g (r, θ) ^ 2) ∂μ := by
        simp only [radialAngularMean,
          intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
        rw [integral_const_mul, ← integral_prod _ hfullSq]
      _ = ∫ r in K.left m..K.right m, radialAngularMean (fun θ => g (r, θ) ^ 2) := hline.symm
      _ = Real.pi⁻¹ * ∫ p, g p ^ 2 ∂μ.prod angleMeasure :=
        n07a_periodic_radial_mean_eq_half hm.le hgLp.integrable_sq
          (hp.mono fun r hpr => fun θ => congrArg (fun x : ℝ => x ^ 2) (hpr θ))
      _ = Real.pi⁻¹ * ‖u‖ ^ 2 := by
        congr 1
        have hnorm : ‖u‖ ^ 2 = ∫ p, f p ^ 2 ∂canonicalMeasure S K m := by
          simpa only [Lp.toLp_coeFn] using reference_memLp_norm_sq_eq_integral (Lp.memLp u)
        rw [hnorm, n07aCanonicalMeasure_eq_prod]
        exact integral_congr_ae (hgprod.mono fun p hp => congrArg (· ^ 2) hp)
  rw [hterms, ← hvalue]
  exact n07a_hasSum_integral_radialCoefficient_sq hfull hp he

theorem n07aCanonicalUnitMode_hasSum (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (hu : n07aAngularReflection m u = u) :
    HasSum (fun n : ℕ => ‖n07aCanonicalUnitMode hm u n‖ ^ 2)
      ((K.right m - K.left m)⁻¹ * (Real.pi⁻¹ * ‖u‖ ^ 2)) := by
  simpa only [n07aCanonicalUnitMode_norm_sq] using
    (n07aCanonicalRadialMode_hasSum hm u hu).mul_left (K.right m - K.left m)⁻¹

end ContinuousFlexibility.Analysis
