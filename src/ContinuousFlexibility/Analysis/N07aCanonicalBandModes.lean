module

public import ContinuousFlexibility.Analysis.N07aCanonicalModeParseval
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalBand

/-!
# The actual cosine representative and norm of one canonical band

The Hilbert projection is identified with the true half-period cosine
coefficient. Its squared norm is exactly π times the radial mode norm,
including the constant mode. This is the local bridge from the weak mode
energy to the blocks of the original relative operator.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial

theorem n07aHalfRadialCoefficient_congr_ae {μ : Measure ℝ} [SFinite μ]
    {f g : PolarPoint → ℝ} (h : f =ᵐ[μ.prod angleMeasure] g) (n : ℕ) :
    n07aHalfRadialCoefficient f n =ᵐ[μ] n07aHalfRadialCoefficient g n := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with r hr
  unfold n07aHalfRadialCoefficient
  congr 1
  exact integral_congr_ae (hr.mono fun θ hθ => congrArg (· * referenceAngularBasis n θ) hθ)

theorem n07aHalfRadialCoefficient_mul_radial (a : ℝ → ℝ) (f : PolarPoint → ℝ)
    (n : ℕ) (r : ℝ) :
    n07aHalfRadialCoefficient (fun p => a p.1 * f p) n r =
      a r * n07aHalfRadialCoefficient f n r := by
  unfold n07aHalfRadialCoefficient
  simp only [mul_assoc, integral_const_mul]
  ring

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aCanonicalEvenRepresentative_coefficient (u : CanonicalL2 S K m)
    (hu : n07aAngularReflection m u = u) (n : ℕ) :
    n07aHalfRadialCoefficient u n =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))]
      referenceRadialCoefficient (n07aAngularEvenRepresentative u) n := by
  have he : (u : PolarPoint → ℝ) =ᵐ[
      (volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure]
      n07aAngularEvenRepresentative u := by
    simpa only [n07aCanonicalMeasure_eq_prod] using (n07aCanonicalEvenRepresentative_ae u hu).symm
  filter_upwards [n07aHalfRadialCoefficient_congr_ae he n,
    memLp_two_prod_sections (n07aCanonicalEvenRepresentative_memLp u hu)] with r hr hri
  refine hr.trans (n07aHalfRadialCoefficient_eq_reference n r
    (n07aAngularEvenRepresentative_periodic u r) ?_)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr
    (hri.integrable (by norm_num))

theorem n07aAngularBand_cosine_ae (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (hu : n07aAngularReflection m u = u) (n : ℕ) :
    (n07aAngularBand m hm n u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => n07aHalfRadialCoefficient u n p.1 * referenceAngularBasis n p.2 := by
  have hb := n07aAngularBand_eq_reference_of_periodic m hm
    (Eventually.of_forall (n07aAngularEvenRepresentative_periodic u))
    (Eventually.of_forall (n07aAngularEvenRepresentative_even u))
    (n07aCanonicalEvenRepresentative_ae u hu).symm n
  have hc := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (Ioo (K.left m) (K.right m))) (ν := angleMeasure)).ae
    (n07aCanonicalEvenRepresentative_coefficient u hu n)
  have hc' : ∀ᵐ p ∂canonicalMeasure S K m,
      n07aHalfRadialCoefficient u n p.1 =
        referenceRadialCoefficient (n07aAngularEvenRepresentative u) n p.1 := by
    simpa only [n07aCanonicalMeasure_eq_prod] using hc
  filter_upwards [hb, hc'] with p hp hcp
  rw [hp]
  simp only [referenceBasisProjection, angularBasisProjection, Finset.sum_singleton]
  change referenceRadialCoefficient (n07aAngularEvenRepresentative u) n p.1 *
    referenceAngularBasis n p.2 = _
  rw [← hcp]

theorem n07a_referenceAngularBasis_sq_integral (n : ℕ) :
    (∫ θ, referenceAngularBasis n θ ^ 2 ∂angleMeasure) = Real.pi := by
  have hp : Function.Periodic (fun θ => referenceAngularBasis n θ ^ 2) Real.pi :=
    fun θ => congrArg (fun x : ℝ => x ^ 2) (referenceAngularBasis_periodic n θ)
  have hi : IntervalIntegrable (fun θ => referenceAngularBasis n θ ^ 2) volume
      (0 : ℝ) (2 * Real.pi) :=
    ((contDiff_referenceAngularBasis n).continuous.pow 2).intervalIntegrable _ _
  have hmean : radialAngularMean (fun θ => referenceAngularBasis n θ ^ 2) = 1 := by
    simpa only [pow_two, ite_true] using referenceAngularBasis_pairing n n
  rw [radialAngularMean_eq_halfPeriod hp hi,
    intervalIntegral.integral_of_le Real.pi_pos.le] at hmean
  calc
    _ = Real.pi * (Real.pi⁻¹ * ∫ θ, referenceAngularBasis n θ ^ 2 ∂angleMeasure) := by
      rw [← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
    _ = Real.pi * 1 := congrArg (Real.pi * ·) hmean
    _ = _ := mul_one _

theorem n07aAngularBand_norm_sq_mode (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (hu : n07aAngularReflection m u = u) (n : ℕ) :
    ‖n07aAngularBand m hm n u‖ ^ 2 = Real.pi * ‖n07aCanonicalRadialMode u n‖ ^ 2 := by
  let v := n07aAngularBand m hm n u
  let f : PolarPoint → ℝ := fun p => n07aHalfRadialCoefficient u n p.1 * referenceAngularBasis n p.2
  have he : (v : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f := n07aAngularBand_cosine_ae hm u hu n
  have hf : MemLp f 2 (canonicalMeasure S K m) := (memLp_congr_ae he).mp (Lp.memLp v)
  have hn : ‖v‖ ^ 2 = ∫ p, f p ^ 2 ∂canonicalMeasure S K m := by
    have h := reference_memLp_norm_sq_eq_integral (Lp.memLp v)
    rw [Lp.toLp_coeFn] at h
    exact h.trans (integral_congr_ae (he.mono fun p hp => congrArg (· ^ 2) hp))
  rw [n07aCanonicalMeasure_eq_prod] at hf
  have hprod : (∫ p, f p ^ 2 ∂canonicalMeasure S K m) =
      ∫ r in Ioo (K.left m) (K.right m), ∫ θ, f (r, θ) ^ 2 ∂angleMeasure := by
    rw [n07aCanonicalMeasure_eq_prod, integral_prod _ hf.integrable_sq]
  rw [hn, hprod, n07aCanonicalRadialMode_norm_sq,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by
    simp only [f, mul_pow, integral_const_mul, n07a_referenceAngularBasis_sq_integral]
    ring

end ContinuousFlexibility.Analysis
