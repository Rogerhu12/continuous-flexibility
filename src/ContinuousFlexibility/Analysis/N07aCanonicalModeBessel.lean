module

public import ContinuousFlexibility.Analysis.N07aCanonicalModeParseval
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Bessel bounds for arbitrary actual canonical source classes

Only the angular variable is periodically extended. Finite cosine
projections are contractions on every radial section, so their actual
radial L² norms have a summable square bound without an evenness premise.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial

theorem n07aAngularPeriodicRepresentative_ae {μ : Measure ℝ} [SFinite μ]
    (u : PolarPoint → ℝ) :
    n07aAngularPeriodicRepresentative u =ᵐ[μ.prod angleMeasure] u := by
  have hθ : ∀ᵐ θ ∂angleMeasure, θ ∈ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem measurableSet_Ioc
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μ) (ν := angleMeasure)).ae hθ]
    with p hp
  have he : toIocMod Real.pi_pos 0 p.2 = p.2 :=
    (toIocMod_eq_self Real.pi_pos).mpr (by simpa only [zero_add] using hp)
  simp only [n07aAngularPeriodicRepresentative, he]

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aCanonicalRadialMode_sum_sq_le (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (I : Finset ℕ) :
    (∑ n ∈ I, ‖n07aCanonicalRadialMode u n‖ ^ 2) ≤ Real.pi⁻¹ * ‖u‖ ^ 2 := by
  let μ := volume.restrict (Ioo (K.left m) (K.right m))
  let f : PolarPoint → ℝ := u
  let g := n07aAngularPeriodicRepresentative f
  have hgprod : g =ᵐ[μ.prod angleMeasure] f := n07aAngularPeriodicRepresentative_ae f
  have hg : g =ᵐ[canonicalMeasure S K m] f := by
    simpa only [μ, n07aCanonicalMeasure_eq_prod] using hgprod
  have hgLp : MemLp g 2 (canonicalMeasure S K m) := (memLp_congr_ae hg).mpr (Lp.memLp u)
  have hgHalf : MemLp g 2 (μ.prod angleMeasure) := by
    simpa only [μ, n07aCanonicalMeasure_eq_prod] using hgLp
  have hp : ∀ᵐ r ∂μ, Function.Periodic (fun θ => g (r, θ)) Real.pi :=
    Eventually.of_forall (n07aAngularPeriodicRepresentative_periodic f)
  have hfull := n07aCanonical_memLp_full_of_periodic hgLp hp
  have hcoeff (n : ℕ) : n07aHalfRadialCoefficient f n =ᵐ[μ] referenceRadialCoefficient g n := by
    filter_upwards [Measure.ae_ae_of_ae_prod hgprod, memLp_two_prod_sections hfull] with r hr hri
    have he : n07aHalfRadialCoefficient f n r = n07aHalfRadialCoefficient g n r := by
      unfold n07aHalfRadialCoefficient
      congr 1
      exact integral_congr_ae (hr.mono fun θ hθ => congrArg (· * referenceAngularBasis n θ) hθ.symm)
    refine he.trans (n07aHalfRadialCoefficient_eq_reference n r
      (n07aAngularPeriodicRepresentative_periodic f r) ?_)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr
      (hri.integrable (by norm_num))
  have hterm (n : ℕ) : ‖n07aCanonicalRadialMode u n‖ ^ 2 =
      ∫ r, referenceRadialCoefficient g n r ^ 2 ∂μ := by
    rw [n07aCanonicalRadialMode_norm_sq]
    exact integral_congr_ae ((hcoeff n).mono fun r hr => congrArg (· ^ 2) hr)
  have hi (n : ℕ) : Integrable (fun r => referenceRadialCoefficient g n r ^ 2) μ :=
    (memLp_referenceRadialCoefficient_prod hfull n).integrable_sq
  have hline : (∫ r in K.left m..K.right m, radialAngularMean (fun θ => g (r, θ) ^ 2)) =
      ∫ r, radialAngularMean (fun θ => g (r, θ) ^ 2) ∂μ := by
    change _ = ∫ r in Ioo (K.left m) (K.right m), radialAngularMean (fun θ => g (r, θ) ^ 2)
    rw [intervalIntegral.integral_of_le hm.le, restrict_Ioo_eq_restrict_Ioc]
  have henergy : (∫ r, radialAngularMean (fun θ => g (r, θ) ^ 2) ∂μ) =
      Real.pi⁻¹ * ‖u‖ ^ 2 := by
    rw [← hline, n07a_periodic_radial_mean_eq_half hm.le hgHalf.integrable_sq
      (hp.mono fun r hpr => fun θ => congrArg (fun x : ℝ => x ^ 2) (hpr θ))]
    congr 1
    have hnorm : ‖u‖ ^ 2 = ∫ p, f p ^ 2 ∂canonicalMeasure S K m := by
      simpa only [Lp.toLp_coeFn] using reference_memLp_norm_sq_eq_integral (Lp.memLp u)
    rw [hnorm, n07aCanonicalMeasure_eq_prod]
    exact integral_congr_ae (hgprod.mono fun p hp => congrArg (· ^ 2) hp)
  calc
    _ = ∫ r, ∑ n ∈ I, referenceRadialCoefficient g n r ^ 2 ∂μ := by
      simp_rw [hterm]
      exact (integral_finsetSum I (fun n _ => hi n)).symm
    _ ≤ ∫ r, radialAngularMean (fun θ => g (r, θ) ^ 2) ∂μ := by
      apply integral_mono_ae (integrable_finsetSum I (fun n _ => hi n))
        (integrable_radialAngularMean_sq hfull)
      filter_upwards [memLp_two_prod_sections hfull] with r hr
      exact referenceAngularCoefficient_sum_sq_le hr I
    _ = _ := henergy

theorem n07aCanonicalRadialMode_summable_sq (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) : Summable (fun n => ‖n07aCanonicalRadialMode u n‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (n07aCanonicalRadialMode_sum_sq_le hm u)

theorem n07aCanonicalUnitMode_sum_sq_le (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (I : Finset ℕ) :
    (∑ n ∈ I, ‖n07aCanonicalUnitMode hm u n‖ ^ 2) ≤
      (K.right m - K.left m)⁻¹ * (Real.pi⁻¹ * ‖u‖ ^ 2) := by
  simp_rw [n07aCanonicalUnitMode_norm_sq]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (n07aCanonicalRadialMode_sum_sq_le hm u I)
    (inv_nonneg.mpr (sub_nonneg.mpr hm.le))

end ContinuousFlexibility.Analysis
