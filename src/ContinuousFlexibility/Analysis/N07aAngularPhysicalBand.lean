module

public import ContinuousFlexibility.Analysis.N07aAngularBands
public import ContinuousFlexibility.Analysis.N07aAngularCosineCoefficients
public import ContinuousFlexibility.Analysis.N07aAngularPeriodMeasure

/-!
# Identification of canonical bands with actual physical cosine projections

All radial Fourier indices are retained.  Fubini identifies the true
two-variable coefficient with the Fourier transform of the angular
section coefficient; the scalar half-period identity then identifies the
actual cosine projection with the existing canonical Hilbert band.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ComplexConjugate

variable {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07aCircleFourierCoeff_unscaled (f : ℝ → ℝ) (k : ℤ) :
    (∫ θ, circleFourierWave (-k) θ * (f θ : ℂ) ∂angleMeasure) =
      (Real.pi : ℂ) * circleFourierCoeff f k := by
  rw [circleFourierCoeff_integral, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul]

/-- Genuine partial angular analysis of every radial Fourier coefficient. -/
theorem n07aAngularFourier_partial (m : ℕ) (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (f : PolarPoint → ℝ)
    (huf : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f)
    (j : SpacesTorusFrequency) :
    n07aAngularFourier m hm u j =
      (((Real.sqrt (n07aAngularCellArea (K := K) m) *
        (n07aAngularCellArea (K := K) m)⁻¹) : ℝ) : ℂ) *
        ∫ r, spacesUnitFourierAffine (-(j 0)) (1 / (K.right m - K.left m))
          (-K.left m / (K.right m - K.left m)) r *
          ((Real.pi : ℂ) * circleFourierCoeff (fun θ => f (r, θ)) (j 1))
          ∂volume.restrict (Ioo (K.left m) (K.right m)) := by
  have hf : MemLp f 2 (canonicalMeasure S K m) := (memLp_congr_ae huf).mp (Lp.memLp u)
  have hF : Integrable
      (fun p => n07aAngularCanonicalWave (K := K) m (-j) p * (f p : ℂ))
      ((volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure) := by
    rw [← n07aCanonicalMeasure_eq_prod]
    exact memLp_one_iff_integrable.mp
      ((n07aCanonicalContinuous_memLp (S := S) (K := K) m
        (n07aAngularCanonicalWave_contDiff m (-j)).continuous).mul hf.ofReal)
  rw [n07aAngularFourier_coefficient]
  have he : (∫ p, n07aAngularCanonicalWave (K := K) m (-j) p * (u p : ℂ)
        ∂canonicalMeasure S K m) =
      ∫ p, n07aAngularCanonicalWave (K := K) m (-j) p * (f p : ℂ)
        ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [huf] with p hp
    rw [hp]
  rw [he, n07aCanonicalMeasure_eq_prod, integral_prod _ hF]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by
    simp only [n07aAngularCanonicalWave_separated, n07aAngularWave, Pi.neg_apply, mul_assoc]
    rw [integral_const_mul, n07aCircleFourierCoeff_unscaled]

theorem n07aCanonical_memLp_of_full {m : ℕ} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 ((volume.restrict (Ioo (K.left m) (K.right m))).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) :
    MemLp f 2 (canonicalMeasure S K m) := by
  rw [n07aCanonicalMeasure_eq_prod]
  exact hf.mono_measure (Measure.prod_mono le_rfl
    (Measure.restrict_mono_set _ (Ioc_subset_Ioc le_rfl (by linarith [Real.pi_pos]))))

/-- Actual finite cosine projection masks exactly the canonical angular index. -/
theorem n07aAngularFourier_basisProjection (m : ℕ) (hm : K.left m < K.right m)
    {u v : CanonicalL2 S K m} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 ((volume.restrict (Ioo (K.left m) (K.right m))).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))))
    (hp : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      Function.Even (fun θ => f (r, θ))) (I : Finset ℕ)
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f)
    (hv : (v : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] referenceBasisProjection I f)
    (j : SpacesTorusFrequency) :
    n07aAngularFourier m hm v j =
      if n07aAngularFrequency j ∈ I then n07aAngularFourier m hm u j else 0 := by
  have hs : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      circleFourierCoeff (fun θ => referenceBasisProjection I f (r, θ)) (j 1) =
        if n07aAngularFrequency j ∈ I then circleFourierCoeff (fun θ => f (r, θ)) (j 1) else 0 := by
    filter_upwards [memLp_two_prod_sections hf, hp, he] with r hfr hpr her
    exact n07a_circleFourierCoeff_basisProjection hfr hpr her I (j 1)
  rw [n07aAngularFourier_partial m hm v _ hv j]
  by_cases hj : n07aAngularFrequency j ∈ I
  · rw [ite_eq_left hj, n07aAngularFourier_partial m hm u _ hu j]
    congr 1
    apply integral_congr_ae
    filter_upwards [hs] with r hr
    rw [hr, ite_eq_left hj]
  · rw [ite_eq_right hj]
    suffices hzero : (∫ r, spacesUnitFourierAffine (-(j 0))
        (1 / (K.right m - K.left m)) (-K.left m / (K.right m - K.left m)) r *
        ((Real.pi : ℂ) * circleFourierCoeff
          (fun θ => referenceBasisProjection I f (r, θ)) (j 1))
        ∂volume.restrict (Ioo (K.left m) (K.right m))) = 0 by
      rw [hzero, mul_zero]
    apply integral_eq_zero_of_ae
    filter_upwards [hs] with r hr
    rw [hr, ite_eq_right hj, mul_zero, mul_zero, Pi.zero_apply]

/-- The existing canonical Hilbert band has the actual physical cosine
projection as a representative on the prescribed canonical measure. -/
theorem n07aAngularBand_eq_referenceBasisProjection (m : ℕ)
    (hm : K.left m < K.right m) {u : CanonicalL2 S K m} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 ((volume.restrict (Ioo (K.left m) (K.right m))).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))))
    (hp : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      Function.Even (fun θ => f (r, θ)))
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f) (n : ℕ) :
    (n07aAngularBand m hm n u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      referenceBasisProjection {n} f := by
  have hg := n07aCanonical_memLp_of_full (memLp_referenceBasisProjection_prod hf {n})
  let v : CanonicalL2 S K m := hg.toLp (referenceBasisProjection {n} f)
  have hv : (v : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      referenceBasisProjection {n} f := hg.coeFn_toLp
  have hEq : n07aAngularBand m hm n u = v := by
    apply (n07aAngularFourier m hm).injective
    apply lp.ext
    funext j
    rw [n07aAngularBand_coefficient, n07aAngularFourier_basisProjection m hm hf hp he {n} hu hv]
    simp only [Finset.mem_singleton]
  rw [hEq]
  exact hv

/-- No full-period integrability needs to be assumed for a genuine periodic
representative of an existing canonical class. -/
theorem n07aAngularBand_eq_reference_of_periodic (m : ℕ)
    (hm : K.left m < K.right m) {u : CanonicalL2 S K m} {f : PolarPoint → ℝ}
    (hp : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      Function.Even (fun θ => f (r, θ)))
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f) (n : ℕ) :
    (n07aAngularBand m hm n u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      referenceBasisProjection {n} f :=
  n07aAngularBand_eq_referenceBasisProjection m hm
    (n07aCanonical_memLp_full_of_periodic ((memLp_congr_ae hu).mp (Lp.memLp u)) hp) hp he hu n

end ContinuousFlexibility.Statements
