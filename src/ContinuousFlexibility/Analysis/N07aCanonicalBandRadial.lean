module

public import ContinuousFlexibility.Analysis.N07aCanonicalBandModes
public import ContinuousFlexibility.Analysis.N07aCanonicalRadialReflection
public import ContinuousFlexibility.Analysis.N07aCanonicalSmoothJets

/-!
# Actual angular bands commute with weak radial differentiation

The proof moves the genuine cosine projection onto compact tests. Its
radial derivative is differentiated under the fixed angular integral.
Uniqueness then shows that the original weak derivative retains a single
input band. No derivative of an arbitrary L² representative is taken.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

theorem n07a_referenceBasisProjection_single (n : ℕ) (f : PolarPoint → ℝ) :
    referenceBasisProjection {n} f = fun p => referenceRadialCoefficient f n p.1 *
      referenceAngularBasis n p.2 := by
  funext p
  simp only [referenceBasisProjection, angularBasisProjection, Finset.sum_singleton,
    referenceRadialCoefficient]

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonicalTest_basisProjection {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) (n : ℕ) :
    CanonicalTest S K m (referenceBasisProjection {n} φ) := by
  obtain ⟨hs, hp, J, hJ, hJI, hz⟩ := hφ
  refine ⟨referenceBasisProjection_contDiff hs {n}, referenceBasisProjection_periodic {n} φ,
    J, hJ, hJI, ?_⟩
  intro r hr θ
  rw [n07a_referenceBasisProjection_single]
  change referenceRadialCoefficient φ n r * referenceAngularBasis n θ = 0
  rw [referenceRadialCoefficient_zero_outside hz n hr, zero_mul]

theorem n07a_referenceBasisProjection_firstNormal {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (n : ℕ) :
    mixedDerivative 1 0 (referenceBasisProjection {n} φ) =
      referenceBasisProjection {n} (mixedDerivative 1 0 φ) := by
  rw [n07a_referenceBasisProjection_single, n07a_referenceBasisProjection_single]
  funext p
  rw [n07a_canonical_basis_radial (contDiff_referenceRadialCoefficient hφ n) n,
    deriv_referenceRadialCoefficient hφ, n07a_radialPartial_eq_mixed hφ]

theorem n07aAngularBand_test_pairing (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (hu : n07aAngularReflection m u = u) (n : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, n07aAngularBand m hm n u p * φ p ∂canonicalMeasure S K m) =
      ∫ p, u p * referenceBasisProjection {n} φ p ∂canonicalMeasure S K m := by
  let a := n07aHalfRadialCoefficient u n
  let f : PolarPoint → ℝ := fun p => (a p.1 * referenceAngularBasis n p.2) * φ p
  have he : (fun p => n07aAngularBand m hm n u p * φ p) =ᵐ[canonicalMeasure S K m] f :=
    (n07aAngularBand_cosine_ae hm u hu n).mono fun p hp => congrArg (· * φ p) hp
  have hf : Integrable f (canonicalMeasure S K m) :=
    ((Lp.memLp (n07aAngularBand m hm n u)).integrable_mul (n07a_canonicalTest_memLp hφ)).congr he
  rw [n07aCanonicalMeasure_eq_prod] at hf
  have hiR : Integrable (fun p => u p *
      (referenceRadialCoefficient φ n p.1 * referenceAngularBasis n p.2))
      (canonicalMeasure S K m) := by
    have h := (Lp.memLp u).integrable_mul
      (n07a_canonicalTest_memLp (n07a_canonicalTest_basisProjection hφ n))
    rwa [n07a_referenceBasisProjection_single] at h
  have hc (r : ℝ) : n07aHalfRadialCoefficient φ n r = referenceRadialCoefficient φ n r := by
    apply n07aHalfRadialCoefficient_eq_reference n r
    · intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hφ.2.1 (r, θ)
    · exact (hφ.1.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hprod : (∫ p, f p ∂canonicalMeasure S K m) =
      ∫ r in Ioo (K.left m) (K.right m), ∫ θ, f (r, θ) ∂angleMeasure := by
    rw [n07aCanonicalMeasure_eq_prod, integral_prod _ hf]
  calc
    _ = ∫ p, f p ∂canonicalMeasure S K m := integral_congr_ae he
    _ = Real.pi * ∫ r in Ioo (K.left m) (K.right m), a r * referenceRadialCoefficient φ n r := by
      rw [hprod, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun r => by
        change (∫ θ, f (r, θ) ∂angleMeasure) =
          Real.pi * (a r * referenceRadialCoefficient φ n r)
        have hcomm : (fun θ => f (r, θ)) =
            fun θ => φ (r, θ) * (a r * referenceAngularBasis n θ) := by
          funext θ
          dsimp only [f]
          ring
        rw [hcomm, n07a_canonical_basis_row_integral, hc]
        ring
    _ = _ := by
      rw [n07a_referenceBasisProjection_single]
      exact (n07a_canonical_basis_pairing_integrable u n (referenceRadialCoefficient φ n) hiR).symm

theorem n07a_weakCanonical_firstNormal_band (hm : K.left m < K.right m)
    {u d : CanonicalL2 S K m} (hu : n07aAngularReflection m u = u)
    (hd : N07aWeakCanonicalMixedDerivative S K m u d 1 0) (n : ℕ) :
    N07aWeakCanonicalMixedDerivative S K m
      (n07aAngularBand m hm n u) (n07aAngularBand m hm n d) 1 0 := by
  have hdEven := n07a_weakCanonical_radial_reflection hm hu hd
  intro φ hφ
  simp only [Nat.add_zero, pow_one, neg_one_mul]
  calc
    _ = ∫ p, d p * referenceBasisProjection {n} φ p ∂canonicalMeasure S K m :=
      n07aAngularBand_test_pairing hm d hdEven n hφ
    _ = -(∫ p, u p * mixedDerivative 1 0 (referenceBasisProjection {n} φ) p
        ∂canonicalMeasure S K m) := by
      simpa only [Nat.add_zero, pow_one, neg_one_mul] using
        hd _ (n07a_canonicalTest_basisProjection hφ n)
    _ = -(∫ p, u p * referenceBasisProjection {n} (mixedDerivative 1 0 φ) p
        ∂canonicalMeasure S K m) := by rw [n07a_referenceBasisProjection_firstNormal hφ.1]
    _ = _ := congrArg Neg.neg (n07aAngularBand_test_pairing hm u hu n
      (n07a_canonicalTest_mixedDerivative hφ 1 0)).symm

theorem n07a_firstNormal_singleBand (hm : K.left m < K.right m)
    {u d : CanonicalL2 S K m} (hu : n07aAngularReflection m u = u)
    (hd : N07aWeakCanonicalMixedDerivative S K m u d 1 0) (n : ℕ)
    (hband : n07aAngularBand m hm n u = u) : n07aAngularBand m hm n d = d := by
  have h := n07a_weakCanonical_firstNormal_band hm hu hd n
  rw [hband] at h
  exact n07a_weakCanonicalMixed_unique hm h hd

end ContinuousFlexibility.Analysis
