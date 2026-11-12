import ContinuousFlexibility.Analysis.N07aCanonicalOpenTests

/-!
# The weak product rule for actual open-piece coefficients

All multiplication operators act on the original canonical L² class.
Only the compact test times the coefficient is globally smooth; the
coefficient itself is required to be smooth only where the equation holds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_weakCanonical_first_product_on {χ : PolarPoint → ℝ}
    (hχ : ContDiffOn ℝ ∞ χ (canonicalOpen S K m))
    (hχp : ∀ p ∈ canonicalOpen S K m, χ (p + (0, Real.pi)) = χ p)
    (j : Fin 2) (A B : ℝ)
    (hA : ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A)
    (hB : ∀ᵐ p ∂canonicalMeasure S K m,
      |mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ p| ≤ B)
    {f g : CanonicalL2 S K m}
    (hfg : N07aWeakCanonicalMixedDerivative S K m f g
      (n07aFirstOrder j).1 (n07aFirstOrder j).2) :
    N07aWeakCanonicalMixedDerivative S K m
      (n07aCanonicalMultiplier χ (n07a_canonicalOpen_aestronglyMeasurable hχ.continuousOn)
        A hA f)
      (n07aCanonicalMultiplier χ (n07a_canonicalOpen_aestronglyMeasurable hχ.continuousOn)
          A hA g +
        n07aCanonicalMultiplier
          (mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ)
          (n07a_canonicalOpen_aestronglyMeasurable
            (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hχ _ _).continuousOn)
          B hB f)
      (n07aFirstOrder j).1 (n07aFirstOrder j).2 := by
  let dχ := mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ
  have hdχ : ContDiffOn ℝ ∞ dχ (canonicalOpen S K m) :=
    contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hχ _ _
  have hdχp : ∀ p ∈ canonicalOpen S K m, dχ (p + (0, Real.pi)) = dχ p :=
    n07a_mixedDerivative_periodic_on hχp _ _
  intro φ hφ
  let dφ := mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 φ
  have hdφ := n07a_canonicalTest_mixedDerivative hφ (n07aFirstOrder j).1
    (n07aFirstOrder j).2
  have hi₁ : Integrable (fun p => f p * (dχ p * φ p)) (canonicalMeasure S K m) :=
    (Lp.memLp f).integrable_mul
      (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hφ hdχ hdχp))
  have hi₂ : Integrable (fun p => f p * (χ p * dφ p)) (canonicalMeasure S K m) :=
    (Lp.memLp f).integrable_mul
      (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hdφ hχ hχp))
  have htest := hfg (fun p => χ p * φ p) (n07a_canonicalTest_mul_on hφ hχ hχp)
  have hleibniz :
      (∫ p, f p * mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2
        (fun q => χ q * φ q) p ∂canonicalMeasure S K m) =
      ∫ p, f p * (dχ p * φ p + χ p * dφ p) ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    exact congrArg (f p * ·) (n07a_mixedDerivative_first_mul_on hχ hφ.1.contDiffOn j hp)
  rw [n07aFirstOrder_sum, pow_one, neg_one_mul, hleibniz] at htest
  have hsplit :
      (∫ p, f p * (dχ p * φ p + χ p * dφ p) ∂canonicalMeasure S K m) =
      (∫ p, f p * (dχ p * φ p) ∂canonicalMeasure S K m) +
        ∫ p, f p * (χ p * dφ p) ∂canonicalMeasure S K m := by
    simp_rw [mul_add]
    exact integral_add hi₁ hi₂
  rw [hsplit] at htest
  rw [← n07aCanonicalTestPairing_apply φ (n07a_canonicalTest_memLp hφ), map_add,
    n07aCanonicalTestPairing_apply, n07aCanonicalTestPairing_apply,
    n07aCanonicalMultiplier_pairing, n07aCanonicalMultiplier_pairing,
    n07aFirstOrder_sum, pow_one, neg_one_mul, n07aCanonicalMultiplier_pairing]
  change (∫ p, g p * (χ p * φ p) ∂canonicalMeasure S K m) +
    (∫ p, f p * (dχ p * φ p) ∂canonicalMeasure S K m) =
      -(∫ p, f p * (χ p * dφ p) ∂canonicalMeasure S K m)
  linarith only [htest]

end ContinuousFlexibility.Analysis
