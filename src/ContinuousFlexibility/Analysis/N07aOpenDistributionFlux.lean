module

public import ContinuousFlexibility.Analysis.N07aCanonicalTestDivergence
public import ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficients

/-!
# The actual open-coefficient distribution equation gives its weak flux

Every coefficient is multiplied by a compact test before integration by
parts. No global smooth extension of an open coefficient is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem N07aCanonicalOpenCoefficient.mul_pairing
    (χ : N07aCanonicalOpenCoefficient S K m) (u : CanonicalL2 S K m)
    (φ : PolarPoint → ℝ) :
    (∫ p, χ.mul u p * φ p ∂canonicalMeasure S K m) =
      ∫ p, u p * (χ.value p * φ p) ∂canonicalMeasure S K m :=
  n07aCanonicalMultiplier_pairing χ.value _ _ _ u φ

theorem n07a_openDistribution_flux
    (a b c : N07aCanonicalOpenCoefficient S K m)
    {u ur uθ F : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (heq : N07aCanonicalDistributionEquation S K m ⟨a.value, b.value, c.value⟩ u F) :
    N07aCanonicalFluxEquation S K m F (a.mul ur + b.mul uθ) (b.mul ur + c.mul uθ) := by
  intro φ hφ
  let φr := mixedDerivative 1 0 φ
  let φθ := mixedDerivative 0 1 φ
  have hφr : CanonicalTest S K m φr := n07a_canonicalTest_mixedDerivative hφ 1 0
  have hφθ : CanonicalTest S K m φθ := n07a_canonicalTest_mixedDerivative hφ 0 1
  let ψr : PolarPoint → ℝ := fun p => a.value p * φr p + b.value p * φθ p
  let ψθ : PolarPoint → ℝ := fun p => b.value p * φr p + c.value p * φθ p
  have hψr : CanonicalTest S K m ψr :=
    n07a_canonicalTest_add (n07a_canonicalTest_mul_on hφr a.smooth a.periodic)
      (n07a_canonicalTest_mul_on hφθ b.smooth b.periodic)
  have hψθ : CanonicalTest S K m ψθ :=
    n07a_canonicalTest_add (n07a_canonicalTest_mul_on hφr b.smooth b.periodic)
      (n07a_canonicalTest_mul_on hφθ c.smooth c.periodic)
  have hdiv : divergenceOperator ⟨a.value, b.value, c.value⟩ φ =
      fun p => mixedDerivative 1 0 ψr p + mixedDerivative 0 1 ψθ p := by
    funext p
    simp only [divergenceOperator, n07a_radialPartial_eq_mixed hφ.1,
      n07a_angularPartial_eq_mixed hφ.1]
    change radialPartial ψr p + angularPartial ψθ p = _
    rw [n07a_radialPartial_eq_mixed hψr.1, n07a_angularPartial_eq_mixed hψθ.1]
  have hdeq := heq φ hφ
  rw [hdiv] at hdeq
  simp_rw [mul_add] at hdeq
  have hi₁ : Integrable (fun p => u p * mixedDerivative 1 0 ψr p)
      (canonicalMeasure S K m) := (Lp.memLp u).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hψr 1 0))
  have hi₂ : Integrable (fun p => u p * mixedDerivative 0 1 ψθ p)
      (canonicalMeasure S K m) := (Lp.memLp u).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hψθ 0 1))
  rw [integral_add hi₁ hi₂] at hdeq
  have hrtest := hr ψr hψr
  have hθtest := hθ ψθ hψθ
  simp only [add_zero, zero_add, pow_one, neg_one_mul] at hrtest hθtest
  have hir₁ : Integrable (fun p => ur p * (a.value p * φr p))
      (canonicalMeasure S K m) := (Lp.memLp ur).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hφr a.smooth a.periodic))
  have hir₂ : Integrable (fun p => ur p * (b.value p * φθ p))
      (canonicalMeasure S K m) := (Lp.memLp ur).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hφθ b.smooth b.periodic))
  have hiθ₁ : Integrable (fun p => uθ p * (b.value p * φr p))
      (canonicalMeasure S K m) := (Lp.memLp uθ).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hφr b.smooth b.periodic))
  have hiθ₂ : Integrable (fun p => uθ p * (c.value p * φθ p))
      (canonicalMeasure S K m) := (Lp.memLp uθ).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hφθ c.smooth c.periodic))
  simp only [ψr, mul_add] at hrtest
  rw [integral_add hir₁ hir₂] at hrtest
  simp only [ψθ, mul_add] at hθtest
  rw [integral_add hiθ₁ hiθ₂] at hθtest
  rw [n07a_canonicalIntegral_add _ _ (n07a_canonicalTest_memLp hφr),
    n07a_canonicalIntegral_add _ _ (n07a_canonicalTest_memLp hφθ)]
  simp only [N07aCanonicalOpenCoefficient.mul_pairing]
  linarith only [hdeq, hrtest, hθtest]

end ContinuousFlexibility.Analysis
