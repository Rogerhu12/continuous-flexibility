import ContinuousFlexibility.Analysis.N07aOpenDistributionFlux
import ContinuousFlexibility.Analysis.N07aWeakNormalEquation

/-!
# The actual finite weak jet expansion of a divergence operator

The principal expression is an L² class formed from the original five
weak jets. Compact-test product rules identify it with the original
distribution; neither a boundary trace nor a smooth representative of
the unknown is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_openDivergence_pairing
    (a b c : N07aCanonicalOpenCoefficient S K m)
    {u ur uθ : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, u p * divergenceOperator ⟨a.value, b.value, c.value⟩ φ p ∂canonicalMeasure S K m) =
      -((∫ p, (a.mul ur + b.mul uθ) p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m) +
        ∫ p, (b.mul ur + c.mul uθ) p * mixedDerivative 0 1 φ p ∂canonicalMeasure S K m) := by
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
  have hi₁ : Integrable (fun p => u p * mixedDerivative 1 0 ψr p)
      (canonicalMeasure S K m) := (Lp.memLp u).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hψr 1 0))
  have hi₂ : Integrable (fun p => u p * mixedDerivative 0 1 ψθ p)
      (canonicalMeasure S K m) := (Lp.memLp u).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hψθ 0 1))
  have hrtest := hr ψr hψr
  have hθtest := hθ ψθ hψθ
  simp only [add_zero, zero_add, pow_one, neg_one_mul] at hrtest hθtest
  have hir₁ := (Lp.memLp ur).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hφr a.smooth a.periodic))
  have hir₂ := (Lp.memLp ur).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hφθ b.smooth b.periodic))
  have hiθ₁ := (Lp.memLp uθ).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hφr b.smooth b.periodic))
  have hiθ₂ := (Lp.memLp uθ).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hφθ c.smooth c.periodic))
  change Integrable (fun p => ur p * (a.value p * φr p)) (canonicalMeasure S K m) at hir₁
  change Integrable (fun p => ur p * (b.value p * φθ p)) (canonicalMeasure S K m) at hir₂
  change Integrable (fun p => uθ p * (b.value p * φr p)) (canonicalMeasure S K m) at hiθ₁
  change Integrable (fun p => uθ p * (c.value p * φθ p)) (canonicalMeasure S K m) at hiθ₂
  simp only [ψr, mul_add] at hrtest
  rw [integral_add hir₁ hir₂] at hrtest
  simp only [ψθ, mul_add] at hθtest
  rw [integral_add hiθ₁ hiθ₂] at hθtest
  rw [hdiv]
  simp_rw [mul_add]
  rw [integral_add hi₁ hi₂,
    n07a_canonicalIntegral_add _ _ (n07a_canonicalTest_memLp hφr),
    n07a_canonicalIntegral_add _ _ (n07a_canonicalTest_memLp hφθ)]
  simp only [N07aCanonicalOpenCoefficient.mul_pairing]
  linarith only [hrtest, hθtest]

theorem n07a_openDistribution_of_flux
    (a b c : N07aCanonicalOpenCoefficient S K m)
    {u ur uθ F : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hflux : N07aCanonicalFluxEquation S K m F
      (a.mul ur + b.mul uθ) (b.mul ur + c.mul uθ)) :
    N07aCanonicalDistributionEquation S K m ⟨a.value, b.value, c.value⟩ u F := by
  intro φ hφ
  rw [n07a_openDivergence_pairing a b c hr hθ hφ, hflux φ hφ, neg_neg]

def n07aOpenDivergence (a b c : N07aCanonicalOpenCoefficient S K m)
    (ur uθ urr urθ uθθ : CanonicalL2 S K m) : CanonicalL2 S K m :=
  ((a.mul urr + (a.jet 1 0).mul ur) +
    (b.mul urθ + (b.jet 1 0).mul uθ)) +
  ((b.mul urθ + (b.jet 0 1).mul ur) +
    (c.mul uθθ + (c.jet 0 1).mul uθ))

theorem n07aOpenDivergence_distribution
    (a b c : N07aCanonicalOpenCoefficient S K m)
    {u ur uθ urr urθ uθθ : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hrr : N07aWeakCanonicalMixedDerivative S K m ur urr 1 0)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1) :
    N07aCanonicalDistributionEquation S K m ⟨a.value, b.value, c.value⟩ u
      (n07aOpenDivergence a b c ur uθ urr urθ uθθ) := by
  apply n07a_openDistribution_of_flux a b c hr hθ
  exact n07a_weakCanonical_flux_of_derivatives
    ((a.first_product 0 hrr).add
      (b.first_product 0 (n07a_weakCanonical_crossDerivative hr hθ hrθ)))
    ((b.first_product 1 hrθ).add (c.first_product 1 hθθ)) rfl

end ContinuousFlexibility.Analysis
