import ContinuousFlexibility.Analysis.N07aWeakRegularityAlgebra
import ContinuousFlexibility.Analysis.N07aAngularClassical
import ContinuousFlexibility.Analysis.PhysicalTransmissionOperator

/-!
# From the actual distributional operator to the weak flux equation

The operator is the frozen `divergenceOperator`. Testing the known first
weak derivatives against its two smooth coefficient fluxes proves the
first-order divergence identity used in normal regularity. The unknown
itself is only an L² class throughout this argument.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonicalTest_add {φ ψ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) (hψ : CanonicalTest S K m ψ) :
    CanonicalTest S K m (fun p => φ p + ψ p) := by
  obtain ⟨hφs, hφp, J, hJ, hJI, hJz⟩ := hφ
  obtain ⟨hψs, hψp, Q, hQ, hQI, hQz⟩ := hψ
  refine ⟨hφs.add hψs, hφp.add hψp, J ∪ Q, hJ.union hQ,
    union_subset hJI hQI, ?_⟩
  intro r hr θ
  change φ (r, θ) + ψ (r, θ) = 0
  rw [hJz r (fun h => hr (Or.inl h)) θ, hQz r (fun h => hr (Or.inr h)) θ, zero_add]

theorem n07a_radialPartial_eq_mixed {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    radialPartial φ = mixedDerivative 1 0 φ := by
  simpa only [spaces_mixedDerivative_zero, zero_add] using radialPartial_mixedDerivative hφ 0 0

theorem n07a_angularPartial_eq_mixed {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    angularPartial φ = mixedDerivative 0 1 φ := by
  simpa only [spaces_mixedDerivative_zero, zero_add] using angularPartial_mixedDerivative hφ 0 0

theorem n07a_canonicalIntegral_add (u v : CanonicalL2 S K m)
    {φ : PolarPoint → ℝ} (hφ : MemLp φ 2 (canonicalMeasure S K m)) :
    (∫ p, (u + v) p * φ p ∂canonicalMeasure S K m) =
      (∫ p, u p * φ p ∂canonicalMeasure S K m) +
        ∫ p, v p * φ p ∂canonicalMeasure S K m := by
  rw [← n07aCanonicalTestPairing_apply φ hφ, map_add,
    n07aCanonicalTestPairing_apply, n07aCanonicalTestPairing_apply]

theorem n07aSmoothCanonicalMul_pairing (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (u : CanonicalL2 S K m) (φ : PolarPoint → ℝ) :
    (∫ p, n07aSmoothCanonicalMul χ hχ u p * φ p ∂canonicalMeasure S K m) =
      ∫ p, u p * (χ p * φ p) ∂canonicalMeasure S K m :=
  n07aCanonicalMultiplier_pairing χ _ _ _ u φ

/-- The original distributional second-order equation on a canonical
piece, expressed with the frozen symmetric divergence operator. -/
def N07aCanonicalDistributionEquation (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (L : SymmetricCoefficients) (u F : CanonicalL2 S K m) : Prop :=
  ∀ φ, CanonicalTest S K m φ →
    (∫ p, u p * divergenceOperator L φ p ∂canonicalMeasure S K m) =
      ∫ p, F p * φ p ∂canonicalMeasure S K m

/-- The actual distributional divergence equation gives the true weak
flux identity as soon as the first two weak derivatives are known. -/
theorem n07a_weakDivergence_flux (L : SymmetricCoefficients)
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hap : Function.Periodic L.a (0, Real.pi))
    (hbp : Function.Periodic L.b (0, Real.pi))
    (hcp : Function.Periodic L.c (0, Real.pi))
    {u ur uθ F : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (heq : N07aCanonicalDistributionEquation S K m L u F) :
    N07aCanonicalFluxEquation S K m F
      (n07aSmoothCanonicalMul L.a ha ur + n07aSmoothCanonicalMul L.b hb uθ)
      (n07aSmoothCanonicalMul L.b hb ur + n07aSmoothCanonicalMul L.c hc uθ) := by
  intro φ hφ
  let φr := mixedDerivative 1 0 φ
  let φθ := mixedDerivative 0 1 φ
  have hφr : CanonicalTest S K m φr := n07a_canonicalTest_mixedDerivative hφ 1 0
  have hφθ : CanonicalTest S K m φθ := n07a_canonicalTest_mixedDerivative hφ 0 1
  let ψr : PolarPoint → ℝ := fun p => L.a p * φr p + L.b p * φθ p
  let ψθ : PolarPoint → ℝ := fun p => L.b p * φr p + L.c p * φθ p
  have hψr : CanonicalTest S K m ψr :=
    n07a_canonicalTest_add (n07a_canonicalTest_mul hφr ha hap)
      (n07a_canonicalTest_mul hφθ hb hbp)
  have hψθ : CanonicalTest S K m ψθ :=
    n07a_canonicalTest_add (n07a_canonicalTest_mul hφr hb hbp)
      (n07a_canonicalTest_mul hφθ hc hcp)
  have hdiv : divergenceOperator L φ =
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
  have hir₁ : Integrable (fun p => ur p * (L.a p * φr p))
      (canonicalMeasure S K m) := (Lp.memLp ur).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul hφr ha hap))
  have hir₂ : Integrable (fun p => ur p * (L.b p * φθ p))
      (canonicalMeasure S K m) := (Lp.memLp ur).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul hφθ hb hbp))
  have hiθ₁ : Integrable (fun p => uθ p * (L.b p * φr p))
      (canonicalMeasure S K m) := (Lp.memLp uθ).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul hφr hb hbp))
  have hiθ₂ : Integrable (fun p => uθ p * (L.c p * φθ p))
      (canonicalMeasure S K m) := (Lp.memLp uθ).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mul hφθ hc hcp))
  simp only [ψr, mul_add] at hrtest
  rw [integral_add hir₁ hir₂] at hrtest
  simp only [ψθ, mul_add] at hθtest
  rw [integral_add hiθ₁ hiθ₂] at hθtest
  rw [n07a_canonicalIntegral_add _ _ (n07a_canonicalTest_memLp hφr),
    n07a_canonicalIntegral_add _ _ (n07a_canonicalTest_memLp hφθ)]
  simp only [n07aSmoothCanonicalMul_pairing]
  linarith only [hdeq, hrtest, hθtest]

end ContinuousFlexibility.Analysis
