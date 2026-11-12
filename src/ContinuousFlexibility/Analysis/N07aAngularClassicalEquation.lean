import ContinuousFlexibility.Analysis.N07aAngularOpenRegularity
import ContinuousFlexibility.Analysis.N07aCanonicalGreenPairing
import ContinuousFlexibility.Analysis.N07aOpenClassicalNormal

/-!
# The original distribution equation is the classical divergence equation

For an actual smooth periodic representative, Green's identity transfers
the derivatives from compact tests. The genuine compact-test separation
of the canonical L² space then identifies the original source with its
classical divergence. No equation is substituted for the actual
`divergenceOperator`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonicalOpen_divergence_contDiffOn (A : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ A.a (canonicalOpen S K m))
    (hb : ContDiffOn ℝ ∞ A.b (canonicalOpen S K m))
    (hc : ContDiffOn ℝ ∞ A.c (canonicalOpen S K m))
    {v : PolarPoint → ℝ} (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m)) :
    ContDiffOn ℝ ∞ (divergenceOperator A v) (canonicalOpen S K m) := by
  have hU : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hvr := contDiffOn_mixedDerivative hU hv 1 0
  have hvθ := contDiffOn_mixedDerivative hU hv 0 1
  exact ((contDiffOn_mixedDerivative hU ((ha.mul hvr).add (hb.mul hvθ)) 1 0).add
    (contDiffOn_mixedDerivative hU ((hb.mul hvr).add (hc.mul hvθ)) 0 1)).congr
    (n07a_open_divergence_mixed A ha hb hc hv)

theorem n07a_canonicalOpen_divergence_periodic (A : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ A.a (canonicalOpen S K m))
    (hb : ContDiffOn ℝ ∞ A.b (canonicalOpen S K m))
    (hc : ContDiffOn ℝ ∞ A.c (canonicalOpen S K m))
    (hap : ∀ p ∈ canonicalOpen S K m, A.a (p + (0, Real.pi)) = A.a p)
    (hbp : ∀ p ∈ canonicalOpen S K m, A.b (p + (0, Real.pi)) = A.b p)
    (hcp : ∀ p ∈ canonicalOpen S K m, A.c (p + (0, Real.pi)) = A.c p)
    {v : PolarPoint → ℝ} (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m))
    (hvp : ∀ p ∈ canonicalOpen S K m, v (p + (0, Real.pi)) = v p) :
    ∀ p ∈ canonicalOpen S K m,
      divergenceOperator A v (p + (0, Real.pi)) = divergenceOperator A v p := by
  have hvrp := n07a_mixedDerivative_periodic_on hvp 1 0
  have hvθp := n07a_mixedDerivative_periodic_on hvp 0 1
  have hrp : ∀ p ∈ canonicalOpen S K m,
      (A.a (p + (0, Real.pi)) * mixedDerivative 1 0 v (p + (0, Real.pi)) +
        A.b (p + (0, Real.pi)) * mixedDerivative 0 1 v (p + (0, Real.pi))) =
      A.a p * mixedDerivative 1 0 v p + A.b p * mixedDerivative 0 1 v p := by
    intro p hp
    rw [hap p hp, hbp p hp, hvrp p hp, hvθp p hp]
  have hθp : ∀ p ∈ canonicalOpen S K m,
      (A.b (p + (0, Real.pi)) * mixedDerivative 1 0 v (p + (0, Real.pi)) +
        A.c (p + (0, Real.pi)) * mixedDerivative 0 1 v (p + (0, Real.pi))) =
      A.b p * mixedDerivative 1 0 v p + A.c p * mixedDerivative 0 1 v p := by
    intro p hp
    rw [hbp p hp, hcp p hp, hvrp p hp, hvθp p hp]
  intro p hp
  have hp' : p + (0, Real.pi) ∈ canonicalOpen S K m := by
    exact ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
  rw [n07a_open_divergence_mixed A ha hb hc hv hp',
    n07a_open_divergence_mixed A ha hb hc hv hp]
  dsimp only
  exact congrArg₂ (· + ·)
    (n07a_mixedDerivative_periodic_on
      (f := fun q => A.a q * mixedDerivative 1 0 v q + A.b q * mixedDerivative 0 1 v q)
      hrp 1 0 p hp)
    (n07a_mixedDerivative_periodic_on
      (f := fun q => A.b q * mixedDerivative 1 0 v q + A.c q * mixedDerivative 0 1 v q)
      hθp 0 1 p hp)

theorem n07a_canonical_test_separation (hm : K.left m < K.right m)
    {u v : CanonicalL2 S K m}
    (heq : ∀ φ, CanonicalTest S K m φ →
      (∫ p, u p * φ p ∂canonicalMeasure S K m) =
        ∫ p, v p * φ p ∂canonicalMeasure S K m) : u = v := by
  apply n07aAngularWeak_unique m hm (f := u) (k := 0)
  · intro φ hφ
    simp only [pow_zero, one_mul, spaces_mixedDerivative_zero]
  · intro φ hφ
    simpa only [pow_zero, one_mul, spaces_mixedDerivative_zero] using (heq φ hφ).symm

/-- Equality is pointwise on the open strip, in the original differential
expression and with the original smooth source representative. -/
theorem n07a_openDistribution_smooth_eqOn (hm : K.left m < K.right m)
    (A : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ A.a (canonicalOpen S K m))
    (hb : ContDiffOn ℝ ∞ A.b (canonicalOpen S K m))
    (hc : ContDiffOn ℝ ∞ A.c (canonicalOpen S K m))
    (hap : ∀ p ∈ canonicalOpen S K m, A.a (p + (0, Real.pi)) = A.a p)
    (hbp : ∀ p ∈ canonicalOpen S K m, A.b (p + (0, Real.pi)) = A.b p)
    (hcp : ∀ p ∈ canonicalOpen S K m, A.c (p + (0, Real.pi)) = A.c p)
    {u F : CanonicalL2 S K m} {v f : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m))
    (hvp : ∀ p ∈ canonicalOpen S K m, v (p + (0, Real.pi)) = v p)
    (hf : ContinuousOn f (canonicalOpen S K m))
    (hfp : ∀ p ∈ canonicalOpen S K m, f (p + (0, Real.pi)) = f p)
    (hue : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] v)
    (hFe : (F : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f)
    (hLp : MemLp (divergenceOperator A v) 2 (canonicalMeasure S K m))
    (heq : N07aCanonicalDistributionEquation S K m A u F) :
    EqOn (divergenceOperator A v) f (canonicalOpen S K m) := by
  let G : CanonicalL2 S K m := hLp.toLp (divergenceOperator A v)
  have hGe : (G : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] divergenceOperator A v :=
    MemLp.coeFn_toLp hLp
  have hGF : G = F := by
    apply n07a_canonical_test_separation hm
    intro φ hφ
    calc
      (∫ p, G p * φ p ∂canonicalMeasure S K m) =
          ∫ p, divergenceOperator A v p * φ p ∂canonicalMeasure S K m := by
        exact integral_congr_ae (hGe.mono fun p hp => congrArg (· * φ p) hp)
      _ = ∫ p, v p * divergenceOperator A φ p ∂canonicalMeasure S K m :=
        (n07a_canonicalOpen_green A ha hb hc hap hbp hcp hv hvp hφ).symm
      _ = ∫ p, u p * divergenceOperator A φ p ∂canonicalMeasure S K m := by
        exact integral_congr_ae (hue.symm.mono fun p hp =>
          congrArg (· * divergenceOperator A φ p) hp)
      _ = _ := heq φ hφ
  rw [hGF] at hGe
  exact n07a_canonical_periodicOn_eqOn_of_ae_eq
    (n07a_canonicalOpen_divergence_contDiffOn A ha hb hc hv).continuousOn hf
    (n07a_canonicalOpen_divergence_periodic A ha hb hc hap hbp hcp hv hvp) hfp
    (hGe.symm.trans hFe)

end ContinuousFlexibility.Analysis
