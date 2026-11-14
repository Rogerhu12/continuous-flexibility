module

public import ContinuousFlexibility.Analysis.N07aCanonicalGreenPairing

/-! # Canonical divergence preserves compact canonical tests -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- Open smooth periodic coefficients send a genuine compact test to a
genuine compact test under the actual symmetric divergence expression. -/
theorem n07a_canonicalTest_divergence (A : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ A.a (canonicalOpen S K m))
    (hb : ContDiffOn ℝ ∞ A.b (canonicalOpen S K m))
    (hc : ContDiffOn ℝ ∞ A.c (canonicalOpen S K m))
    (hap : ∀ p ∈ canonicalOpen S K m, A.a (p + (0, Real.pi)) = A.a p)
    (hbp : ∀ p ∈ canonicalOpen S K m, A.b (p + (0, Real.pi)) = A.b p)
    (hcp : ∀ p ∈ canonicalOpen S K m, A.c (p + (0, Real.pi)) = A.c p)
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) :
    CanonicalTest S K m (divergenceOperator A W) := by
  have hWr := n07a_canonicalTest_mixedDerivative hW 1 0
  have hWt := n07a_canonicalTest_mixedDerivative hW 0 1
  let qr := fun p => A.a p * mixedDerivative 1 0 W p + A.b p * mixedDerivative 0 1 W p
  let qt := fun p => A.b p * mixedDerivative 1 0 W p + A.c p * mixedDerivative 0 1 W p
  have hqr : CanonicalTest S K m qr := n07a_canonicalTest_add
    (n07a_canonicalTest_mul_on hWr ha hap) (n07a_canonicalTest_mul_on hWt hb hbp)
  have hqt : CanonicalTest S K m qt := n07a_canonicalTest_add
    (n07a_canonicalTest_mul_on hWr hb hbp) (n07a_canonicalTest_mul_on hWt hc hcp)
  have he : divergenceOperator A W =
      fun p => mixedDerivative 1 0 qr p + mixedDerivative 0 1 qt p := by
    funext p
    simp only [divergenceOperator, n07a_radialPartial_eq_mixed hW.1,
      n07a_angularPartial_eq_mixed hW.1]
    change radialPartial qr p + angularPartial qt p = _
    rw [n07a_radialPartial_eq_mixed hqr.1, n07a_angularPartial_eq_mixed hqt.1]
  rw [he]
  exact n07a_canonicalTest_add (n07a_canonicalTest_mixedDerivative hqr 1 0)
    (n07a_canonicalTest_mixedDerivative hqt 0 1)

end ContinuousFlexibility.Analysis
