module

public import ContinuousFlexibility.Analysis.N07aCanonicalCutoffColumn

/-!
# Green pairing including the actual potential

An open smooth comparison field need not have a global extension or an
unweighted L² norm. Compact tests and the actual source column justify
every integral and move the whole divergence-plus-potential expression.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonicalOpen_green_potential (A : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ A.a (canonicalOpen S K m))
    (hb : ContDiffOn ℝ ∞ A.b (canonicalOpen S K m))
    (hc : ContDiffOn ℝ ∞ A.c (canonicalOpen S K m))
    (hap : ∀ p ∈ canonicalOpen S K m, A.a (p + (0, Real.pi)) = A.a p)
    (hbp : ∀ p ∈ canonicalOpen S K m, A.b (p + (0, Real.pi)) = A.b p)
    (hcp : ∀ p ∈ canonicalOpen S K m, A.c (p + (0, Real.pi)) = A.c p)
    {f q H W : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hfp : ∀ p ∈ canonicalOpen S K m, f (p + (0, Real.pi)) = f p)
    (hq : ContDiffOn ℝ ∞ q (canonicalOpen S K m))
    (hqp : ∀ p ∈ canonicalOpen S K m, q (p + (0, Real.pi)) = q p)
    (hH : ContDiffOn ℝ ∞ H (canonicalOpen S K m))
    (hHp : ∀ p ∈ canonicalOpen S K m, H (p + (0, Real.pi)) = H p)
    (hcolumn : EqOn H (fun p => divergenceOperator A f p + q p * f p)
      (canonicalOpen S K m)) (hW : CanonicalTest S K m W) :
    (∫ p, f p * (divergenceOperator A W p + q p * W p)
      ∂canonicalMeasure S K m) =
      ∫ p, H p * W p ∂canonicalMeasure S K m := by
  have hdivW := n07a_canonicalTest_divergence A ha hb hc hap hbp hcp hW
  have hqW := n07a_canonicalTest_mul_on hW hq hqp
  have hidivW := n07a_canonicalOpen_integrable_mul_test hf hfp hdivW
  have hiqW := n07a_canonicalOpen_integrable_mul_test hf hfp hqW
  have hiH := n07a_canonicalOpen_integrable_mul_test hH hHp hW
  have hidivf : Integrable (fun p => divergenceOperator A f p * W p)
      (canonicalMeasure S K m) := by
    apply (hiH.sub hiqW).congr
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    simp only [Pi.sub_apply]
    rw [hcolumn hp]
    ring
  have he : (fun p => H p * W p) =ᵐ[canonicalMeasure S K m]
      fun p => divergenceOperator A f p * W p + f p * (q p * W p) := by
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    rw [hcolumn hp]
    ring
  simp_rw [mul_add]
  rw [integral_add hidivW hiqW,
    n07a_canonicalOpen_green A ha hb hc hap hbp hcp hf hfp hW,
    integral_congr_ae he, integral_add hidivf hiqW]

end ContinuousFlexibility.Analysis
