module

public import ContinuousFlexibility.Analysis.N06OpenCubicTestCutoff
public import ContinuousFlexibility.Radial.R11bWeakNormalLimit

/-!
# Actual cubic pairings for tests smooth only on the open cylinder

The original weighted graph fields give L2 membership of the true cubic
test operator. The cutoff limit then extends its compact distributional
identity to the actual test itself. Only integrable actual derivatives
are required, and no values of a totalized inverse at an endpoint occur.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n06_cubic_openTest_memLp_of_graph
    (hl : K.left m = 0) (hr : K.right m = 1)
    {A B C φ : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hC : ContDiffOn ℝ ∞ C (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |A p| ≤ δ ∧ |B p| ≤ δ ∧ |C p| ≤ δ ∧
        |radialPartial A p| ≤ δ ∧ |angularPartial B p| ≤ δ ∧
        |radialPartial B p| ≤ δ ∧ |angularPartial C p| ≤ δ)
    (hφ : ContDiffOn ℝ ∞ φ (canonicalOpen S K m))
    (hgraph : ∀ i, MemLp (n06CubicGraphFields (fun p => cylinderWeight p.1) φ i)
      2 (canonicalMeasure S K m)) :
    MemLp (divergenceOperator
      (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) φ) 2
      (canonicalMeasure S K m) := by
  obtain ⟨hL, _, _⟩ := n06_memLp_of_square_le_finiteSum
    (n06CubicGraphFields (fun p => cylinderWeight p.1) φ)
    (K := 125 * δ ^ 2) (by positivity)
    (n06_divergenceOperator_measurable _ _).aestronglyMeasurable hgraph (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
      have hpU : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
      have hpr : p.1 ∈ Icc (0 : ℝ) 1 := by
        simpa only [hl, hr] using Ioo_subset_Icc_self hp.1
      obtain ⟨hA₀, hB₀, hC₀, hAr, hBt, hBr, hCt⟩ := hjet p hpU
      have hn := (isOpen_Ioo.prod isOpen_univ).mem_nhds hpU
      have hd₁ := (cylinderWeight_hasDerivAt p.1).differentiableAt
      have hd : DifferentiableAt ℝ (fun q : PolarPoint => cylinderWeight q.1) p :=
        hd₁.comp p differentiableAt_fst
      have hdθ : angularPartial (fun q : PolarPoint => cylinderWeight q.1) p = 0 :=
        angularPartial_radialHeightField hd₁
      have hdr : |radialPartial (fun q : PolarPoint => cylinderWeight q.1) p| ≤ 1 := by
        change |radialPartial (radialHeightField cylinderWeight) p| ≤ 1
        rw [radialPartial_radialHeightField hd₁, (cylinderWeight_hasDerivAt p.1).deriv]
        exact abs_le.mpr ⟨by linarith [hpr.2], by linarith [hpr.1]⟩
      rw [n06CubicGraphFields_square_sum _ _ _ (cylinderWeight_nonneg hpr)]
      exact n06CubicCoefficients_divergence_sq_le hd
        ((hA.contDiffAt hn).differentiableAt (by simp))
        ((hB.contDiffAt hn).differentiableAt (by simp))
        ((hC.contDiffAt hn).differentiableAt (by simp))
        ((hφ.contDiffAt hn).of_le (by norm_num)) hdθ
        (cylinderWeight_nonneg hpr) (cylinderWeight_le_one hpr) hdr hδ
        hA₀ hB₀ hC₀ hAr hBt hBr hCt)
  exact hL

/-- The same compact weak equation holds for the actual open-strip test.
The first jets and weighted second jets are explicit L2 fields. -/
theorem n06_cubic_pairing_of_openTest
    (hl : K.left m = 0) (hr : K.right m = 1)
    {A B C φ : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hC : ContDiffOn ℝ ∞ C (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |A p| ≤ δ ∧ |B p| ≤ δ ∧ |C p| ≤ δ ∧
        |radialPartial A p| ≤ δ ∧ |angularPartial B p| ≤ δ ∧
        |radialPartial B p| ≤ δ ∧ |angularPartial C p| ≤ δ)
    (u g : CanonicalL2 S K m)
    (hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, g p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u p * divergenceOperator
          (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) ψ p
            ∂canonicalMeasure S K m)
    (hφ : ContDiffOn ℝ ∞ φ (canonicalOpen S K m))
    (hpφ : ∀ p ∈ canonicalOpen S K m, φ (p + (0, Real.pi)) = φ p)
    (hφ₀ : MemLp φ 2 (canonicalMeasure S K m))
    (hφr : MemLp (radialPartial φ) 2 (canonicalMeasure S K m))
    (hφt : MemLp (angularPartial φ) 2 (canonicalMeasure S K m))
    (hgraph : ∀ i, MemLp (n06CubicGraphFields (fun p => cylinderWeight p.1) φ i)
      2 (canonicalMeasure S K m)) :
    (∫ p, g p * φ p ∂canonicalMeasure S K m) =
      ∫ p, u p * divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p
          ∂canonicalMeasure S K m := by
  have hL := n06_cubic_openTest_memLp_of_graph hl hr hδ hA hB hC hjet hφ hgraph
  obtain ⟨hLn, hLlim⟩ :=
    n06_cubic_openTest_cutoff_tendsto hl hr hδ hA hB hC hjet hφ hφ₀ hφr hφt hL
  have hleft := r11b_tendsto_integral_mul_of_L2_tendsto
    (fun n => n06InteriorTestCut_memLp hφ₀ n) hφ₀ (Lp.memLp g)
    (n06InteriorTestCut_tendsto hl hr hφ₀)
  have hright := r11b_tendsto_integral_mul_of_L2_tendsto hLn hL (Lp.memLp u) hLlim
  have hseq : (fun n => ∫ p, n06InteriorTestCut n φ p * g p ∂canonicalMeasure S K m) =
      fun n => ∫ p, divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) (n06InteriorTestCut n φ) p *
          u p ∂canonicalMeasure S K m := by
    funext n
    simpa only [mul_comm] using
      hweak _ (n06InteriorTestCut_canonicalTest_of_open hl hr hφ hpφ n)
  rw [hseq] at hleft
  simpa only [mul_comm] using tendsto_nhds_unique hleft hright

end ContinuousFlexibility.Analysis
