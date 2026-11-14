module

public import ContinuousFlexibility.Analysis.N06CubicCutoffLp
public import ContinuousFlexibility.Analysis.N06LocalClosedCubicPairing
public import ContinuousFlexibility.Analysis.N06N05PositiveCubicSourceMap
public import ContinuousFlexibility.Radial.R11bWeakNormalLimit

/-!
# Closed-cylinder tests for the same positive cubic source map

The compact-test identity of the already constructed source map extends
by the actual cutoff convergence. The map, its original source level,
and the height component of the same N05 inverse are unchanged. Only the
test is extended from a closed-cylinder neighborhood; the divided
coefficients need smoothness and bounded first jets only on the open
cylinder. Neither endpoint vanishing nor evenness of the test is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The original compact distributional equation determines the pairing
with every smooth periodic closed-cylinder test. Both actual test
sequences converge in the same canonical L² space. -/
theorem n06_cubic_pairing_closed_of_compact
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
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
    (hφ : ContDiff ℝ ∞ φ) (hpφ : Function.Periodic φ (0, Real.pi)) :
    (∫ p, g p * φ p ∂canonicalMeasure S K m) =
      ∫ p, u p * divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p
        ∂canonicalMeasure S K m := by
  have hφLp := n06_memLp_canonical_of_continuous (S := S) (K := K) m hφ.continuous
  obtain ⟨hL, hLn, hLlim⟩ := n06_cubic_closedTest_cutoff_tendsto hl hr hδ hA hB hC hjet hφ
  have hleft := r11b_tendsto_integral_mul_of_L2_tendsto
    (fun n => n06InteriorTestCut_memLp hφLp n) hφLp (Lp.memLp g)
    (n06InteriorTestCut_tendsto hl hr hφLp)
  have hright := r11b_tendsto_integral_mul_of_L2_tendsto hLn hL (Lp.memLp u) hLlim
  have hseq : (fun n => ∫ p, n06InteriorTestCut n φ p * g p ∂canonicalMeasure S K m) =
      fun n => ∫ p, divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) (n06InteriorTestCut n φ) p *
          u p ∂canonicalMeasure S K m := by
    funext n
    simpa only [mul_comm] using
      hweak _ (n06InteriorTestCut_canonicalTest hl hr hφ hpφ n)
  rw [hseq] at hleft
  simpa only [mul_comm] using tendsto_nhds_unique hleft hright

private theorem positive_first_jets
    {S : PhysicalSpacesData} {K : CanonicalData S} {b : ℕ}
    {scale : ℕ → ℝ} {δ : ℝ} {A B C : ℕ → PolarPoint → ℝ}
    (h : N06PositiveCubicControl K b scale δ A B C)
    (m : ℕ) (hm : K.positive m = true) (p : PolarPoint) (hp : p ∈ canonicalOpen S K m) :
    |A m p| ≤ δ * scale m ∧ |B m p| ≤ δ * scale m ∧ |C m p| ≤ δ * scale m ∧
      |radialPartial (A m) p| ≤ δ * scale m ∧ |angularPartial (B m) p| ≤ δ * scale m ∧
      |radialPartial (B m) p| ≤ δ * scale m ∧ |angularPartial (C m) p| ≤ δ * scale m := by
  have hzero := h.jets m hm 0 0 (by omega) p hp
  have hrad := h.jets m hm 1 0 (by omega) p hp
  have hang := h.jets m hm 0 1 (by omega) p hp
  simp only [spaces_mixedDerivative_zero] at hzero
  have hR (f : PolarPoint → ℝ) (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m)) :
      radialPartial f p = mixedDerivative 1 0 f p := by
    simpa only [spaces_mixedDerivative_zero, Nat.zero_add] using
      mixedDerivative_radialPartial (isOpen_Ioo.prod isOpen_univ) hf 0 0 hp
  have hT (f : PolarPoint → ℝ) (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m)) :
      angularPartial f p = mixedDerivative 0 1 f p := by
    simpa only [spaces_mixedDerivative_zero, Nat.zero_add] using
      mixedDerivative_angularPartial (isOpen_Ioo.prod isOpen_univ) hf 0 0 hp
  refine ⟨hzero.1, hzero.2.1, hzero.2.2, ?_, ?_, ?_, ?_⟩
  · rw [hR _ (h.a_smooth m hm)]
    exact hrad.1
  · rw [hT _ (h.b_smooth m hm)]
    exact hang.2.1
  · rw [hR _ (h.b_smooth m hm)]
    exact hrad.2.1
  · rw [hT _ (h.c_smooth m hm)]
    exact hang.2.2

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- The very same map supplied by the N05 positive cubic construction
satisfies the closed-cylinder identity. Its compact identity is the one
already proved for `M`; no graph representatives are selected again. -/
theorem n06N05_positiveCubicSourceMap_closed_pairing
    {S : PhysicalSpacesData} {K : CanonicalData S} {Vol : VolumeModelData S K}
    {b : ℕ} {B : CanonicalDomainData S K Vol b}
    {scale : ℕ → ℝ} {δ : ℝ} {A Bc Cc : ℕ → PolarPoint → ℝ}
    (hcoeff : N06PositiveCubicControl K b scale δ A Bc Cc)
    (M : Vol.level (3 / 4 : ℝ) 0 b →L[ℝ] Vol.level (3 / 4 : ℝ) 0 b)
    (hM : ∀ F n ψ, CanonicalTest S K n ψ →
      (∫ p, Vol.forget (3 / 4 : ℝ) 0 b (M F) n p * ψ p ∂canonicalMeasure S K n) =
        ∫ p, n06InverseCanonicalHeight B F n p *
          n06PositiveCubicTestOperator K A Bc Cc n ψ p ∂canonicalMeasure S K n)
    (F : Vol.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.positive m = true)
    (hl : K.left m = 0) (hr : K.right m = 1)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpφ : Function.Periodic φ (0, Real.pi)) :
    (∫ p, Vol.forget (3 / 4 : ℝ) 0 b (M F) m p * φ p ∂canonicalMeasure S K m) =
      ∫ p, n06InverseCanonicalHeight B F m p *
        n06PositiveCubicTestOperator K A Bc Cc m φ p ∂canonicalMeasure S K m := by
  have hmid : ((1 / 2 : ℝ), (0 : ℝ)) ∈ canonicalOpen S K m := by
    simp only [canonicalOpen, hl, hr, mem_prod, mem_Ioo, mem_univ, and_true]
    norm_num
  have hδm : 0 ≤ δ * scale m :=
    (abs_nonneg (A m ((1 / 2 : ℝ), 0))).trans (positive_first_jets hcoeff m hm _ hmid).1
  rw [n06PositiveCubicTestOperator, if_pos hm]
  apply n06_cubic_pairing_closed_of_compact hl hr hδm
    (hcoeff.a_smooth m hm) (hcoeff.b_smooth m hm) (hcoeff.c_smooth m hm)
    (positive_first_jets hcoeff m hm)
    (n06InverseCanonicalHeight B F m) (Vol.forget (3 / 4 : ℝ) 0 b (M F) m)
    ?_ hφ hpφ
  intro ψ hψ
  simpa only [n06PositiveCubicTestOperator, if_pos hm] using hM F m ψ hψ

/-- Only the actual test is extended. The original coefficients retain
exactly their open-strip hypotheses, and the same map `M` and inverse
height occur in the resulting pairing. -/
theorem n06N05_positiveCubicSourceMap_local_closed_pairing
    {S : PhysicalSpacesData} {K : CanonicalData S} {Vol : VolumeModelData S K}
    {b : ℕ} {B : CanonicalDomainData S K Vol b}
    {scale : ℕ → ℝ} {δ : ℝ} {A Bc Cc : ℕ → PolarPoint → ℝ}
    (hcoeff : N06PositiveCubicControl K b scale δ A Bc Cc)
    (M : Vol.level (3 / 4 : ℝ) 0 b →L[ℝ] Vol.level (3 / 4 : ℝ) 0 b)
    (hM : ∀ F n ψ, CanonicalTest S K n ψ →
      (∫ p, Vol.forget (3 / 4 : ℝ) 0 b (M F) n p * ψ p ∂canonicalMeasure S K n) =
        ∫ p, n06InverseCanonicalHeight B F n p *
          n06PositiveCubicTestOperator K A Bc Cc n ψ p ∂canonicalMeasure S K n)
    (F : Vol.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.positive m = true)
    (hl : K.left m = 0) (hr : K.right m = 1)
    {l r : ℝ} (hl₀ : l < 0) (hr₁ : 1 < r) {φ : PolarPoint → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ (Ioo l r ×ˢ univ))
    (hpφ : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), φ (p + (0, Real.pi)) = φ p) :
    (∫ p, Vol.forget (3 / 4 : ℝ) 0 b (M F) m p * φ p ∂canonicalMeasure S K m) =
      ∫ p, n06InverseCanonicalHeight B F m p *
        n06PositiveCubicTestOperator K A Bc Cc m φ p ∂canonicalMeasure S K m := by
  obtain ⟨ψ, hψ, hpψ, hsame⟩ :=
    n06_exists_smooth_periodic_closed_strip_extension hl₀ hr₁ hφ hpφ
  have hpiece : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    rw [canonicalMeasure, hl, hr]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    exact ⟨Ioo_subset_Icc_self hp.1, mem_univ _⟩
  calc
    _ = ∫ p, Vol.forget (3 / 4 : ℝ) 0 b (M F) m p * ψ p ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [hpiece] with p hp
      rw [(hsame p hp).eq_of_nhds]
    _ = ∫ p, n06InverseCanonicalHeight B F m p *
        n06PositiveCubicTestOperator K A Bc Cc m ψ p ∂canonicalMeasure S K m :=
      n06N05_positiveCubicSourceMap_closed_pairing hcoeff M hM F m hm hl hr hψ hpψ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hpiece] with p hp
      simp only [n06PositiveCubicTestOperator, if_pos hm]
      rw [n06_divergenceOperator_input_congr_germ _ (hsame p hp)]

end ContinuousFlexibility.Statements
