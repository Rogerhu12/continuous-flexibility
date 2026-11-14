module

public import ContinuousFlexibility.Analysis.N06PositiveCubicSource
public import ContinuousFlexibility.Analysis.N06UnitWeakCubicSource

/-!
# The actual weak equation of the all-piece positive cubic source

The completed unit-cylinder pairing is applied on the positive pieces.
Both the perturbation and its source vanish on the negative pieces.
Thus the original all-piece source is identified by canonical tests,
without requiring any of its graph representatives to be smooth.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def n06PositiveCubicTestOperator
    {S : PhysicalSpacesData} (K : CanonicalData S) (A B C : ℕ → PolarPoint → ℝ)
    (m : ℕ) (φ : PolarPoint → ℝ) : PolarPoint → ℝ :=
  if K.positive m = true then
    divergenceOperator (n06CubicCoefficients (fun p => cylinderWeight p.1) (A m) (B m) (C m)) φ
  else fun _ => 0

theorem N06PositiveCubicControl.testOperator_memLp
    {S : PhysicalSpacesData} {K : CanonicalData S} {b : ℕ}
    {scale : ℕ → ℝ} {δ : ℝ} {A B C : ℕ → PolarPoint → ℝ}
    (h : N06PositiveCubicControl K b scale δ A B C)
    (hl : ∀ m, K.positive m = true → K.left m = 0)
    (hr : ∀ m, K.positive m = true → K.right m = 1)
    (m : ℕ) (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ) :
    MemLp (n06PositiveCubicTestOperator K A B C m φ) 2 (canonicalMeasure S K m) := by
  by_cases hm : K.positive m = true
  · have hstrip : canonicalOpen S K m = Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
      simp only [canonicalOpen, hl m hm, hr m hm]
    have hA : ContDiffOn ℝ ∞ (A m) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
      simpa only [hstrip] using h.a_smooth m hm
    have hB : ContDiffOn ℝ ∞ (B m) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
      simpa only [hstrip] using h.b_smooth m hm
    have hC : ContDiffOn ℝ ∞ (C m) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
      simpa only [hstrip] using h.c_smooth m hm
    have hd : ContDiff ℝ ∞ (fun p : PolarPoint => cylinderWeight p.1 ^ 3) := by
      change ContDiff ℝ ∞ (fun p : PolarPoint => (p.1 * (1 - p.1)) ^ 3)
      exact (contDiff_fst.mul (contDiff_const.sub contDiff_fst)).pow 3
    have htest := n06_unit_divergence_test_contDiff
      (n06CubicCoefficients (fun p => cylinderWeight p.1) (A m) (B m) (C m))
      (hd.contDiffOn.mul hA) (hd.contDiffOn.mul hB) (hd.contDiffOn.mul hC)
      ((n06_unitCanonicalTest_iff (hl m hm) (hr m hm) φ).mpr hφ)
    rw [n06PositiveCubicTestOperator, if_pos hm]
    exact n06_memLp_canonical_of_continuous m htest.continuous
  · rw [n06PositiveCubicTestOperator, if_neg hm]
    exact MemLp.zero

/-- The material-normalized source built from the actual graph fields is
the weak cubic divergence of the original physical canonical height. -/
theorem n06_positiveCubicSource_pairing
    {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {Vol : VolumeModelData S K} (hVol : IsVolumeModel T S K Vol)
    {β loss : ℝ} {b : ℕ} {F : Vol.level β 0 b} {W : Vol.level β (-loss) b}
    {a c V : ℕ → ℝ → ℝ} {κ : ℕ → ℝ}
    (P : N06PositiveWeakGraphFamily T K β loss F.val W.val a c V κ)
    {scale : ℕ → ℝ} {δ : ℝ} {A B C : ℕ → PolarPoint → ℝ}
    (hcoeff : N06PositiveCubicControl K b scale δ A B C)
    (hl : ∀ m, K.positive m = true → K.left m = 0)
    (hr : ∀ m, K.positive m = true → K.right m = 1)
    (G : Vol.level β 0 b)
    (hG : ∀ m, (Vol.forget β 0 b G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => ∑ i : Fin 5, n06PositiveCubicMultipliers K A B C i m p *
        n06PositivePhysicalGraphFields P i m 0 p) :
    ∀ m φ, CanonicalTest S K m φ →
      (∫ p, Vol.forget β 0 b G m p * φ p ∂canonicalMeasure S K m) =
        ∫ p, Vol.forget β (-loss) b W m p *
          n06PositiveCubicTestOperator K A B C m φ p ∂canonicalMeasure S K m := by
  have hW : W.val ∈ canonicalVolumeGraph S K b := by
    rw [← hVol.1 β (-loss) b]
    exact W.property
  intro m φ hφ
  by_cases hm : K.positive m = true
  · have hstrip : canonicalOpen S K m = Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
      simp only [canonicalOpen, hl m hm, hr m hm]
    have hA : ContDiffOn ℝ ∞ (A m) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
      simpa only [hstrip] using hcoeff.a_smooth m hm
    have hB : ContDiffOn ℝ ∞ (B m) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
      simpa only [hstrip] using hcoeff.b_smooth m hm
    have hC : ContDiffOn ℝ ∞ (C m) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
      simpa only [hstrip] using hcoeff.c_smooth m hm
    have hpA : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), A m (p + (0, Real.pi)) = A m p := by
      simpa only [hstrip] using hcoeff.a_periodic m hm
    have hpB : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), B m (p + (0, Real.pi)) = B m p := by
      simpa only [hstrip] using hcoeff.b_periodic m hm
    have hpC : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), C m (p + (0, Real.pi)) = C m p := by
      simpa only [hstrip] using hcoeff.c_periodic m hm
    have hpair := (P m hm).cubic_pairing (hl m hm) (hr m hm)
      (n06MaterialJetRow_reflection β (-loss) W.val hW m)
      (n06MaterialJetRow_weak β (-loss) W.val hW m) hA hB hC hpA hpB hpC hφ
    have hfield : (Vol.forget β 0 b G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => ∑ i : Fin 5,
          n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) (A m) (B m) (C m) i p *
            (P m hm).field i 0 p := by
      simpa only [n06PositiveCubicMultipliers, if_pos hm,
        n06PositivePhysicalGraphFields, dif_pos hm] using hG m
    calc
      _ = ∫ p, (∑ i : Fin 5,
          n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) (A m) (B m) (C m) i p *
            (P m hm).field i 0 p) * φ p ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hfield] with p hp
        rw [hp]
      _ = _ := by
        rw [← hpair, n06MaterialJetRow_zero_eq_forget hVol β (-loss) b W m]
        simp only [n06PositiveCubicTestOperator, if_pos hm]
  · have hzero : (Vol.forget β 0 b G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun _ => 0 := by
      simpa only [n06PositiveCubicMultipliers, if_neg hm, zero_mul,
        Finset.sum_const_zero] using hG m
    calc
      (∫ p, Vol.forget β 0 b G m p * φ p ∂canonicalMeasure S K m) = 0 := by
        have heq : (fun p => Vol.forget β 0 b G m p * φ p) =ᵐ[canonicalMeasure S K m]
            fun _ => (0 : ℝ) := by
          filter_upwards [hzero] with p hp
          rw [hp, zero_mul]
        exact (integral_congr_ae heq).trans (integral_zero _ _)
      _ = _ := by simp only [n06PositiveCubicTestOperator, if_neg hm, mul_zero, integral_zero]

end ContinuousFlexibility.Analysis
