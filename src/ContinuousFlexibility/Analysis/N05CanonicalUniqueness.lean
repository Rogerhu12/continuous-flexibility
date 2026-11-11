import ContinuousFlexibility.Analysis.N05CanonicalGraph
import ContinuousFlexibility.Analysis.CylinderTestPeriodization
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Separation by the actual canonical tests

A compact planar test supported in the open fundamental rectangle can be
periodized without changing it on that rectangle. The local distribution
uniqueness theorem therefore separates canonical L² classes.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology

theorem n05CanonicalMeasure_eq_open_rectangle (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) :
    canonicalMeasure S K m =
      volume.restrict (Ioo (K.left m) (K.right m) ×ˢ Ioo (0 : ℝ) Real.pi) := by
  rw [n05CanonicalMeasure_eq_prod]
  have ha : angleMeasure = (volume : Measure ℝ).restrict (Ioo (0 : ℝ) Real.pi) :=
    (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
  rw [ha, Measure.prod_restrict]

theorem n05CanonicalTest_of_periodization {S : PhysicalSpacesData} {K : CanonicalData S}
    {m : ℕ} {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (K.left m) (K.right m) ×ˢ Ioo (0 : ℝ) Real.pi) :
    CanonicalTest S K m (cylinderTestPeriodization φ) := by
  have ht := isCylinderTest_cylinderTestPeriodization hφ hc
  refine ⟨ht.1, ht.2.1, Prod.fst '' tsupport φ, hc.image continuous_fst, ?_, ?_⟩
  · rintro r ⟨p, hp, rfl⟩
    exact (hs hp).1
  · intro r hr θ
    unfold cylinderTestPeriodization
    have hz (k : ℤ) : φ (cylinderAngularShift k (r, θ)) = 0 := by
      by_contra hk
      exact hr ⟨cylinderAngularShift k (r, θ), subset_tsupport φ hk, rfl⟩
    simp only [hz, tsum_zero]

theorem n05CanonicalPeriodization_eq {S : PhysicalSpacesData} {K : CanonicalData S}
    {m : ℕ} {φ : PolarPoint → ℝ}
    (hs : tsupport φ ⊆ Ioo (K.left m) (K.right m) ×ˢ Ioo (0 : ℝ) Real.pi)
    (p : PolarPoint) (hp : p.2 ∈ Ioc (0 : ℝ) Real.pi) :
    cylinderTestPeriodization φ p = φ p := by
  have hz (k : ℤ) (hk : k ≠ 0) : φ (cylinderAngularShift k p) = 0 := by
    by_contra hφ
    have hθ := (hs (subset_tsupport φ hφ)).2
    change 0 < p.2 + k • Real.pi ∧ p.2 + k • Real.pi < Real.pi at hθ
    simp only [zsmul_eq_mul] at hθ
    have hk' : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases hk' with hneg | hpos
    · have hneg' : (k : ℝ) ≤ -1 := by exact_mod_cast hneg
      have hm := mul_le_mul_of_nonneg_right hneg' Real.pi_pos.le
      linarith only [hθ.1, hp.2, hm]
    · have hpos' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpos
      have hm := mul_le_mul_of_nonneg_right hpos' Real.pi_pos.le
      linarith only [hθ.2, hp.1, hm]
  calc
    cylinderTestPeriodization φ p = φ (cylinderAngularShift 0 p) := tsum_eq_single 0 hz
    _ = φ p := by
      change φ (p.1, p.2 + (0 : ℤ) • Real.pi) = φ p
      simp only [zero_zsmul, add_zero, Prod.mk.eta]

theorem n05CanonicalL2_eq_zero_of_test (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CanonicalL2 S K m)
    (hu : ∀ φ : PolarPoint → ℝ, CanonicalTest S K m φ →
      (∫ p, u p * φ p ∂canonicalMeasure S K m) = 0) : u = 0 := by
  let U : Set PolarPoint := Ioo (K.left m) (K.right m) ×ˢ Ioo (0 : ℝ) Real.pi
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hi : LocallyIntegrableOn (u : PolarPoint → ℝ) U (canonicalMeasure S K m) :=
    ((Lp.memLp u).integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn U
  have hz : ∀ᵐ p ∂canonicalMeasure S K m, p ∈ U → u p = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hi
    intro φ hφ hc hs
    have ht : CanonicalTest S K m (cylinderTestPeriodization φ) :=
      n05CanonicalTest_of_periodization hφ hc hs
    calc
      (∫ p, φ p • u p ∂canonicalMeasure S K m) =
          ∫ p, u p * cylinderTestPeriodization φ p ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        have ha : ∀ᵐ p ∂canonicalMeasure S K m,
            p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
          ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
        filter_upwards [ha] with p hp
        rw [n05CanonicalPeriodization_eq hs p hp.2]
        simp only [smul_eq_mul, mul_comm]
      _ = 0 := hu _ ht
  have ha : ∀ᵐ p ∂canonicalMeasure S K m, p ∈ U := by
    rw [n05CanonicalMeasure_eq_open_rectangle]
    exact ae_restrict_mem hU.measurableSet
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hz, ha] with p hp hpu
  exact hp hpu

theorem n05WeakCanonicalAngularDerivative_unique {S : PhysicalSpacesData}
    {K : CanonicalData S} {m : ℕ} {f d e : CanonicalL2 S K m} {j : ℕ}
    (hd : WeakCanonicalAngularDerivative S K m f d j)
    (he : WeakCanonicalAngularDerivative S K m f e j) : d = e := by
  apply sub_eq_zero.mp
  apply n05CanonicalL2_eq_zero_of_test S K m (d - e)
  intro φ hφ
  let P := n05CanonicalTestPairing S K m φ (n05CanonicalTest_memLp hφ)
  calc
    (∫ p, (d - e) p * φ p ∂canonicalMeasure S K m) = P (d - e) :=
      (n05CanonicalTestPairing_apply S K m φ _ (d - e)).symm
    _ = P d - P e := P.map_sub d e
    _ = (∫ p, d p * φ p ∂canonicalMeasure S K m) -
        (∫ p, e p * φ p ∂canonicalMeasure S K m) := by
      rw [n05CanonicalTestPairing_apply, n05CanonicalTestPairing_apply]
    _ = 0 := sub_eq_zero.mpr ((hd φ hφ).trans (he φ hφ).symm)

end ContinuousFlexibility.Statements
