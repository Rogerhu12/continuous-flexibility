import ContinuousFlexibility.Analysis.N07aCanonicalWeakJets
import ContinuousFlexibility.Analysis.SpacesCylinderIntegration

/-!
# Classical test jets in the actual canonical weak graph

A canonical test is a genuine periodic cylinder test. Its compact radial
support removes the difference between the full cylinder measure and the
canonical interval measure. Classical integration by parts therefore
gives the same weak relation used by the frozen volume graph.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonicalTest_zero_outside {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) {p : PolarPoint} (hp : p.1 ∉ Ioo (K.left m) (K.right m)) :
    φ p = 0 := by
  obtain ⟨_, _, J, _, hJ, hzero⟩ := hφ
  exact hzero p.1 (fun hr => hp (hJ hr)) p.2

theorem n07a_canonicalTest_isCylinderTest {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) : IsCylinderTest φ := by
  refine ⟨hφ.1, hφ.2.1, |K.left m| + |K.right m| + 1, by positivity, ?_⟩
  intro p hp
  apply n07a_canonicalTest_zero_outside hφ
  intro hr
  have hlt : |p.1| < |K.left m| + |K.right m| + 1 := by
    rw [abs_lt]
    constructor
    · linarith [hr.1, neg_le_abs (K.left m), abs_nonneg (K.right m)]
    · linarith [hr.2, le_abs_self (K.right m), abs_nonneg (K.left m)]
  exact (not_lt_of_ge hp) hlt

theorem n07a_canonicalMeasure_eq_cylinder_restrict (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) :
    canonicalMeasure S K m =
      materialCylinderMeasure.restrict (Ioo (K.left m) (K.right m) ×ˢ univ) := by
  rw [canonicalMeasure, materialCylinderMeasure,
    Measure.restrict_restrict (measurableSet_Ioo.prod MeasurableSet.univ)]
  congr 1
  ext p
  simp only [mem_prod, mem_inter_iff, mem_univ, and_true, true_and]

theorem n07a_canonicalIntegral_eq_cylinder {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : PolarPoint → E}
    (hF : ∀ p : PolarPoint, p.1 ∉ Ioo (K.left m) (K.right m) → F p = 0) :
    (∫ p, F p ∂canonicalMeasure S K m) = ∫ p, F p ∂materialCylinderMeasure := by
  rw [n07a_canonicalMeasure_eq_cylinder_restrict]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  exact hF p (fun hr => hp ⟨hr, mem_univ _⟩)

/-- Every classical canonical test jet represents its actual mixed weak derivative. -/
theorem n07a_canonicalTest_weakMixed {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) (a b : ℕ) :
    N07aWeakCanonicalMixedDerivative S K m
      ((n07a_canonicalTest_memLp hφ).toLp φ)
      ((n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ a b)).toLp
        (mixedDerivative a b φ)) a b := by
  intro ψ hψ
  have hφd := n07a_canonicalTest_mixedDerivative hφ a b
  calc
    (∫ p, (n07a_canonicalTest_memLp hφd).toLp (mixedDerivative a b φ) p * ψ p
        ∂canonicalMeasure S K m) =
        ∫ p, mixedDerivative a b φ p * ψ p ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (n07a_canonicalTest_memLp hφd)] with p hp
      rw [hp]
    _ = ∫ p, mixedDerivative a b φ p * ψ p ∂materialCylinderMeasure := by
      apply n07a_canonicalIntegral_eq_cylinder
      intro p hp
      rw [n07a_canonicalTest_zero_outside hφd hp, zero_mul]
    _ = (-1 : ℝ) ^ (a + b) *
        ∫ p, φ p * mixedDerivative a b ψ p ∂materialCylinderMeasure :=
      spaces_integral_mixedDerivative_mul hφ.1 hφ.2.1 (n07a_canonicalTest_isCylinderTest hψ) a b
    _ = (-1 : ℝ) ^ (a + b) *
        ∫ p, φ p * mixedDerivative a b ψ p ∂canonicalMeasure S K m := by
      congr 1
      symm
      apply n07a_canonicalIntegral_eq_cylinder
      intro p hp
      rw [n07a_canonicalTest_zero_outside hφ hp, zero_mul]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (n07a_canonicalTest_memLp hφ)] with p hp
      rw [hp]

theorem n07a_canonicalTest_weakAngular {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) (k : ℕ) :
    WeakCanonicalAngularDerivative S K m
      ((n07a_canonicalTest_memLp hφ).toLp φ)
      ((n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ 0 k)).toLp
        (mixedDerivative 0 k φ)) k :=
  (n07a_weakCanonicalMixed_zero_radial_iff _ _ k).mp (n07a_canonicalTest_weakMixed hφ 0 k)

end ContinuousFlexibility.Analysis
