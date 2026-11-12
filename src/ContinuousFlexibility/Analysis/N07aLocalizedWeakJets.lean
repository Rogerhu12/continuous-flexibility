import ContinuousFlexibility.Analysis.N07aCanonicalExtension
import ContinuousFlexibility.Analysis.N07aWeakDivergenceEquation
import ContinuousFlexibility.Analysis.N07aCylinderReconstruction

/-!
# Compact radial localization of every actual canonical weak jet

The compact coefficient makes every test product admissible in the
original canonical interval. Extension by zero therefore introduces no
boundary distributions. An induction using the genuine first product
rule gives the full cylinder weak jet tower and its smooth representative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_cylinderWeak_refl (u : CylinderL2) : HasWeakMixedDerivative u u 0 0 := by
  intro φ _
  simp only [spaces_mixedDerivative_zero, zero_add, pow_zero, one_mul]

theorem n07a_cylinderWeak_add {f g u v : CylinderL2} {a b : ℕ}
    (hfg : HasWeakMixedDerivative f g a b) (huv : HasWeakMixedDerivative u v a b) :
    HasWeakMixedDerivative (f + u) (g + v) a b := by
  exact (mem_weakMixedDerivativeGraph a b _).mp
    ((weakMixedDerivativeGraph a b).add_mem
      ((mem_weakMixedDerivativeGraph a b (f, g)).mpr hfg)
      ((mem_weakMixedDerivativeGraph a b (u, v)).mpr huv))

theorem n07a_cylinderWeak_comp {f g h : CylinderL2} {a b c d : ℕ}
    (hfg : HasWeakMixedDerivative f g a b) (hgh : HasWeakMixedDerivative g h c d) :
    HasWeakMixedDerivative f h (a + c) (b + d) := by
  intro φ hφ
  rw [hgh φ hφ, hfg (mixedDerivative c d φ) (hφ.mixedDerivative c d),
    n07a_mixedDerivative_mixedDerivative hφ.1, ← mul_assoc, ← pow_add]
  congr 2
  omega

/-- The weak product rule transferred to the whole cylinder. Compact
radial support is used on the coefficient, not presumed of the unknown. -/
theorem n07a_canonicalLocalization_first {χ : PolarPoint → ℝ}
    (hχ : CanonicalTest S K m χ) (j : Fin 2) {u du : CanonicalL2 S K m}
    (hu : N07aWeakCanonicalMixedDerivative S K m u du
      (n07aFirstOrder j).1 (n07aFirstOrder j).2) :
    HasWeakMixedDerivative
      (n07aCanonicalExtension (n07aSmoothCanonicalMul χ hχ.1 u))
      (n07aCanonicalExtension (n07aSmoothCanonicalMul χ hχ.1 du) +
        n07aCanonicalExtension
          (n07aSmoothCanonicalMul
            (mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ)
            (contDiff_mixedDerivative hχ.1 _ _) u))
      (n07aFirstOrder j).1 (n07aFirstOrder j).2 := by
  intro φ hφ
  let dχ := mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ
  let dφ := mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 φ
  have hdχ : CanonicalTest S K m dχ :=
    n07a_canonicalTest_mixedDerivative hχ _ _
  have ht : CanonicalTest S K m (fun p => χ p * φ p) := by
    simpa only [mul_comm] using n07a_canonicalTest_mul hχ hφ.1 hφ.2.1
  have ht₁ : CanonicalTest S K m (fun p => dχ p * φ p) := by
    simpa only [mul_comm] using n07a_canonicalTest_mul hdχ hφ.1 hφ.2.1
  have ht₂ : CanonicalTest S K m (fun p => χ p * dφ p) := by
    simpa only [mul_comm] using n07a_canonicalTest_mul hχ
      (hφ.mixedDerivative _ _).1 (hφ.mixedDerivative _ _).2.1
  have hi₁ : Integrable (fun p => u p * (dχ p * φ p)) (canonicalMeasure S K m) :=
    (Lp.memLp u).integrable_mul (n07a_canonicalTest_memLp ht₁)
  have hi₂ : Integrable (fun p => u p * (χ p * dφ p)) (canonicalMeasure S K m) :=
    (Lp.memLp u).integrable_mul (n07a_canonicalTest_memLp ht₂)
  have he := hu (fun p => χ p * φ p) ht
  rw [n07aFirstOrder_sum, pow_one, neg_one_mul,
    n07a_mixedDerivative_first_mul hχ.1 hφ.1] at he
  change (∫ p, du p * (χ p * φ p) ∂canonicalMeasure S K m) =
    -(∫ p, u p * (dχ p * φ p + χ p * dφ p) ∂canonicalMeasure S K m) at he
  simp_rw [mul_add] at he
  rw [integral_add hi₁ hi₂] at he
  rw [← cylinderTestPairing_apply φ hφ.memLp, map_add,
    cylinderTestPairing_apply, cylinderTestPairing_apply,
    n07aCanonicalExtension_pairing, n07aCanonicalExtension_pairing,
    n07aCanonicalExtension_pairing, n07aFirstOrder_sum, pow_one, neg_one_mul]
  simp only [n07aSmoothCanonicalMul_pairing]
  linarith only [he]

private theorem n07a_canonicalLocalization_step (a b : ℕ) (j : Fin 2)
    (ih : ∀ (χ : PolarPoint → ℝ) (hχ : CanonicalTest S K m χ)
      (u : CanonicalL2 S K m), (∀ n, N07aCanonicalNormalRegular S K m u n) →
      ∃ v : CylinderL2, HasWeakMixedDerivative
        (n07aCanonicalExtension (n07aSmoothCanonicalMul χ hχ.1 u)) v a b) :
    ∀ (χ : PolarPoint → ℝ) (hχ : CanonicalTest S K m χ)
      (u : CanonicalL2 S K m), (∀ n, N07aCanonicalNormalRegular S K m u n) →
      ∃ v : CylinderL2, HasWeakMixedDerivative
        (n07aCanonicalExtension (n07aSmoothCanonicalMul χ hχ.1 u)) v
          (a + (n07aFirstOrder j).1) (b + (n07aFirstOrder j).2) := by
  intro χ hχ u hu
  obtain ⟨du, hdu⟩ := hu (n07aFirstOrder j).1 (n07aFirstOrder j).1 le_rfl
    (n07aFirstOrder j).2
  have hdureg : ∀ n, N07aCanonicalNormalRegular S K m du n :=
    fun n => (hu (n + (n07aFirstOrder j).1)).derivative hdu
  obtain ⟨v, hv⟩ := ih χ hχ du hdureg
  obtain ⟨w, hw⟩ := ih
    (mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ)
    (n07a_canonicalTest_mixedDerivative hχ _ _) u hu
  refine ⟨v + w, ?_⟩
  simpa only [Nat.add_comm] using
    n07a_cylinderWeak_comp (n07a_canonicalLocalization_first hχ j hdu)
      (n07a_cylinderWeak_add hv hw)

/-- Every canonical weak mixed derivative survives compact radial
localization and extension to the complete cylinder. -/
theorem n07a_canonicalLocalization_allMixed (a b : ℕ) :
    ∀ (χ : PolarPoint → ℝ) (hχ : CanonicalTest S K m χ)
      (u : CanonicalL2 S K m), (∀ n, N07aCanonicalNormalRegular S K m u n) →
      ∃ v : CylinderL2, HasWeakMixedDerivative
        (n07aCanonicalExtension (n07aSmoothCanonicalMul χ hχ.1 u)) v a b := by
  induction a with
  | zero =>
    induction b with
    | zero =>
      intro χ hχ u _
      exact ⟨_, n07a_cylinderWeak_refl _⟩
    | succ b ih =>
      simpa [n07aFirstOrder] using n07a_canonicalLocalization_step 0 b (1 : Fin 2) ih
  | succ a ih =>
    simpa [n07aFirstOrder] using n07a_canonicalLocalization_step a b (0 : Fin 2) ih

/-- A compactly localized canonical weak solution has a genuine smooth
periodic representative agreeing with the original L² class. -/
theorem n07a_exists_smooth_localizedCanonical {χ : PolarPoint → ℝ}
    (hχ : CanonicalTest S K m χ) (u : CanonicalL2 S K m)
    (hu : ∀ n, N07aCanonicalNormalRegular S K m u n) :
    ∃ v : PolarPoint → ℝ, ContDiff ℝ ∞ v ∧ Function.Periodic v (0, Real.pi) ∧
      v =ᵐ[canonicalMeasure S K m] (fun p => χ p * u p) := by
  choose d hd using fun a b => n07a_canonicalLocalization_allMixed a b χ hχ u hu
  obtain ⟨v, hv, hvp, hveq, _⟩ := n07a_exists_smooth_cylinderRepresentative
    (n07aCanonicalExtension (n07aSmoothCanonicalMul χ hχ.1 u)) d hd
  have hzero : d 0 0 = n07aCanonicalExtension (n07aSmoothCanonicalMul χ hχ.1 u) :=
    hasWeakMixedDerivative_unique (hd 0 0) (n07a_cylinderWeak_refl _)
  have he := hveq 0 0
  rw [spaces_mixedDerivative_zero, hzero] at he
  have hmeasure : canonicalMeasure S K m ≤ materialCylinderMeasure := by
    rw [n07a_canonicalMeasure_eq_cylinder_restrict]
    exact Measure.restrict_le_self
  exact ⟨v, hv, hvp, (he.filter_mono (ae_mono hmeasure)).trans
    ((n07aCanonicalExtension_restrict_ae _).trans (n07aSmoothCanonicalMul_ae χ hχ.1 u))⟩

end ContinuousFlexibility.Analysis
