import ContinuousFlexibility.Analysis.N07aAngularRadialRecovery
import ContinuousFlexibility.Analysis.N07aAngularIntervalRestriction
import ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficients

/-!
# All angular orders of the recovered first normal derivative

Differentiating the actual second-order weak identity only differentiates
its compact test. A radial cutoff commutes with these angular derivatives.
Consequently the recovered graph has every angular order, and restriction
where the cutoff is one recovers the original solution on a smaller strip.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- Angular differentiation preserves the true rough second-order equation. -/
theorem N07aCanonicalSecondPrimitiveEquation.angular
    {v h g vk hk gk : CanonicalL2 S K m} {k : ℕ}
    (heq : N07aCanonicalSecondPrimitiveEquation v h g)
    (hv : N07aWeakCanonicalMixedDerivative S K m v vk 0 k)
    (hh : N07aWeakCanonicalMixedDerivative S K m h hk 0 k)
    (hg : N07aWeakCanonicalMixedDerivative S K m g gk 0 k) :
    N07aCanonicalSecondPrimitiveEquation vk hk gk := by
  intro φ hφ
  have ht := heq _ (n07a_canonicalTest_mixedDerivative hφ 0 k)
  have hv' := hv _ (n07a_canonicalTest_mixedDerivative hφ 2 0)
  have hh' := hh _ (n07a_canonicalTest_mixedDerivative hφ 1 0)
  have hg' := hg φ hφ
  simp only [n07a_mixedDerivative_mixedDerivative hφ.1, zero_add, add_zero] at ht hv' hh' hg'
  have hs := congrArg (fun x : ℝ => (-1 : ℝ) ^ k * x) ht
  simp only [mul_add, mul_neg] at hs
  linarith only [hv', hh', hg', hs]

/-- Multiplication by an actual smooth radial cutoff commutes with every
weak angular derivative in the prescribed canonical graph. -/
theorem n07a_weakAngular_radialCutoff {ξ : ℝ → ℝ}
    (hξ : CanonicalTest S K m (fun p => ξ p.1))
    {u uk : CanonicalL2 S K m} {k : ℕ}
    (hu : N07aWeakCanonicalMixedDerivative S K m u uk 0 k) :
    N07aWeakCanonicalMixedDerivative S K m
      (n07aSmoothCanonicalMul (fun p => ξ p.1) hξ.1 u)
      (n07aSmoothCanonicalMul (fun p => ξ p.1) hξ.1 uk) 0 k := by
  intro φ hφ
  have htest := hu (fun p => ξ p.1 * φ p) (n07a_canonicalTest_mul hφ hξ.1 hξ.2.1)
  have hd : mixedDerivative 0 k (fun p => ξ p.1 * φ p) =
      fun p => ξ p.1 * mixedDerivative 0 k φ p := by
    funext p
    simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_const_mul_field]
  rw [hd] at htest
  rw [n07aSmoothCanonicalMul_pairing, n07aSmoothCanonicalMul_pairing]
  exact htest

/-- All-angular `L²` data in the real second-order equation recover the
entire first-normal graph after any compact radial localization. -/
theorem n07a_secondPrimitive_local_firstRegular (m : ℕ) (hm : K.left m < K.right m)
    {ξ : ℝ → ℝ} (hξ : CanonicalTest S K m (fun p => ξ p.1))
    {v h g : CanonicalL2 S K m}
    (heq : N07aCanonicalSecondPrimitiveEquation v h g)
    (hv : N07aCanonicalNormalRegular S K m v 0)
    (hh : N07aCanonicalNormalRegular S K m h 0)
    (hg : N07aCanonicalNormalRegular S K m g 0) :
    N07aCanonicalNormalRegular S K m
      (n07aSmoothCanonicalMul (fun p => ξ p.1) hξ.1 v) 1 := by
  intro a ha k
  obtain ⟨vk, hvk⟩ := hv 0 le_rfl k
  have hcut := n07a_weakAngular_radialCutoff hξ hvk
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · exact ⟨_, hcut⟩
  · obtain ⟨hk, hhk⟩ := hh 0 le_rfl k
    obtain ⟨gk, hgk⟩ := hg 0 le_rfl k
    obtain ⟨d, hd⟩ := n07a_secondPrimitive_exists_local_first m hm hξ
      (heq.angular hvk hhk hgk)
    exact ⟨d, by simpa only [zero_add, add_zero] using hcut.comp hd⟩

/-- Multiplying by the genuine reciprocal leading coefficient recovers
the localized original unknown, including all its first-normal angular jets. -/
theorem n07a_firstRegular_of_leading_localization
    (a ρ : N07aCanonicalOpenCoefficient S K m)
    (hinv : ∀ᵐ p ∂canonicalMeasure S K m, ρ.value p * a.value p = 1)
    {χ : PolarPoint → ℝ} (hχ : ContDiff ℝ ∞ χ) {u : CanonicalL2 S K m}
    (hu : N07aCanonicalNormalRegular S K m (n07aSmoothCanonicalMul χ hχ (a.mul u)) 1) :
    N07aCanonicalNormalRegular S K m (n07aSmoothCanonicalMul χ hχ u) 1 := by
  have h := ρ.normalRegular 1 _ hu
  have he : ρ.mul (n07aSmoothCanonicalMul χ hχ (a.mul u)) =
      n07aSmoothCanonicalMul χ hχ u := by
    apply Lp.ext
    filter_upwards [ρ.mul_ae (n07aSmoothCanonicalMul χ hχ (a.mul u)),
      n07aSmoothCanonicalMul_ae χ hχ (a.mul u), a.mul_ae u,
      n07aSmoothCanonicalMul_ae χ hχ u, hinv] with p hρ hcut ha hχu hi
    rw [hρ, hcut, ha, hχu]
    calc
      ρ.value p * (χ p * (a.value p * u p)) = χ p * ((ρ.value p * a.value p) * u p) := by ring
      _ = χ p * u p := by rw [hi, one_mul]
  rw [he] at h
  exact h

end ContinuousFlexibility.Analysis
