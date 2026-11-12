import ContinuousFlexibility.Analysis.N07aCanonicalMultipliers

/-!
# Recovering a normal derivative from the weak flux equation

All fields below are the actual canonical L² classes. Mixed derivatives
are commuted on compact radial test functions. The flux identity then
recovers the missing normal derivative without first choosing a smooth
representative of the solution.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem N07aWeakCanonicalMixedDerivative.neg
    {f g : CanonicalL2 S K m} {a b : ℕ}
    (h : N07aWeakCanonicalMixedDerivative S K m f g a b) :
    N07aWeakCanonicalMixedDerivative S K m (-f) (-g) a b := by
  simpa only [neg_one_smul] using h.smul (-1)

theorem N07aWeakCanonicalMixedDerivative.sub
    {f g u v : CanonicalL2 S K m} {a b : ℕ}
    (hfg : N07aWeakCanonicalMixedDerivative S K m f g a b)
    (huv : N07aWeakCanonicalMixedDerivative S K m u v a b) :
    N07aWeakCanonicalMixedDerivative S K m (f - u) (g - v) a b := by
  simpa only [sub_eq_add_neg] using hfg.add huv.neg

/-- Two derivatives of the same L² class determine the remaining weak
derivative of the lower jet. No cancellation on the unknown function is
used: both identities are evaluated on smooth test functions. -/
theorem N07aWeakCanonicalMixedDerivative.suffix
    {f g h : CanonicalL2 S K m} {a b c d : ℕ}
    (hfg : N07aWeakCanonicalMixedDerivative S K m f g a b)
    (hfh : N07aWeakCanonicalMixedDerivative S K m f h (a + c) (b + d)) :
    N07aWeakCanonicalMixedDerivative S K m g h c d := by
  intro φ hφ
  rw [hfh φ hφ]
  have ht := hfg (mixedDerivative c d φ)
    (n07a_canonicalTest_mixedDerivative hφ c d)
  rw [n07a_mixedDerivative_mixedDerivative hφ.1] at ht
  calc
    _ = (-1 : ℝ) ^ (c + d) * ((-1 : ℝ) ^ (a + b) *
        ∫ p, f p * mixedDerivative (a + c) (b + d) φ p
          ∂canonicalMeasure S K m) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    _ = _ := congrArg (fun x : ℝ => (-1 : ℝ) ^ (c + d) * x) ht.symm

/-- The angular derivative of the first radial jet is also the radial
derivative of the first angular jet, in the original weak test space. -/
theorem n07a_weakCanonical_crossDerivative
    {u ur uθ urθ : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1) :
    N07aWeakCanonicalMixedDerivative S K m uθ urθ 1 0 := by
  apply hθ.suffix
  simpa only [Nat.zero_add, Nat.add_zero] using hr.comp hrθ

/-- Distributional divergence on the same canonical piece. -/
def N07aCanonicalFluxEquation (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (F qr qθ : CanonicalL2 S K m) : Prop :=
  ∀ φ, CanonicalTest S K m φ →
    (∫ p, qr p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m) +
      (∫ p, qθ p * mixedDerivative 0 1 φ p ∂canonicalMeasure S K m) =
        -(∫ p, F p * φ p ∂canonicalMeasure S K m)

/-- Once the angular flux has an angular derivative, the equation gives
the radial derivative of the radial flux as an actual L² class. -/
theorem n07a_weakCanonical_normalFlux
    {F qr qθ dqθ : CanonicalL2 S K m}
    (hflux : N07aCanonicalFluxEquation S K m F qr qθ)
    (hθ : N07aWeakCanonicalMixedDerivative S K m qθ dqθ 0 1) :
    N07aWeakCanonicalMixedDerivative S K m qr (F - dqθ) 1 0 := by
  intro φ hφ
  have he := hflux φ hφ
  have hd := hθ φ hφ
  simp only [zero_add, pow_one, neg_one_mul] at hd
  rw [← n07aCanonicalTestPairing_apply φ (n07a_canonicalTest_memLp hφ), map_sub,
    n07aCanonicalTestPairing_apply, n07aCanonicalTestPairing_apply]
  simp only [add_zero, pow_one, neg_one_mul]
  linarith only [he, hd]

/-- Reversing the preceding step checks the sign and identifies exactly
the divergence equation used by the normal bootstrap. -/
theorem n07a_weakCanonical_flux_of_derivatives
    {F qr qθ dqr dqθ : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m qr dqr 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m qθ dqθ 0 1)
    (heq : dqr + dqθ = F) : N07aCanonicalFluxEquation S K m F qr qθ := by
  intro φ hφ
  have hr' := hr φ hφ
  have hθ' := hθ φ hφ
  simp only [add_zero, zero_add, pow_one, neg_one_mul] at hr' hθ'
  have he := congrArg (n07aCanonicalTestPairing φ (n07a_canonicalTest_memLp hφ)) heq
  rw [map_add, n07aCanonicalTestPairing_apply, n07aCanonicalTestPairing_apply,
    n07aCanonicalTestPairing_apply] at he
  linarith only [hr', hθ', he]

/-- Multiplying a known weak normal derivative by the reciprocal leading
coefficient is justified by the actual weak product rule. This is the
normal-derivative recovery step after subtracting the mixed flux. -/
theorem n07a_weakCanonical_normalQuotient
    {χ : PolarPoint → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχp : Function.Periodic χ (0, Real.pi)) (A B : ℝ)
    (hA : ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A)
    (hB : ∀ᵐ p ∂canonicalMeasure S K m, |mixedDerivative 1 0 χ p| ≤ B)
    {v dv : CanonicalL2 S K m}
    (hv : N07aWeakCanonicalMixedDerivative S K m v dv 1 0) :
    N07aWeakCanonicalMixedDerivative S K m
      (n07aCanonicalMultiplier χ hχ.continuous.aestronglyMeasurable A hA v)
      (n07aCanonicalMultiplier χ hχ.continuous.aestronglyMeasurable A hA dv +
        n07aCanonicalMultiplier (mixedDerivative 1 0 χ)
          (contDiff_mixedDerivative hχ 1 0).continuous.aestronglyMeasurable B hB v)
      1 0 := by
  simpa only [n07aFirstOrder, Fin.isValue, ↓reduceIte, Prod.fst, Prod.snd] using
    n07a_weakCanonical_first_product hχ hχp (0 : Fin 2) A B hA hB hv

end ContinuousFlexibility.Analysis
