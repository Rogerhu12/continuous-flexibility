import ContinuousFlexibility.Analysis.N07aWeakSecondNormal
import ContinuousFlexibility.Analysis.N07aWeakNormalBootstrap

/-!
# All normal weak derivatives from the actual divergence equation

The right-hand side includes the genuine zero-order potential. Its
regularity is established together with the solution, so it is not
silently treated as an independently smooth source. All products are
the actual canonical L² multipliers.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aC1Multiplier_normalRegular (n : ℕ)
    (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχp : Function.Periodic χ (0, Real.pi)) (A : ℝ)
    (hA : N07aCanonicalC1Bound S K m χ A) {u : CanonicalL2 S K m}
    (hu : N07aCanonicalNormalRegular S K m u n) :
    N07aCanonicalNormalRegular S K m (n07aC1Multiplier χ hχ A hA u) n := by
  rw [n07aC1Multiplier, ← n07aSmoothCanonicalMul_eq χ hχ A hA.value]
  exact n07aSmoothCanonicalMul_normalRegular n χ hχ hχp u hu

theorem n07aC1DerivativeMultiplier_normalRegular (n : ℕ)
    (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχp : Function.Periodic χ (0, Real.pi)) (A : ℝ)
    (hA : N07aCanonicalC1Bound S K m χ A) (j : Fin 2) {u : CanonicalL2 S K m}
    (hu : N07aCanonicalNormalRegular S K m u n) :
    N07aCanonicalNormalRegular S K m (n07aC1DerivativeMultiplier χ hχ A hA j u) n := by
  rw [n07aC1DerivativeMultiplier, ← n07aSmoothCanonicalMul_eq _ _ A (hA.first j)]
  exact n07aSmoothCanonicalMul_normalRegular n _ (contDiff_mixedDerivative hχ _ _)
    (n07a_canonicalCoefficient_derivative_periodic hχp _ _) u hu

/-- The explicit second-normal right-hand side has `n` normal derivatives
as soon as the solution has `n+1`; no derivative of order `n+2` is used. -/
theorem n07aCanonicalSecondNormalRhs_normalRegular (n : ℕ)
    (a b c χ : PolarPoint → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) (hχ : ContDiff ℝ ∞ χ)
    (hap : Function.Periodic a (0, Real.pi)) (hbp : Function.Periodic b (0, Real.pi))
    (hcp : Function.Periodic c (0, Real.pi)) (hχp : Function.Periodic χ (0, Real.pi))
    (A : ℝ) (haA : N07aCanonicalC1Bound S K m a A)
    (hbA : N07aCanonicalC1Bound S K m b A) (hcA : N07aCanonicalC1Bound S K m c A)
    (hχA : N07aCanonicalC1Bound S K m χ A)
    {u ur uθ urθ uθθ F : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1)
    (hu : N07aCanonicalNormalRegular S K m u (n + 1))
    (hF : N07aCanonicalNormalRegular S K m F n) :
    N07aCanonicalNormalRegular S K m
      (n07aCanonicalSecondNormalRhs a b c χ ha hb hc hχ A haA hbA hcA hχA
        F ur uθ urθ uθθ) n := by
  have hur : N07aCanonicalNormalRegular S K m ur n := hu.derivative hr
  have huθ : N07aCanonicalNormalRegular S K m uθ n :=
    (hu.mono (Nat.le_succ n)).derivative hθ
  have hurθ : N07aCanonicalNormalRegular S K m urθ n := hu.derivative (hr.comp hrθ)
  have huθθ : N07aCanonicalNormalRegular S K m uθθ n :=
    (hu.mono (Nat.le_succ n)).derivative (hθ.comp hθθ)
  unfold n07aCanonicalSecondNormalRhs
  apply N07aCanonicalNormalRegular.add
  · apply n07aC1Multiplier_normalRegular n χ hχ hχp A hχA
    apply N07aCanonicalNormalRegular.sub
    · apply N07aCanonicalNormalRegular.sub hF
      exact ((n07aC1Multiplier_normalRegular n b hb hbp A hbA hurθ).add
        (n07aC1DerivativeMultiplier_normalRegular n b hb hbp A hbA 1 hur)).add
        ((n07aC1Multiplier_normalRegular n c hc hcp A hcA huθθ).add
          (n07aC1DerivativeMultiplier_normalRegular n c hc hcp A hcA 1 huθ))
    · exact (n07aC1Multiplier_normalRegular n b hb hbp A hbA hurθ).add
        (n07aC1DerivativeMultiplier_normalRegular n b hb hbp A hbA 0 huθ)
  · exact n07aC1DerivativeMultiplier_normalRegular n χ hχ hχp A hχA 0
      (n07aC1Multiplier_normalRegular n a ha hap A haA hur)

/-- A genuine weak divergence equation with a smooth potential gives all
mixed L² weak derivatives from angular regularity and one normal derivative.
The original source is the only field assumed to have all normal orders. -/
theorem n07a_weakCanonical_divergenceBootstrap
    (a b c χ q : PolarPoint → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c)
    (hχ : ContDiff ℝ ∞ χ) (hq : ContDiff ℝ ∞ q)
    (hap : Function.Periodic a (0, Real.pi)) (hbp : Function.Periodic b (0, Real.pi))
    (hcp : Function.Periodic c (0, Real.pi)) (hχp : Function.Periodic χ (0, Real.pi))
    (hqp : Function.Periodic q (0, Real.pi)) (A : ℝ) (hA : 1 ≤ A)
    (haA : N07aCanonicalC1Bound S K m a A) (hbA : N07aCanonicalC1Bound S K m b A)
    (hcA : N07aCanonicalC1Bound S K m c A) (hχA : N07aCanonicalC1Bound S K m χ A)
    (hinv : ∀ᵐ p ∂canonicalMeasure S K m, χ p * a p = 1)
    {u ur uθ urθ uθθ F : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1)
    (hbase : N07aCanonicalNormalRegular S K m u 1)
    (hF : ∀ n : ℕ, N07aCanonicalNormalRegular S K m F n)
    (hflux : N07aCanonicalFluxEquation S K m (F - n07aSmoothCanonicalMul q hq u)
      (n07aC1Multiplier a ha A haA ur + n07aC1Multiplier b hb A hbA uθ)
      (n07aC1Multiplier b hb A hbA ur + n07aC1Multiplier c hc A hcA uθ)) :
    ∀ n : ℕ, N07aCanonicalNormalRegular S K m u n := by
  have hsecond := (n07a_weakCanonical_secondNormal a b c χ ha hb hc hχ hbp hcp hχp
    A hA haA hbA hcA hχA hinv hr hθ hrθ hθθ hflux).2.1
  apply Nat.twoStepInduction
  · exact hbase.mono (Nat.zero_le _)
  · exact hbase
  · intro n _ hn
    apply n07aCanonicalNormalRegular_of_second hbase hsecond
    apply n07aCanonicalSecondNormalRhs_normalRegular n a b c χ ha hb hc hχ
      hap hbp hcp hχp A haA hbA hcA hχA hr hθ hrθ hθθ hn
    exact (hF n).sub (n07aSmoothCanonicalMul_normalRegular n q hq hqp u
      (hn.mono (Nat.le_succ n)))

end ContinuousFlexibility.Analysis
