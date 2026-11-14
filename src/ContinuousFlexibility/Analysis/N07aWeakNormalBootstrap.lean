module

public import ContinuousFlexibility.Analysis.N07aWeakRegularityAlgebra

/-!
# Qualitative normal bootstrap in the actual canonical weak space

A second-normal equation whose right-hand side contains at most one
normal derivative of the unknown recovers every normal derivative.
The finite sum is built from the actual bounded coefficient multipliers
and prescribed weak jets; its regularity is proved by the weak jet
algebra rather than assumed of the solution.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology BigOperators
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- A second-normal weak equation and regularity of its actual right-hand
side recover every additional normal order. -/
theorem n07aCanonicalNormalRegular_of_second
    {u R : CanonicalL2 S K m} {n : ℕ}
    (hbase : N07aCanonicalNormalRegular S K m u 1)
    (hsecond : N07aWeakCanonicalMixedDerivative S K m u R 2 0)
    (hR : N07aCanonicalNormalRegular S K m R n) :
    N07aCanonicalNormalRegular S K m u (n + 2) := by
  intro a ha b
  by_cases ha1 : a ≤ 1
  · exact hbase a ha1 b
  · obtain ⟨v, hv⟩ := hR (a - 2) (by omega) b
    refine ⟨v, ?_⟩
    have h := hsecond.comp hv
    have he : 2 + (a - 2) = a := by omega
    simpa only [he, Nat.zero_add] using h

/-- A finite normal recursion with genuine weak coefficient products
upgrades an initially first-normal solution to every mixed weak order. -/
theorem n07a_weakCanonical_normalBootstrap
    {ι : Type*} (I : Finset ι)
    (χ : ι → PolarPoint → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχp : ∀ i, Function.Periodic (χ i) (0, Real.pi))
    (ρ : PolarPoint → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρp : Function.Periodic ρ (0, Real.pi))
    (ar ang : ι → ℕ) (har : ∀ i ∈ I, ar i ≤ 1)
    {u F : CanonicalL2 S K m} (v : ι → CanonicalL2 S K m)
    (hv : ∀ i ∈ I, N07aWeakCanonicalMixedDerivative S K m u (v i) (ar i) (ang i))
    (hbase : N07aCanonicalNormalRegular S K m u 1)
    (hF : ∀ n : ℕ, N07aCanonicalNormalRegular S K m F n)
    (hsecond : N07aWeakCanonicalMixedDerivative S K m u
      ((∑ i ∈ I, n07aSmoothCanonicalMul (χ i) (hχ i) (v i)) +
        n07aSmoothCanonicalMul ρ hρ F) 2 0) :
    ∀ n : ℕ, N07aCanonicalNormalRegular S K m u n := by
  apply Nat.twoStepInduction
  · exact hbase.mono (by omega)
  · exact hbase
  · intro n _ hn
    apply n07aCanonicalNormalRegular_of_second hbase hsecond
    apply N07aCanonicalNormalRegular.add
    · apply n07aCanonicalNormalRegular_sum I _ n
      intro i hi
      apply n07aSmoothCanonicalMul_normalRegular n (χ i) (hχ i) (hχp i)
      have hneeded : n + ar i ≤ n + 1 := by have := har i hi; omega
      exact (hn.mono hneeded).derivative (hv i hi)
    · exact n07aSmoothCanonicalMul_normalRegular n ρ hρ hρp F (hF n)

/-- Each mixed derivative is an L² class obtained by the preceding
bootstrap. This conclusion is still prior to smooth reconstruction. -/
theorem n07a_weakCanonical_allMixed_of_normalRegular
    {u : CanonicalL2 S K m}
    (hu : ∀ n : ℕ, N07aCanonicalNormalRegular S K m u n) (a b : ℕ) :
    ∃ v : CanonicalL2 S K m, N07aWeakCanonicalMixedDerivative S K m u v a b :=
  hu a a le_rfl b

end ContinuousFlexibility.Analysis
