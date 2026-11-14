module

public import ContinuousFlexibility.Analysis.N07aAngularClassical
public import ContinuousFlexibility.Analysis.N07aWeakRegularityAlgebra
public import ContinuousFlexibility.Analysis.SpacesLpRestriction

/-!
# Restricting the actual canonical weak jets to a smaller radial interval

The operator is the existing measure-dominated L² restriction. Compact
tests on the smaller strip are also tests on the larger one, and their
pairings agree exactly. No boundary value or matching trace is involved.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology ENNReal

variable {S : PhysicalSpacesData} {K J : CanonicalData S} {m n : ℕ}

/-- Only the actual interval is restricted; the angular measure is unchanged. -/
theorem n07a_canonicalMeasure_mono
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m)) :
    canonicalMeasure S J n ≤ canonicalMeasure S K m := by
  unfold canonicalMeasure
  exact Measure.restrict_mono (Set.prod_mono hsub subset_rfl) le_rfl

def n07aCanonicalRestrict
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m)) :
    CanonicalL2 S K m →L[ℝ] CanonicalL2 S J n :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa only [one_smul] using n07a_canonicalMeasure_mono hsub)

theorem n07aCanonicalRestrict_ae
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m))
    (u : CanonicalL2 S K m) :
    (n07aCanonicalRestrict hsub u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

theorem n07aCanonicalRestrict_norm_le
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m))
    (u : CanonicalL2 S K m) : ‖n07aCanonicalRestrict hsub u‖ ≤ ‖u‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (n07aCanonicalRestrict_ae hsub u), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (n07a_canonicalMeasure_mono hsub))

theorem n07a_canonicalTest_mono
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m))
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S J n φ) : CanonicalTest S K m φ := by
  obtain ⟨hs, hp, Q, hQ, hQI, hzero⟩ := hφ
  exact ⟨hs, hp, Q, hQ, hQI.trans hsub, hzero⟩

theorem n07aCanonicalRestrict_pairing
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m))
    (u : CanonicalL2 S K m) {φ : PolarPoint → ℝ} (hφ : CanonicalTest S J n φ) :
    (∫ p, n07aCanonicalRestrict hsub u p * φ p ∂canonicalMeasure S J n) =
      ∫ p, u p * φ p ∂canonicalMeasure S K m := by
  calc
    _ = ∫ p, u p * φ p ∂canonicalMeasure S J n := by
      apply integral_congr_ae
      filter_upwards [n07aCanonicalRestrict_ae hsub u] with p hp
      rw [hp]
    _ = ∫ p, u p * φ p ∂materialCylinderMeasure := by
      apply n07a_canonicalIntegral_eq_cylinder
      intro p hp
      rw [n07a_canonicalTest_zero_outside hφ hp, mul_zero]
    _ = _ := by
      symm
      apply n07a_canonicalIntegral_eq_cylinder
      intro p hp
      rw [n07a_canonicalTest_zero_outside (n07a_canonicalTest_mono hsub hφ) hp, mul_zero]

/-- Actual mixed distributional derivatives restrict to the smaller strip. -/
theorem n07aCanonicalRestrict_weak
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m))
    {u v : CanonicalL2 S K m} {a b : ℕ}
    (huv : N07aWeakCanonicalMixedDerivative S K m u v a b) :
    N07aWeakCanonicalMixedDerivative S J n
      (n07aCanonicalRestrict hsub u) (n07aCanonicalRestrict hsub v) a b := by
  intro φ hφ
  rw [n07aCanonicalRestrict_pairing hsub v hφ,
    n07aCanonicalRestrict_pairing hsub u (n07a_canonicalTest_mixedDerivative hφ a b)]
  exact huv φ (n07a_canonicalTest_mono hsub hφ)

theorem n07aCanonicalRestrict_normalRegular
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m))
    {u : CanonicalL2 S K m} {k : ℕ} (hu : N07aCanonicalNormalRegular S K m u k) :
    N07aCanonicalNormalRegular S J n (n07aCanonicalRestrict hsub u) k := by
  intro a ha b
  obtain ⟨v, hv⟩ := hu a ha b
  exact ⟨n07aCanonicalRestrict hsub v, n07aCanonicalRestrict_weak hsub hv⟩

/-- On the smaller strip a cutoff equal to one gives exactly the original
L² class, independent of the representatives used by the multipliers. -/
theorem n07aCanonicalRestrict_cutoff
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m))
    {χ : PolarPoint → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hone : ∀ p ∈ canonicalOpen S J n, χ p = 1) (u : CanonicalL2 S K m) :
    n07aCanonicalRestrict hsub (n07aSmoothCanonicalMul χ hχ u) =
      n07aCanonicalRestrict hsub u := by
  apply Lp.ext
  have he := (n07aSmoothCanonicalMul_ae χ hχ u).filter_mono
    (ae_mono (n07a_canonicalMeasure_mono hsub))
  have hmem : ∀ᵐ p ∂canonicalMeasure S J n, p ∈ canonicalOpen S J n := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    exact ⟨hp.1, mem_univ _⟩
  filter_upwards [n07aCanonicalRestrict_ae hsub (n07aSmoothCanonicalMul χ hχ u),
    n07aCanonicalRestrict_ae hsub u, he, hmem] with p hleft hright hmul hp
  rw [hleft, hright, hmul, hone p hp, one_mul]

/-- The localized first-normal graph is the true first-normal graph of the
original solution on every smaller strip where the cutoff is one. -/
theorem n07aCanonicalRestrict_localFirst
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m))
    {χ : PolarPoint → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hone : ∀ p ∈ canonicalOpen S J n, χ p = 1) {u : CanonicalL2 S K m}
    (hu : N07aCanonicalNormalRegular S K m (n07aSmoothCanonicalMul χ hχ u) 1) :
    N07aCanonicalNormalRegular S J n (n07aCanonicalRestrict hsub u) 1 := by
  have h := n07aCanonicalRestrict_normalRegular hsub hu
  rw [n07aCanonicalRestrict_cutoff hsub hχ hone u] at h
  exact h

end ContinuousFlexibility.Analysis
