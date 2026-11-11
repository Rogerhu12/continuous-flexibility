import ContinuousFlexibility.Analysis.N05ReferenceAngularJetBasis
import ContinuousFlexibility.Statements.Analysis

/-!
# Actual derivatives of the two low reference modes

Every positive angular derivative kills the mean. The remaining bordered
frequency is exactly two, so it only contributes the scalar factor 2^b.
The normalized phase continues to have unit angular square norm.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

def n05_referenceLowJetBasis : ℕ → ℝ → ℝ
  | 0 => cosineMode 2
  | 1 => fun θ => -sineMode 2 θ
  | b + 2 => fun θ => -n05_referenceLowJetBasis b θ

theorem n05_referenceLowJetBasis_contDiff (b : ℕ) :
    ContDiff ℝ ∞ (n05_referenceLowJetBasis b) := by
  induction b using Nat.twoStepInduction with
  | zero => exact r11b_contDiff_cosineMode 2
  | one => exact (r11b_contDiff_sineMode 2).neg
  | more b hb _ => exact hb.neg

theorem n05_referenceLowJetBasis_memLp (b : ℕ) :
    MemLp (n05_referenceLowJetBasis b) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
  memLp_referenceAngular_interval_of_continuous
    (n05_referenceLowJetBasis_contDiff b).continuous

theorem n05_referenceLowJetBasis_pairing (b : ℕ) :
    angularPairing (n05_referenceLowJetBasis b) (n05_referenceLowJetBasis b) = 1 := by
  induction b using Nat.twoStepInduction with
  | zero =>
    simpa only [n05_referenceLowJetBasis, ite_true] using
      angularPairing_cosineMode 2 2 (by decide) (by decide)
  | one =>
    simpa only [n05_referenceLowJetBasis, angularPairing, neg_mul_neg, ite_true] using
      angularPairing_sineMode 2 2 (by decide) (by decide)
  | more b hb _ =>
    simpa only [n05_referenceLowJetBasis, angularPairing, neg_mul_neg] using hb

theorem n05_referenceLowBasis_iteratedDeriv (b : ℕ) :
    iteratedDeriv b (referenceAngularBasis 1) =
      fun θ => (2 : ℝ) ^ b * n05_referenceLowJetBasis b θ := by
  induction b using Nat.twoStepInduction with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, one_mul,
      n05_referenceLowJetBasis, referenceAngularBasis]
  | one =>
    funext θ
    rw [iteratedDeriv_one]
    change deriv (cosineMode 2) θ = (2 : ℝ) ^ 1 * (-sineMode 2 θ)
    rw [deriv_cosineMode, pow_one]
    simp only [cosineModeFirst, sineMode, Nat.cast_ofNat]
    ring
  | more b hb _ =>
    have hsecond : deriv (deriv (referenceAngularBasis 1)) =
        fun θ => -(2 : ℝ) ^ 2 * referenceAngularBasis 1 θ := by
      simpa only [Nat.mul_one, Nat.cast_ofNat] using
        funext (deriv_deriv_referenceAngularBasis 1)
    rw [iteratedDeriv_succ', iteratedDeriv_succ', hsecond]
    funext θ
    rw [iteratedDeriv_const_mul_field, hb]
    simp only [n05_referenceLowJetBasis, pow_add, pow_two]
    ring

def n05_referenceLowAngularJet (b : ℕ) (u : PolarPoint → ℝ) : PolarPoint → ℝ :=
  mixedDerivative 0 b (referenceBasisProjection {0, 1} u)

theorem n05_referenceLowAngularJet_apply {b : ℕ} (hb : 0 < b)
    (u : PolarPoint → ℝ) (x : PolarPoint) :
    n05_referenceLowAngularJet b u x =
      (2 : ℝ) ^ b * referenceRadialCoefficient u 1 x.1 *
        n05_referenceLowJetBasis b x.2 := by
  have hlow : (fun θ => referenceBasisProjection {0, 1} u (x.1, θ)) =
      fun θ => referenceRadialCoefficient u 0 x.1 +
        referenceRadialCoefficient u 1 x.1 * referenceAngularBasis 1 θ := by
    funext θ
    simp only [referenceBasisProjection, angularBasisProjection,
      Finset.sum_insert (by decide : (0 : ℕ) ∉ {1}), Finset.sum_singleton,
      referenceRadialCoefficient, referenceAngularBasis, mul_one]
  change iteratedDeriv b (fun θ => referenceBasisProjection {0, 1} u (x.1, θ)) x.2 = _
  rw [hlow, iteratedDeriv_const_add hb, iteratedDeriv_const_mul_field,
    n05_referenceLowBasis_iteratedDeriv]
  ring

end ContinuousFlexibility.Radial
