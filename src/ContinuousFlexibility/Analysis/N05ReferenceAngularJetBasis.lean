module

public import ContinuousFlexibility.Radial.ReferenceCosineJacobi
public import ContinuousFlexibility.Radial.R11bFiniteSynthesis
public import ContinuousFlexibility.Radial.R11bFourierTests

/-!
# Actual angular derivatives of the high cosine basis

The normalized derivative basis rotates between cosine and sine modes.
Its orthonormality is independent of the derivative order. The frequency
power is kept in the radial coefficient, so finite synthesis computes
ordinary angular derivatives with their exact normalization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff BigOperators
open ContinuousFlexibility.Statements

def n05_referenceHighJetBasis : ℕ → ℕ → ℝ → ℝ
  | 0, n => cosineMode (2 * (n + 2))
  | 1, n => fun θ => -sineMode (2 * (n + 2)) θ
  | b + 2, n => fun θ => -n05_referenceHighJetBasis b n θ

theorem n05_referenceHighJetBasis_contDiff (b n : ℕ) :
    ContDiff ℝ ∞ (n05_referenceHighJetBasis b n) := by
  induction b using Nat.twoStepInduction with
  | zero => exact r11b_contDiff_cosineMode _
  | one => exact (r11b_contDiff_sineMode _).neg
  | more b hb _ => exact hb.neg

theorem n05_referenceHighJetBasis_memLp (b n : ℕ) :
    MemLp (n05_referenceHighJetBasis b n) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
  memLp_referenceAngular_interval_of_continuous
    (n05_referenceHighJetBasis_contDiff b n).continuous

theorem n05_referenceHighJetBasis_pairing (b i j : ℕ) :
    angularPairing (n05_referenceHighJetBasis b i) (n05_referenceHighJetBasis b j) =
      if i = j then 1 else 0 := by
  have hfreq : (2 * (i + 2) = 2 * (j + 2)) ↔ i = j := by omega
  induction b using Nat.twoStepInduction with
  | zero =>
    simpa only [n05_referenceHighJetBasis, hfreq] using
      angularPairing_cosineMode (2 * (i + 2)) (2 * (j + 2)) (by omega) (by omega)
  | one =>
    simpa only [n05_referenceHighJetBasis, angularPairing, neg_mul_neg, hfreq] using
      angularPairing_sineMode (2 * (i + 2)) (2 * (j + 2)) (by omega) (by omega)
  | more b hb _ =>
    simpa only [n05_referenceHighJetBasis, angularPairing, neg_mul_neg] using hb

theorem n05_referenceHighBasis_iteratedDeriv (b n : ℕ) :
    iteratedDeriv b (referenceAngularBasis (n + 2)) =
      fun θ => (((2 * (n + 2) : ℕ) : ℝ) ^ b) * n05_referenceHighJetBasis b n θ := by
  induction b using Nat.twoStepInduction with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, one_mul, n05_referenceHighJetBasis,
      referenceAngularBasis]
  | one =>
    funext θ
    simp only [iteratedDeriv_one, referenceAngularBasis, deriv_cosineMode,
      n05_referenceHighJetBasis, pow_one, cosineModeFirst, sineMode]
    ring
  | more b hb _ =>
    have hsecond : deriv (deriv (referenceAngularBasis (n + 2))) =
        fun θ => -(((2 * (n + 2) : ℕ) : ℝ) ^ 2) *
          referenceAngularBasis (n + 2) θ :=
      funext (deriv_deriv_referenceAngularBasis (n + 2))
    rw [iteratedDeriv_succ', iteratedDeriv_succ', hsecond]
    funext θ
    rw [iteratedDeriv_const_mul_field, hb]
    simp only [n05_referenceHighJetBasis, pow_add, pow_two]
    ring

theorem n05_referenceHighProjection_image (J : Finset ℕ) (f : PolarPoint → ℝ) :
    referenceBasisProjection (J.image (fun n => n + 2)) f =
      r11bFiniteSynthesis J (fun n => referenceRadialCoefficient f (n + 2))
        (fun n => referenceAngularBasis (n + 2)) := by
  funext x
  simp only [referenceBasisProjection, angularBasisProjection, r11bFiniteSynthesis,
    referenceRadialCoefficient,
    Finset.sum_image (fun i _ j _ hij => Nat.add_right_cancel hij)]

/-- This is an equality of ordinary iterated derivatives, not a formal
assignment of a frequency multiplier. No radial smoothness is needed. -/
theorem n05_referenceHighFiniteSynthesis_angularJet
    (J : Finset ℕ) (c : ℕ → ℝ → ℝ) (b : ℕ) :
    (fun x : PolarPoint => iteratedDeriv b
      (fun θ => r11bFiniteSynthesis J c
        (fun n => referenceAngularBasis (n + 2)) (x.1, θ)) x.2) =
      r11bFiniteSynthesis J
        (fun n r => (((2 * (n + 2) : ℕ) : ℝ) ^ b) * c n r)
        (n05_referenceHighJetBasis b) := by
  funext x
  change iteratedDeriv b
    (fun θ => ∑ n ∈ J, c n x.1 * referenceAngularBasis (n + 2) θ) x.2 = _
  rw [iteratedDeriv_fun_sum (fun n _ =>
    ((contDiff_const.mul (contDiff_referenceAngularBasis (n + 2))).of_le
      (by simp)).contDiffAt)]
  simp only [iteratedDeriv_const_mul_field, n05_referenceHighBasis_iteratedDeriv,
    r11bFiniteSynthesis]
  apply Finset.sum_congr rfl
  intro n _
  ring

end ContinuousFlexibility.Radial
