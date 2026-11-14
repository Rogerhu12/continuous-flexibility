module

public import ContinuousFlexibility.Radial.OscillatorDifferentialPairing

/-!
# Actual differential energy of the central model

The integrals use genuine whole-line Lebesgue measure and actual
derivatives. A constant shift turns the central expression into the
oscillator plus one. This supplies the physical energy identity needed
for R03.03; it does not yet construct its closed weak-derivative domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def oscillatorEnergyPairing (j : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ, deriv φ x * deriv ψ x) +
    j ^ 2 * (∫ x : ℝ, (x * φ x) * (x * ψ x))

/-- This shift gives the physical positive expression `Hosc + 1`. -/
def centralEnergyShift (j : ℝ) : ℝ :=
  1 - (centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA)

def shiftedCentralEnergyPairing (j : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  oscillatorEnergyPairing j φ ψ + ∫ x : ℝ, φ x * ψ x

theorem centralEnergyShift_level (j : ℝ) (n : ℕ) :
    centralSpectralLevel j n + centralEnergyShift j = j * (2 * (n : ℝ) + 1) + 1 := by
  unfold centralSpectralLevel centralEnergyShift
  ring

/-- Actual integration by parts, including all product-integrability
conditions; neither input is assumed to be an eigenfunction. -/
theorem oscillator_form_pairing {j : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : OscillatorEnergyDomain φ) (hψ : OscillatorEnergyDomain ψ)
    (hHψ : MemLp (oscillatorExpression j ψ) 2 volume) :
    (∫ x : ℝ, φ x * oscillatorExpression j ψ x) =
      oscillatorEnergyPairing j φ ψ := by
  have hsecond := integrable_mul_second_of_oscillator_image hφ hψ hHψ
  have hweighted : Integrable (fun x : ℝ => (x * φ x) * (x * ψ x)) volume :=
    hφ.2.2.2.integrable_mul hψ.2.2.2
  have hnegative : Integrable (fun x : ℝ => -(φ x * deriv (deriv ψ) x)) volume := hsecond.neg
  have hpotential : Integrable (fun x : ℝ =>
      j ^ 2 * ((x * φ x) * (x * ψ x))) volume := hweighted.const_mul _
  have hI := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => (hφ.1.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hψ.1.differentiable_deriv_two x).hasDerivAt)
    hsecond (hφ.2.2.1.integrable_mul hψ.2.2.1) (hφ.2.1.integrable_mul hψ.2.2.1)
  calc
    _ = ∫ x : ℝ, -(φ x * deriv (deriv ψ) x) +
        j ^ 2 * ((x * φ x) * (x * ψ x)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by unfold oscillatorExpression; ring)
    _ = _ := by
      rw [integral_add hnegative hpotential, integral_neg,
        integral_const_mul, hI]
      unfold oscillatorEnergyPairing
      ring

theorem central_shifted_form_pairing {j : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : OscillatorEnergyDomain φ) (hψ : OscillatorEnergyDomain ψ)
    (hHψ : MemLp (liouvilleSchrodinger (j ^ 2)
      centralRadius centralDensityRoot ψ) 2 volume) :
    (∫ x : ℝ, φ x * liouvilleSchrodinger (j ^ 2)
      centralRadius centralDensityRoot ψ x) +
      centralEnergyShift j * (∫ x : ℝ, φ x * ψ x) =
        shiftedCentralEnergyPairing j φ ψ := by
  have hosc := (central_memLp_image_iff hψ).mp hHψ
  have hprod : Integrable (fun x : ℝ => φ x * ψ x) volume :=
    hφ.2.1.integrable_mul hψ.2.1
  have hoscprod : Integrable (fun x : ℝ => φ x * oscillatorExpression j ψ x) volume :=
    hφ.2.1.integrable_mul hosc
  have hshiftprod : Integrable (fun x : ℝ =>
      (centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA) * (φ x * ψ x)) volume :=
    hprod.const_mul _
  have hh : (∫ x : ℝ, φ x * liouvilleSchrodinger (j ^ 2)
      centralRadius centralDensityRoot ψ x) =
      (∫ x : ℝ, φ x * oscillatorExpression j ψ x) +
        (centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA) * (∫ x : ℝ, φ x * ψ x) := by
    calc
      _ = ∫ x : ℝ, φ x * oscillatorExpression j ψ x +
          (centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA) * (φ x * ψ x) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          dsimp only
          rw [central_liouvilleSchrodinger_eq_oscillator_shift]; ring)
      _ = _ := by
        rw [integral_add hoscprod hshiftprod, integral_const_mul]
  rw [hh, oscillator_form_pairing hφ hψ hosc]
  unfold centralEnergyShift shiftedCentralEnergyPairing
  ring

theorem oscillatorEnergyPairing_self_nonneg (j : ℝ) (ψ : ℝ → ℝ) :
    0 ≤ oscillatorEnergyPairing j ψ ψ := by
  unfold oscillatorEnergyPairing
  exact add_nonneg (integral_nonneg fun x => mul_self_nonneg _)
    (mul_nonneg (sq_nonneg j) (integral_nonneg fun x => mul_self_nonneg _))

theorem shiftedCentralEnergyPairing_controls_L2 (j : ℝ) (ψ : ℝ → ℝ) :
    (∫ x : ℝ, ψ x ^ 2) ≤ shiftedCentralEnergyPairing j ψ ψ := by
  have h := oscillatorEnergyPairing_self_nonneg j ψ
  unfold shiftedCentralEnergyPairing
  simpa only [pow_two] using le_add_of_nonneg_left h

/-- Finite sums retain the actual integral orthonormality. -/
theorem integral_finiteHermiteFunction_mul_mode {j : ℝ} (hj : 0 < j)
    (s : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) :
    (∫ x : ℝ, finiteHermiteFunction j s a x * normalizedOscillatorHermite j n x) =
      if n ∈ s then a n else 0 := by
  have hprod (k : ℕ) : Integrable (fun x : ℝ =>
      a k * (normalizedOscillatorHermite j k x * normalizedOscillatorHermite j n x)) volume :=
    ((normalizedOscillatorHermite_energyDomain hj k).2.1.integrable_mul
      (normalizedOscillatorHermite_energyDomain hj n).2.1).const_mul _
  calc
    _ = ∫ x : ℝ, ∑ k ∈ s,
        a k * (normalizedOscillatorHermite j k x * normalizedOscillatorHermite j n x) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      unfold finiteHermiteFunction
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ k ∈ s, a k * (if k = n then 1 else 0) := by
      rw [integral_finsetSum s (fun k _ => hprod k)]
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_const_mul, integral_normalizedOscillatorHermite_mul hj]
    _ = _ := by simp

theorem integral_finiteHermiteFunction_mul {j : ℝ} (hj : 0 < j)
    (s : Finset ℕ) (a b : ℕ → ℝ) :
    (∫ x : ℝ, finiteHermiteFunction j s a x * finiteHermiteFunction j s b x) =
      ∑ n ∈ s, a n * b n := by
  have hprod (n : ℕ) : Integrable (fun x : ℝ =>
      b n * (finiteHermiteFunction j s a x * normalizedOscillatorHermite j n x)) volume :=
    ((finiteHermiteFunction_energyDomain hj s a).2.1.integrable_mul
      (normalizedOscillatorHermite_energyDomain hj n).2.1).const_mul _
  calc
    _ = ∫ x : ℝ, ∑ n ∈ s,
        b n * (finiteHermiteFunction j s a x * normalizedOscillatorHermite j n x) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      change finiteHermiteFunction j s a x *
        (∑ n ∈ s, b n * normalizedOscillatorHermite j n x) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by
      rw [integral_finsetSum s (fun n _ => hprod n)]
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul, integral_finiteHermiteFunction_mul_mode hj]
      simp only [ite_eq_left hn]
      ring

theorem finiteHermiteFunction_central_memLp {j : ℝ} (hj : 0 < j)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    MemLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
      (finiteHermiteFunction j s a)) 2 volume := by
  have heq : liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
      (finiteHermiteFunction j s a) =
      finiteHermiteFunction j s (fun n => a n * centralSpectralLevel j n) := by
    funext x
    rw [centralExpression_finiteHermiteFunction hj]
    rfl
  rw [heq]
  exact (finiteHermiteFunction_energyDomain hj s _).2.1

/-- Exact physical positive energy of each finite actual Hermite sum. -/
theorem finiteHermiteFunction_shifted_energy {j : ℝ} (hj : 0 < j)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    shiftedCentralEnergyPairing j (finiteHermiteFunction j s a)
      (finiteHermiteFunction j s a) =
      ∑ n ∈ s, (j * (2 * (n : ℝ) + 1) + 1) * a n ^ 2 := by
  have hF := finiteHermiteFunction_energyDomain hj s a
  have he := central_shifted_form_pairing hF hF (finiteHermiteFunction_central_memLp hj s a)
  have hcentral : (∫ x : ℝ, finiteHermiteFunction j s a x *
      liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
        (finiteHermiteFunction j s a) x) =
      ∑ n ∈ s, a n * (a n * centralSpectralLevel j n) := by
    have heq : liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
        (finiteHermiteFunction j s a) =
        finiteHermiteFunction j s (fun n => a n * centralSpectralLevel j n) := by
      funext x
      rw [centralExpression_finiteHermiteFunction hj]
      rfl
    rw [heq, integral_finiteHermiteFunction_mul hj]
  rw [hcentral, integral_finiteHermiteFunction_mul hj] at he
  calc
    _ = (∑ n ∈ s, a n * (a n * centralSpectralLevel j n)) +
        centralEnergyShift j * (∑ n ∈ s, a n * a n) := he.symm
    _ = ∑ n ∈ s, (centralSpectralLevel j n + centralEnergyShift j) * a n ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by simp only [centralEnergyShift_level]

end ContinuousFlexibility.Radial
