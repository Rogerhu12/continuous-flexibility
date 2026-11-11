import ContinuousFlexibility.Radial.OuterEnvelope
import ContinuousFlexibility.Radial.OuterKernelEnvelopeAlgebra

/-!
# Common envelope for the whole natural vector and Green operator

One quadratic constant absorbs the core mass, natural Poisson norm and
unit-state propagation. The action factor remains separate and has the
first power for the natural solution and the second for the inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

theorem outer_global_core_envelope {n : ℕ} {Q Kn : ℝ}
    (hn : 1 ≤ n) (hQ : 0 ≤ Q) (hKn : 0 ≤ Kn) :
    exp (Q * (n : ℝ) ^ 2) * Kn ≤ radialE n ^ (12 + 4 * Q) * Kn := by
  apply mul_le_mul_of_nonneg_right _ hKn
  exact (outer_quadratic_le_envelope hn hQ).trans
    (outer_envelope_exponent_mono n (by linarith only [hQ]))

theorem outer_global_natural_envelope {n : ℕ} {Q lam Kn : ℝ}
    (hn : 1 ≤ n) (hQ : 0 ≤ Q) (hKn : 0 ≤ Kn) :
    2 * (sqrt lam * exp (Q * (n : ℝ) ^ 2) *
      (exp (Q * (n : ℝ) ^ 2) * Kn)) ≤
        sqrt lam * radialE n ^ (12 + 4 * Q) * Kn := by
  have heq : exp (2 * Q * (n : ℝ) ^ 2) =
      exp (Q * (n : ℝ) ^ 2) * exp (Q * (n : ℝ) ^ 2) := by
    rw [← exp_add]
    congr 1
    ring
  have htwo : 2 * exp (2 * Q * (n : ℝ) ^ 2) ≤ radialE n ^ (12 + 4 * Q) := by
    calc
      _ ≤ 2 * radialE n ^ (2 * Q) :=
        mul_le_mul_of_nonneg_left
          (outer_quadratic_le_envelope hn (by positivity : 0 ≤ 2 * Q)) (by norm_num)
      _ ≤ radialE n ^ (2 + 2 * Q) := outer_envelope_prefactor hn (by norm_num)
      _ ≤ _ := outer_envelope_exponent_mono n (by linarith only [hQ])
  calc
    _ = sqrt lam * (2 * exp (2 * Q * (n : ℝ) ^ 2)) * Kn := by rw [heq]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htwo (sqrt_nonneg _)) hKn

theorem outer_global_inverse_envelope {n : ℕ} {Q Kn d : ℝ}
    (hn : 1 ≤ n) (hQ : 0 ≤ Q) (hKn : 1 ≤ Kn) (hd : d ≤ 4) :
    2 * (d + 2 * exp (Q * (n : ℝ) ^ 2) ^ 2 *
      (exp (Q * (n : ℝ) ^ 2) * Kn) ^ 2) ≤
        radialE n ^ (12 + 4 * Q) * Kn ^ 2 := by
  have heq : exp (2 * Q * (n : ℝ) ^ 2) =
      exp (Q * (n : ℝ) ^ 2) * exp (Q * (n : ℝ) ^ 2) := by
    rw [← exp_add]
    congr 1
    ring
  have hb := outer_inverse_envelope hn (by positivity : 0 ≤ 2 * Q) hKn hd
  rw [show (12 : ℝ) + 2 * (2 * Q) = 12 + 4 * Q by ring] at hb
  calc
    _ = 2 * (d + 2 * exp (2 * Q * (n : ℝ) ^ 2) ^ 2 * Kn ^ 2) := by rw [heq]; ring
    _ ≤ _ := hb

end ContinuousFlexibility.Radial
