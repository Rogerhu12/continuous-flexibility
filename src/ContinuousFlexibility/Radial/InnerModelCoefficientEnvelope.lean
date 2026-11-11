import ContinuousFlexibility.Radial.InnerModelPoissonNormalization
import ContinuousFlexibility.Radial.InnerModelFluxError
import ContinuousFlexibility.Radial.InnerOrderedChoices

/-!
# Raw coefficient bounds give the model exponential envelopes

The inputs bound the full-line inverse cost, buffer masses, layer
constant, velocity and local weight ratio. The estimates below derive
the compression tolerance and the actual normalized Poisson remainder;
they do not assume smallness of either constructed operator.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements
open scoped BigOperators

theorem innerBuffer_inverse_mass_sum_le_two {B : BufferData}
    (hm : ∀ i, 1 ≤ B.mass i) :
    (∑ i : Fin 2, (B.mass i)⁻¹ ^ 2) ≤ 2 := by
  have hmass (i : Fin 2) : (B.mass i)⁻¹ ^ 2 ≤ 1 := by
    have hnonneg : 0 ≤ (B.mass i)⁻¹ := inv_nonneg.mpr (zero_le_one.trans (hm i))
    have hInv : (B.mass i)⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one (hm i)
    simpa only [one_pow] using (sq_le_sq₀ hnonneg zero_le_one).mpr hInv
  rw [Fin.sum_univ_two]
  linarith only [hmass 0, hmass 1]

/-- The long Morse buffer can have mass below one. Its reciprocal is
bounded by a coefficient power, which is the correct local cost. -/
theorem innerBuffer_inverse_mass_sum_le {B : BufferData}
    (hB : BufferHypotheses B) {coeff : ℝ} (hcoeff : 0 ≤ coeff)
    (hinv : ∀ i, (B.mass i)⁻¹ ≤ coeff) :
    (∑ i : Fin 2, (B.mass i)⁻¹ ^ 2) ≤ 2 * coeff ^ 2 := by
  have hmass (i : Fin 2) : (B.mass i)⁻¹ ^ 2 ≤ coeff ^ 2 :=
    (sq_le_sq₀ (inv_nonneg.mpr (buffer_mass_pos hB i).le) hcoeff).mpr (hinv i)
  rw [Fin.sum_univ_two]
  linarith only [hmass 0, hmass 1]

theorem innerBuffer_dirichlet_envelope_le {B : BufferData}
    (hB : BufferHypotheses B) {C coeff : ℝ}
    (hC : 0 ≤ C) (hcoeff : 1 ≤ coeff) (hB0 : B.B₀ ≤ coeff)
    (hinv : ∀ i, (B.mass i)⁻¹ ≤ coeff) :
    B.B₀ + C * ∑ i, (B.mass i)⁻¹ ^ 2 ≤ (1 + 2 * C) * coeff ^ 2 := by
  have hsum := mul_le_mul_of_nonneg_left
    (innerBuffer_inverse_mass_sum_le hB (zero_le_one.trans hcoeff) hinv) hC
  have hsquare : coeff ≤ coeff ^ 2 := by nlinarith only [hcoeff]
  nlinarith only [hsum, hsquare, hB0]

/-- The original R09 tolerance itself is controlled before invoking
compression. -/
theorem innerBuffer_compression_coefficient_envelope {B : BufferData}
    (hB : BufferHypotheses B) {coeff j t : ℝ}
    (hcoeff : 1 ≤ coeff) (hj : 0 ≤ j)
    (hB0 : B.B₀ ≤ coeff) (hm : ∀ i, B.mass i ≤ coeff * (1 + j))
    (hact : ∀ i, t ≤ B.action i) (i : Fin 2) :
    B.B₀ * B.mass i ^ 2 * exp (-B.action i) ≤
      coeff ^ 3 * (1 + j) ^ 2 * exp (-t) := by
  have hcoeff0 : 0 ≤ coeff := zero_le_one.trans hcoeff
  have hmass := (sq_le_sq₀ (buffer_mass_pos hB i).le
    (mul_nonneg hcoeff0 (by linarith : 0 ≤ 1 + j))).mpr (hm i)
  calc
    _ ≤ coeff * (coeff * (1 + j)) ^ 2 * exp (-t) :=
      mul_le_mul (mul_le_mul hB0 hmass (sq_nonneg _) hcoeff0)
        (exp_le_exp.mpr (neg_le_neg (hact i))) (exp_pos _).le (by positivity)
    _ = _ := by ring

theorem innerBuffer_remainder_coefficient_envelope {B : BufferData}
    (hB : BufferHypotheses B) {C K coeff j t : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hcoeff : 1 ≤ coeff) (hj : 0 ≤ j)
    (hB0 : B.B₀ ≤ coeff) (hlayer : B.layerBound ≤ coeff)
    (hinv : ∀ i, (B.mass i)⁻¹ ≤ coeff) (hmupper : ∀ i, B.mass i ≤ coeff * (1 + j))
    (hact : ∀ i, t ≤ B.action i) (i : Fin 2) :
    innerBufferRemainderEnvelope B C K i ≤
      (2 * K * (1 + 2 * C)) * coeff ^ 5 * (1 + j) ^ 2 * exp (-t) := by
  have hcoeff0 : 0 ≤ coeff := zero_le_one.trans hcoeff
  have hj1 : 0 ≤ 1 + j := by linarith only [hj]
  have hmass : B.mass i ^ (3 / 2 : ℝ) ≤ (coeff * (1 + j)) ^ 2 := by
    have hlarge : 1 ≤ coeff * (1 + j) := by
      nlinarith only [hcoeff, mul_nonneg hcoeff0 hj]
    have hpow : (coeff * (1 + j)) ^ (3 / 2 : ℝ) ≤ (coeff * (1 + j)) ^ 2 := by
      simpa only [rpow_two] using rpow_le_rpow_of_exponent_le hlarge
        (by norm_num : (3 / 2 : ℝ) ≤ 2)
    exact (rpow_le_rpow (buffer_mass_pos hB i).le (hmupper i)
      (by norm_num : (0 : ℝ) ≤ 3 / 2)).trans hpow
  have hlayer' : 1 + B.layerBound ≤ 2 * coeff := by linarith only [hlayer, hcoeff]
  have hforce : K * (1 + B.layerBound) * B.mass i ^ (3 / 2 : ℝ) ≤
      K * (2 * coeff) * (coeff * (1 + j)) ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlayer' hK) hmass
      (rpow_nonneg (buffer_mass_pos hB i).le _) (by positivity)
  have hbase := innerBuffer_dirichlet_envelope_le hB hC hcoeff hB0 hinv
  have hforce0 : 0 ≤ K * (1 + B.layerBound) * B.mass i ^ (3 / 2 : ℝ) := by
    have hlayer0 : 0 ≤ B.layerBound := hB.2.2.2.1.le
    exact mul_nonneg (mul_nonneg hK (by linarith only [hlayer0]))
      (rpow_nonneg (buffer_mass_pos hB i).le _)
  unfold innerBufferRemainderEnvelope
  calc
    _ ≤ ((1 + 2 * C) * coeff ^ 2) *
        ((K * (2 * coeff) * (coeff * (1 + j)) ^ 2) * exp (-t)) :=
      mul_le_mul hbase
        (mul_le_mul hforce (exp_le_exp.mpr (neg_le_neg (hact i)))
          (exp_pos _).le (by positivity))
        (mul_nonneg hforce0 (exp_pos _).le) (by positivity)
    _ = _ := by ring

/-- The scalar is already included in the factor plus one. The same
normalized model remainder has a coefficient power and a quadratic
frequency loss, regardless of the number of cells. -/
theorem innerBuffer_normalized_remainder_coefficient_envelope {B : BufferData}
    (hB : BufferHypotheses B) {C K coeff j t U ratio k : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hcoeff : 1 ≤ coeff) (hj : 0 ≤ j)
    (hB0 : B.B₀ ≤ coeff) (hlayer : B.layerBound ≤ coeff)
    (hinv : ∀ i, (B.mass i)⁻¹ ≤ coeff) (hmupper : ∀ i, B.mass i ≤ coeff * (1 + j))
    (hact : ∀ i, t ≤ B.action i)
    (hU : 0 ≤ U) (hratio : 0 ≤ ratio) (hUupper : U ≤ coeff) (hratioupper : ratio ≤ coeff)
    (hk : 0 < k) (hkinv : (sqrt k)⁻¹ ≤ coeff) (i : Fin 2) :
    (sqrt 12 * U * ratio + 1) * (innerBufferRemainderEnvelope B C K i / sqrt k) ≤
      ((sqrt 12 + 1) * (2 * K * (1 + 2 * C))) *
        coeff ^ 8 * (1 + j) ^ 2 * exp (-t) := by
  have hcoeff0 : 0 ≤ coeff := zero_le_one.trans hcoeff
  have hcoeff2 : 1 ≤ coeff ^ 2 := by nlinarith only [hcoeff]
  have hprod : U * ratio ≤ coeff ^ 2 := by
    simpa only [pow_two] using mul_le_mul hUupper hratioupper hratio hcoeff0
  have hfirst : sqrt 12 * U * ratio + 1 ≤ (sqrt 12 + 1) * coeff ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hprod (sqrt_nonneg 12)
    nlinarith only [h, hcoeff2]
  have henv := innerBuffer_remainder_coefficient_envelope hB hC hK hcoeff hj
    hB0 hlayer hinv hmupper hact i
  have henv0 : 0 ≤ innerBufferRemainderEnvelope B C K i := by
    unfold innerBufferRemainderEnvelope
    have hBpos : 0 < B.B₀ := hB.2.2.1
    have hlayerpos : 0 < B.layerBound := hB.2.2.2.1
    have hmasspos := buffer_mass_pos hB i
    positivity
  rw [div_eq_mul_inv]
  calc
    _ ≤ ((sqrt 12 + 1) * coeff ^ 2) *
        (((2 * K * (1 + 2 * C)) * coeff ^ 5 * (1 + j) ^ 2 * exp (-t)) * coeff) :=
      mul_le_mul hfirst
        (mul_le_mul henv hkinv (inv_nonneg.mpr (sqrt_nonneg k)) (by positivity))
        (mul_nonneg henv0 (inv_nonneg.mpr (sqrt_nonneg k))) (by positivity)
    _ = _ := by ring

/-- The frequency logarithm from the actual Morse action absorbs the
polynomial coefficient envelope used above. -/
theorem inner_morse_polynomial_envelope (T : MorseChainData) {m : ℕ}
    (hd : T.d m = morseChainInteger m) (hm : 1 ≤ m)
    {j p b A c : ℝ} (hj : 0 ≤ j) (hb : 0 ≤ b) (hA : 1 ≤ A) :
    A * radialE m ^ p * (1 + j) ^ b * exp (-c * (j * sqrt (morseChainA T m))) ≤
      exp ((p + 5 * b + log A) * radialQ m +
        b * log (1 + j * sqrt (morseChainA T m)) - c * (j * sqrt (morseChainA T m))) := by
  have hQ1 : 1 ≤ radialQ m := by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    exact (by nlinarith only [hm'] : (1 : ℝ) ≤ (m : ℝ) ^ 2).trans (radial_nat_sq_le_Q m)
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hlogA := mul_le_mul_of_nonneg_left hQ1 (log_nonneg hA)
  have hfreq := mul_le_mul_of_nonneg_left
    (inner_morse_frequency_log_bound T hd hm hj) hb
  rw [radialE, ← exp_mul, rpow_def_of_pos (by linarith : 0 < 1 + j)]
  rw [← exp_log hApos, ← exp_add, ← exp_add, ← exp_add]
  rw [log_exp]
  apply exp_le_exp.mpr
  nlinarith only [hlogA, hfreq]

end ContinuousFlexibility.Radial
