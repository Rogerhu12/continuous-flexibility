import ContinuousFlexibility.Radial.InnerCentralBufferCoefficients
import ContinuousFlexibility.Radial.InnerModelCoefficientEnvelope
import ContinuousFlexibility.Radial.InnerFrequencySuppression

/-!
# One central cut for all compressed even modes

The full-model inverse and the temporary border are fixed before the
cut is chosen. R09 supplies its original compression constants first;
the envelope amplitude may then absorb those constants and any later
fixed normalization costs. A single sufficiently large central cut
constructs the actual localized inverse and Poisson data for every even
mode, and suppresses the common envelope even after multiplication by
the frequency. The requested initial cut may depend on an already
chosen tail index.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

def innerCentralCompressionAmplitude (C : ℝ) : ℝ :=
  max 1 (innerCentralBufferCoefficientLinearConstant C ^ 8)

theorem innerCentralCompressionAmplitude_ge_one (C : ℝ) :
    1 ≤ innerCentralCompressionAmplitude C := le_max_left _ _

def innerCentralCompressionEnvelope (A X₀ j : ℝ) : ℝ :=
  A * (1 + X₀ ^ 2) ^ 8 * (1 + j) ^ 2 * exp (-(X₀ ^ 2 / 16) * j)

/-- The same degree eight controls every raw coefficient power needed
by compression and by the normalized physical Poisson remainder. -/
theorem innerCentralBufferCoefficient_pow_le {X₀ C A : ℝ}
    (hX : 1 ≤ X₀) (hC : 0 ≤ C)
    (hA : innerCentralCompressionAmplitude C ≤ A) {k : ℕ} (hk : k ≤ 8) :
    innerCentralBufferCoefficient X₀ C ^ k ≤ A * (1 + X₀ ^ 2) ^ 8 := by
  have hX0 : 0 ≤ X₀ := zero_le_one.trans hX
  have hc := innerCentralBufferCoefficient_base hX0 hC
  have hc1 : 1 ≤ innerCentralBufferCoefficient X₀ C :=
    (show (1 : ℝ) ≤ 1 + 2 * C by linarith only [hC]).trans hc.1
  have hlinear := innerCentralBufferCoefficient_le_linear hX hC
  have hpow := pow_le_pow_left₀ (zero_le_one.trans hc1) hlinear 8
  rw [mul_pow] at hpow
  have hXbound : X₀ ≤ 1 + X₀ ^ 2 := by
    nlinarith only [hX, sq_nonneg (X₀ - 1)]
  have hXpow := pow_le_pow_left₀ hX0 hXbound 8
  have hKA : innerCentralBufferCoefficientLinearConstant C ^ 8 ≤ A :=
    (le_max_right _ _).trans hA
  have hA0 : 0 ≤ A := zero_le_one.trans
    ((innerCentralCompressionAmplitude_ge_one C).trans hA)
  exact (pow_le_pow_right₀ hc1 hk).trans (hpow.trans
    (mul_le_mul hKA hXpow (pow_nonneg hX0 8) hA0))

/-- The original R09 smallness expression is derived from the actual
central masses and action, before a compressed inverse is constructed. -/
theorem innerCentral_compression_envelope_le {n : ℕ} (hn : 1 ≤ n)
    {X₀ C A : ℝ} (hX : 8 ≤ X₀) (hC : 0 ≤ C)
    (hB : BufferHypotheses (innerCentralBufferData n X₀))
    (hA : innerCentralCompressionAmplitude C ≤ A) (i : Fin 2) :
    let B := innerCentralBufferData n X₀
    B.B₀ * B.mass i ^ 2 * exp (-B.action i) ≤
      innerCentralCompressionEnvelope A X₀ (2 * n) := by
  dsimp only
  have hc := innerCentralBufferCoefficient_bounds hn hX hC
  have hj0 : (0 : ℝ) ≤ 2 * n := mul_nonneg (by norm_num) (Nat.cast_nonneg n)
  have hact (i : Fin 2) : (X₀ ^ 2 / 16) * (2 * n) ≤
      (innerCentralBufferData n X₀).action i := (innerCentralBuffer_action n X₀ i).ge
  have hcompression := innerBuffer_compression_coefficient_envelope hB hc.1 hj0
    hc.2.1 hc.2.2.2.2.1 hact i
  have hcommon := innerCentralBufferCoefficient_pow_le
    ((by norm_num : (1 : ℝ) ≤ 8).trans hX) hC hA (by norm_num : 3 ≤ 8)
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcommon (sq_nonneg (1 + (2 : ℝ) * n)))
    (exp_pos (-((X₀ ^ 2 / 16) * (2 * n)))).le
  simpa only [innerCentralCompressionEnvelope, neg_mul] using hcompression.trans hbound

/-- The polynomial envelope has exactly the logarithmic form used in
the uniform product-frequency suppression theorem. -/
theorem innerCentralCompressionEnvelope_eq_exp {A X₀ j : ℝ}
    (hA : 0 < A) (hj : 0 ≤ j) :
    innerCentralCompressionEnvelope A X₀ j =
      exp (log A + 2 * log (1 + j) + 8 * log (1 + X₀ ^ 2) -
        (1 / 16 : ℝ) * j * X₀ ^ 2) := by
  have hL : 0 < 1 + X₀ ^ 2 := by positivity
  have hj1 : 0 < 1 + j := by linarith only [hj]
  have hLexp : (1 + X₀ ^ 2) ^ 8 = exp (8 * log (1 + X₀ ^ 2)) := by
    simpa only [exp_log hL] using (exp_nat_mul (log (1 + X₀ ^ 2)) 8).symm
  have hjexp : (1 + j) ^ 2 = exp (2 * log (1 + j)) := by
    simpa only [exp_log hj1] using (exp_nat_mul (log (1 + j)) 2).symm
  calc
    innerCentralCompressionEnvelope A X₀ j =
        exp (log A) * exp (8 * log (1 + X₀ ^ 2)) * exp (2 * log (1 + j)) *
          exp (-(X₀ ^ 2 / 16) * j) := by
      rw [innerCentralCompressionEnvelope, exp_log hA, ← hLexp, ← hjexp]
    _ = exp (log A + 2 * log (1 + j) + 8 * log (1 + X₀ ^ 2) -
        (1 / 16 : ℝ) * j * X₀ ^ 2) := by
      rw [← exp_add, ← exp_add, ← exp_add]
      congr 1
      ring

/-- A single far cut constructs the genuine localized central data at
all positive even modes. The amplitude can be increased after C and K
are known, and the cut can be selected after any prescribed initial
floor; no compressed data or final smallness estimate is an input. -/
theorem exists_innerCentralLocalizedChoices (hR09 : R09Statement) :
    ∃ C K ε : ℝ, 0 < C ∧ 0 < K ∧ 0 < ε ∧
      ∀ A : ℝ, innerCentralCompressionAmplitude C ≤ A →
      ∀ η : ℝ, 0 < η → ∀ initial : ℝ, ∃ X₀ : ℝ,
        initial ≤ X₀ ∧ 8 ≤ X₀ ∧
        (∀ j : ℝ, 2 ≤ j → 2 * C * centralRadiusA ≤ innerCentralCapMass j X₀) ∧
        ∀ n : ℕ, 1 ≤ n →
          BufferHypotheses (innerCentralBufferData n X₀) ∧
          Nonempty (InnerBufferLocalizedData (innerCentralBufferData n X₀) C K) ∧
          innerCentralCompressionEnvelope A X₀ (2 * n) < η ∧
          (2 * n : ℝ) * innerCentralCompressionEnvelope A X₀ (2 * n) < η := by
  obtain ⟨C, ε, hC, hε, hcompress⟩ := hR09 (64 + 16 * centralRadiusA ^ 2)
    (by positivity)
  obtain ⟨K, hK, hlocalized⟩ := exists_innerBufferLocalizedData
  refine ⟨C, K, ε, hC, hK, hε, ?_⟩
  intro A hA η hη initial
  have hApos : 0 < A := zero_lt_one.trans_le
    ((innerCentralCompressionAmplitude_ge_one C).trans hA)
  obtain ⟨L₀, hL₀, hsmall⟩ := inner_product_frequency_suppression
    (A := log A) (b := 2) (d := 8) (c := 1 / 16) (η := min ε η)
    (by norm_num) (by norm_num) (by norm_num) (lt_min hε hη)
  obtain ⟨X₀, hinit, hX, hB, hmass⟩ := exists_innerCentralBufferCut C (max initial L₀)
  have hLX : L₀ ≤ X₀ := (le_max_right _ _).trans hinit
  have hX1 : 1 ≤ X₀ := hL₀.trans hLX
  have hLs : L₀ ≤ X₀ ^ 2 := hLX.trans
    (by nlinarith only [hX1, sq_nonneg (X₀ - 1)] : X₀ ≤ X₀ ^ 2)
  refine ⟨X₀, (le_max_left _ _).trans hinit, hX, hmass, ?_⟩
  intro n hn
  have hj := innerCentralBuffer_frequency hn
  have hj0 : (0 : ℝ) ≤ 2 * n := (by norm_num : (0 : ℝ) ≤ 2).trans hj
  have henv := innerCentralCompressionEnvelope_eq_exp (X₀ := X₀) hApos hj0
  have hs : innerCentralCompressionEnvelope A X₀ (2 * n) < min ε η ∧
      (2 * n : ℝ) * innerCentralCompressionEnvelope A X₀ (2 * n) < min ε η := by
    simpa only [henv] using hsmall (X₀ ^ 2) hLs (2 * n)
      ((by norm_num : (1 : ℝ) ≤ 2).trans hj)
  have htol (i : Fin 2) :=
    (innerCentral_compression_envelope_le hn hX hC.le (hB n hn) hA i).trans_lt
      (hs.1.trans_le (min_le_left ε η))
  have hconclusion := hcompress (innerCentralBufferData n X₀) (by exact le_rfl)
    (hB n hn) htol
  exact ⟨hB n hn, hlocalized _ C (hB n hn) hconclusion,
    hs.1.trans_le (min_le_right ε η), hs.2.trans_le (min_le_right ε η)⟩

end ContinuousFlexibility.Radial
