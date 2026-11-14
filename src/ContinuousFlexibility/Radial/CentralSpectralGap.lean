module

public import ContinuousFlexibility.Radial.OscillatorSpectrum

/-!
# Uniform arithmetic separation of the central oscillator levels

This proves the numerical separation in Section 4, equations
`central-spectrum-new`--`rad-eq-sc3`, for the eigenfunctions already
constructed in `OscillatorSpectrum`. It does not identify a closed
operator domain or assert a resolvent norm bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real

/-- The genuine energy of the constructed central Hermite mode. -/
def centralSpectralLevel (j : ℝ) (m : ℕ) : ℝ :=
  j * (2 * (m : ℝ) + 1) + centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA

def centralGapDelta : ℝ := (3 / 4 : ℝ) * (3 - 2 * sqrt 2)

theorem centralOscillatorA_eq_sqrt_half : centralOscillatorA = sqrt 2 / 2 := by
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : sqrt (2 : ℝ) ≠ 0 := (sqrt_pos.mpr (by norm_num)).ne'
  unfold centralOscillatorA
  apply (div_eq_iff hn).mpr
  nlinarith

theorem centralOscillatorA_sq : centralOscillatorA ^ 2 = (1 / 2 : ℝ) := by
  rw [centralOscillatorA_eq_sqrt_half, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem centralGapDelta_pos : 0 < centralGapDelta := by
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := sqrt_nonneg (2 : ℝ)
  unfold centralGapDelta
  nlinarith

theorem centralGapDelta_lt_one : centralGapDelta < 1 := by
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := sqrt_nonneg (2 : ℝ)
  unfold centralGapDelta
  nlinarith

private theorem integer_gap {x δ : ℝ}
    (hlo : 1 + δ ≤ x) (hhi : x ≤ 2 - δ) (z : ℤ) :
    δ ≤ |x - (z : ℝ)| := by
  by_cases hz : z ≤ 1
  · have hz' : (z : ℝ) ≤ 1 := by exact_mod_cast hz
    linarith [le_abs_self (x - (z : ℝ))]
  · have hz2 : (2 : ℤ) ≤ z := by omega
    have hz' : (2 : ℝ) ≤ z := by exact_mod_cast hz2
    linarith [neg_le_abs (x - (z : ℝ))]

/-- The irrational norm lies in a fixed interval separated from every
integer, uniformly in the frequency. -/
theorem central_norm_between {j : ℝ} (hj : 4 ≤ j) :
    1 + centralGapDelta ≤
      2 * centralOscillatorA * centralRadiusA ^ 2 - centralRadiusA ^ 4 / j ^ 2 ∧
    2 * centralOscillatorA * centralRadiusA ^ 2 - centralRadiusA ^ 4 / j ^ 2 ≤
      2 - centralGapDelta := by
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := sqrt_nonneg (2 : ℝ)
  have hb : centralRadiusA ^ 2 = 2 * sqrt 2 - 2 := by
    rw [centralRadiusA_sq, centralOscillatorA_eq_sqrt_half]
    ring
  have hb4 : centralRadiusA ^ 4 = 12 - 8 * sqrt 2 := by
    rw [show centralRadiusA ^ 4 = (centralRadiusA ^ 2) ^ 2 by ring, hb]
    nlinarith
  have hprod : 2 * centralOscillatorA * centralRadiusA ^ 2 = 4 - 2 * sqrt 2 := by
    rw [centralOscillatorA_eq_sqrt_half, hb]
    nlinarith
  have hj2 : (16 : ℝ) ≤ j ^ 2 := by nlinarith
  have hq := div_le_div_of_nonneg_left (sq_nonneg (centralRadiusA ^ 2))
    (by norm_num : (0 : ℝ) < 16) hj2
  rw [← pow_mul, show (2 * 2 : ℕ) = 4 by norm_num] at hq
  have hq0 : 0 ≤ centralRadiusA ^ 4 / j ^ 2 := by positivity
  rw [hb4] at hq0 hq
  rw [hprod, hb4]
  unfold centralGapDelta
  constructor <;> nlinarith

/-- The actual central mode-two energy levels are `4m`. -/
theorem centralSpectralLevel_two (m : ℕ) : centralSpectralLevel 2 m = 4 * (m : ℝ) := by
  unfold centralSpectralLevel
  rw [centralRadiusA_sq]
  ring

/-- Uniform numerical zero-energy gap at every other even frequency.
The quantifiers use one fixed central geometry and one fixed constant. -/
theorem centralSpectralLevel_even_gap (n m : ℕ) (hn : 2 ≤ n) :
    centralGapDelta / 2 ≤ |centralSpectralLevel (2 * (n : ℝ)) m| := by
  let j : ℝ := 2 * (n : ℝ)
  let M : ℝ := 2 * (m : ℝ) + 1
  let b : ℝ := centralRadiusA ^ 2
  let φ : ℝ := j * centralOscillatorA - b / j
  let E : ℝ := centralSpectralLevel j m
  let N : ℝ := 2 * centralOscillatorA * b - b ^ 2 / j ^ 2
  let z : ℤ := 2 * (n : ℤ) ^ 2 - (2 * (m : ℤ) + 1) ^ 2
  have hj : 4 ≤ j := by dsimp [j]; exact_mod_cast (show 4 ≤ 2 * n by omega)
  have hj0 : 0 < j := by linarith
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hA : centralOscillatorA ≤ 1 := by
    rw [centralOscillatorA_eq_sqrt_half]
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrt_nonneg (2 : ℝ)]
  have hb : (1 / 2 : ℝ) < b := by
    dsimp [b]
    rw [centralRadiusA_sq]
    linarith [centralOscillatorA_gt_two_thirds]
  have hN := central_norm_between hj
  have hbpow : centralRadiusA ^ 4 = b ^ 2 := by dsimp [b]; ring
  rw [hbpow] at hN
  change 1 + centralGapDelta ≤ N ∧ N ≤ 2 - centralGapDelta at hN
  have hnorm : j ^ 2 / 2 - φ ^ 2 = N := by
    dsimp [φ, N]
    field_simp [hj0.ne']
    ring_nf
    rw [centralOscillatorA_sq]
    ring
  have hz : (z : ℝ) = j ^ 2 / 2 - M ^ 2 := by
    dsimp [z, j, M]
    push_cast
    ring
  have hgap : centralGapDelta ≤ |M ^ 2 - φ ^ 2| := by
    have hh := integer_gap hN.1 hN.2 z
    rwa [hz, ← hnorm, show j ^ 2 / 2 - φ ^ 2 - (j ^ 2 / 2 - M ^ 2) =
      M ^ 2 - φ ^ 2 by ring] at hh
  have hE : E = j * (M - φ) := by
    dsimp [E, centralSpectralLevel, M, φ]
    field_simp [hj0.ne']
    ring
  change centralGapDelta / 2 ≤ |E|
  by_cases he : 1 ≤ |E|
  · linarith [centralGapDelta_lt_one]
  have he1 : E < 1 := lt_of_le_of_lt (le_abs_self E) (lt_of_not_ge he)
  have hφ : 0 < φ := by
    have hprod : j ≤ j * M := by nlinarith
    nlinarith [hE]
  have hsum : M + φ ≤ 2 * j := by
    have hid : j * (M + φ) = 2 * j ^ 2 * centralOscillatorA - 2 * b + E := by
      dsimp [E, centralSpectralLevel, M, φ]
      field_simp [hj0.ne']
      ring
    nlinarith [mul_le_mul_of_nonneg_left hA (sq_nonneg j)]
  have hfactor : |M ^ 2 - φ ^ 2| = |M - φ| * (M + φ) := by
    rw [show M ^ 2 - φ ^ 2 = (M - φ) * (M + φ) by ring, abs_mul,
      abs_of_pos (by linarith : 0 < M + φ)]
  have hmul := mul_le_mul_of_nonneg_left hsum (abs_nonneg (M - φ))
  have hEabs : |E| = j * |M - φ| := by rw [hE, abs_mul, abs_of_pos hj0]
  rw [hfactor] at hgap
  nlinarith

/-- Direct connection to the actual differential eigen-equation. -/
theorem central_normalizedHermite_spectralLevel
    {j : ℝ} (hj : 0 < j) (m : ℕ) (x : ℝ) :
    liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
      (normalizedOscillatorHermite j m) x =
      centralSpectralLevel j m * normalizedOscillatorHermite j m x :=
  central_normalizedHermite_equation hj m x

end ContinuousFlexibility.Radial
