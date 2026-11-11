import ContinuousFlexibility.Scalar.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positivity of the remainder metric

Pointwise algebra for Section 3, equations `height-jet-notation` and the
following positivity assertion. The quadratic form is the actual coordinate
expression of the remainder metric; no positivity hypothesis is built into
its definition.
-/

namespace ContinuousFlexibility

theorem radialEnergy_pos (w : ℝ) : 0 < radialEnergy w := by
  dsimp [radialEnergy]
  nlinarith [sq_nonneg w]

/-- Positive discriminant forces the angular diagonal factor to be positive. -/
theorem angular_factor_pos_of_discriminant_pos {E k p : ℝ}
    (hE : 0 < E) (hD : 0 < heightDiscriminant E k p) :
    0 < 1 - p ^ 2 := by
  by_contra hn
  have hc : 1 - p ^ 2 ≤ 0 := le_of_not_gt hn
  have hp : E * (1 - p ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hE) hc
  dsimp [heightDiscriminant] at hD
  nlinarith [sq_nonneg k]

/-- Positive discriminant also forces the radial diagonal entry to be positive. -/
theorem radial_factor_pos_of_discriminant_pos {E k p : ℝ}
    (hE : 0 < E) (hD : 0 < heightDiscriminant E k p) :
    0 < E - k ^ 2 := by
  have hp : 0 ≤ E * p ^ 2 := mul_nonneg (le_of_lt hE) (sq_nonneg p)
  dsimp [heightDiscriminant] at hD
  nlinarith

/-- The discriminant criterion is equivalently the coordinate inequality for
the squared norm of the height differential in the radial reference metric.
Identification with a geometric cotangent norm remains a separate step. -/
theorem discriminant_pos_iff_height_norm_sq_lt_one {E k p : ℝ}
    (hE : 0 < E) :
    0 < heightDiscriminant E k p ↔ k ^ 2 / E + p ^ 2 < 1 := by
  constructor
  · intro hD
    have hk : k ^ 2 < (1 - p ^ 2) * E := by
      dsimp [heightDiscriminant] at hD
      nlinarith
    have hk' : k ^ 2 / E < 1 - p ^ 2 := (div_lt_iff₀ hE).2 hk
    linarith
  · intro h
    have hk : k ^ 2 / E < 1 - p ^ 2 := by linarith
    have hk' : k ^ 2 < (1 - p ^ 2) * E := (div_lt_iff₀ hE).1 hk
    dsimp [heightDiscriminant]
    nlinarith

/-- Determinant of the symmetric coordinate matrix of the remainder metric. -/
theorem remainder_matrix_determinant (r E k p : ℝ) :
    (E - k ^ 2) * (r ^ 2 * (1 - p ^ 2)) - (-r * k * p) ^ 2 =
      r ^ 2 * heightDiscriminant E k p := by
  dsimp [heightDiscriminant]
  ring

/-- Completion of the square without divisions, valid even at degeneracy. -/
theorem remainder_complete_square (r E k p x y : ℝ) :
    (1 - p ^ 2) * remainderQuadratic r E k p x y =
      heightDiscriminant E k p * x ^ 2 +
        (r * (1 - p ^ 2) * y - k * p * x) ^ 2 := by
  dsimp [remainderQuadratic, heightDiscriminant]
  ring

theorem remainderPositive_of_discriminant_pos {r E k p : ℝ}
    (hr : 0 < r) (hE : 0 < E) (hD : 0 < heightDiscriminant E k p) :
    RemainderPositive r E k p := by
  have hc := angular_factor_pos_of_discriminant_pos hE hD
  intro x y hxy
  by_cases hx : x = 0
  · have hy : y ≠ 0 := hxy.resolve_left (not_not.mpr hx)
    have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    simpa [remainderQuadratic, hx] using mul_pos (mul_pos hr2 hc) hy2
  · have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    have hprod : 0 < (1 - p ^ 2) * remainderQuadratic r E k p x y := by
      rw [remainder_complete_square]
      exact add_pos_of_pos_of_nonneg (mul_pos hD hx2) (sq_nonneg _)
    by_contra hq
    have hq' : remainderQuadratic r E k p x y ≤ 0 := le_of_not_gt hq
    have hn := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hq'
    exact (not_lt_of_ge hn) hprod

/-- Positive definiteness implies positive discriminant; this direction does
not require positivity of the reference coefficient `E`. -/
theorem discriminant_pos_of_remainderPositive {r E k p : ℝ}
    (hr : 0 < r) (hpos : RemainderPositive r E k p) :
    0 < heightDiscriminant E k p := by
  have h01 := hpos 0 1 (Or.inr one_ne_zero)
  have hrc : 0 < r ^ 2 * (1 - p ^ 2) := by
    simpa [remainderQuadratic] using h01
  have hc : 0 < 1 - p ^ 2 := by
    by_contra hn
    have hn' : 1 - p ^ 2 ≤ 0 := le_of_not_gt hn
    have hp := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) hn'
    exact (not_lt_of_ge hp) hrc
  have hx : 0 < r * (1 - p ^ 2) := mul_pos hr hc
  have hval := hpos (r * (1 - p ^ 2)) (k * p) (Or.inl (ne_of_gt hx))
  have hid :
      (1 - p ^ 2) * remainderQuadratic r E k p (r * (1 - p ^ 2)) (k * p) =
        heightDiscriminant E k p * (r * (1 - p ^ 2)) ^ 2 := by
    dsimp [remainderQuadratic, heightDiscriminant]
    ring
  have hprod : 0 < heightDiscriminant E k p * (r * (1 - p ^ 2)) ^ 2 := by
    rw [← hid]
    exact mul_pos hc hval
  by_contra hn
  have hn' : heightDiscriminant E k p ≤ 0 := le_of_not_gt hn
  have hp := mul_nonpos_of_nonpos_of_nonneg hn' (sq_nonneg (r * (1 - p ^ 2)))
  exact (not_lt_of_ge hp) hprod

/-- The pointwise positivity criterion stated immediately after
`height-jet-notation` in Section 3 of the manuscript. -/
theorem remainderPositive_iff_discriminant_pos {r E k p : ℝ}
    (hr : 0 < r) (hE : 0 < E) :
    RemainderPositive r E k p ↔ 0 < heightDiscriminant E k p :=
  ⟨discriminant_pos_of_remainderPositive hr,
    remainderPositive_of_discriminant_pos hr hE⟩

/-- The same criterion specialized to the radial metric coefficient `1+w²`. -/
theorem radial_remainderPositive_iff_discriminant_pos {r w k p : ℝ}
    (hr : 0 < r) :
    RemainderPositive r (radialEnergy w) k p ↔
      0 < heightDiscriminant (radialEnergy w) k p :=
  remainderPositive_iff_discriminant_pos hr (radialEnergy_pos w)

end ContinuousFlexibility
