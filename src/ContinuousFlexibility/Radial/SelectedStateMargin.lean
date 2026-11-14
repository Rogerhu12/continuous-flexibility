module

public import ContinuousFlexibility.Radial.MatchingMatrixAlgebra
public import ContinuousFlexibility.Radial.MorseHeightAngleExclusion
public import ContinuousFlexibility.Radial.HeightJoinTransfer
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Selected angles in the matching boundary coordinates

All lengths in this file are the explicit Euclidean lengths used by
`radialAngleSine`. In particular, the norm on the product `ℝ × ℝ` is not
substituted for a Euclidean length. A single signed frame covers both ends.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

private theorem state_length_pos {v : ℝ × ℝ} (hv : v ≠ (0, 0)) :
    0 < sqrt (v.1 ^ 2 + v.2 ^ 2) := by
  apply sqrt_pos.mpr
  by_cases h₁ : v.1 = 0
  · have h₂ : v.2 ≠ 0 := fun h₂ => hv (Prod.ext h₁ h₂)
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h₂)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h₁) (sq_nonneg _)

theorem radialAngleSine_nonneg (u v : ℝ × ℝ) : 0 ≤ radialAngleSine u v :=
  div_nonneg (abs_nonneg _) (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))

theorem radialAngleSine_comm (u v : ℝ × ℝ) :
    radialAngleSine u v = radialAngleSine v u := by
  have hd : v.1 * u.2 - v.2 * u.1 = -(u.1 * v.2 - u.2 * v.1) := by ring
  rw [radialAngleSine, radialAngleSine, hd, abs_neg,
    mul_comm (sqrt (v.1 ^ 2 + v.2 ^ 2)) (sqrt (u.1 ^ 2 + u.2 ^ 2))]

/-- The action of an arbitrary real two-by-two transfer matrix on a state. -/
def selectedStateTransfer (a b c d : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (a * v.1 + b * v.2, c * v.1 + d * v.2)

theorem selectedStateTransfer_det (a b c d : ℝ) (u v : ℝ × ℝ) :
    (selectedStateTransfer a b c d u).1 * (selectedStateTransfer a b c d v).2 -
        (selectedStateTransfer a b c d u).2 * (selectedStateTransfer a b c d v).1 =
      (a * d - b * c) * (u.1 * v.2 - u.2 * v.1) := by
  simp only [selectedStateTransfer]
  ring

theorem selectedStateTransfer_ne_zero {a b c d : ℝ} (hdet : a * d - b * c ≠ 0)
    {v : ℝ × ℝ} (hv : v ≠ (0, 0)) : selectedStateTransfer a b c d v ≠ (0, 0) := by
  intro h
  have h₁ : a * v.1 + b * v.2 = 0 := congrArg Prod.fst h
  have h₂ : c * v.1 + d * v.2 = 0 := congrArg Prod.snd h
  have hv₁ : (a * d - b * c) * v.1 = 0 := by linear_combination d * h₁ - b * h₂
  have hv₂ : (a * d - b * c) * v.2 = 0 := by linear_combination a * h₂ - c * h₁
  exact hv (Prod.ext ((mul_eq_zero.mp hv₁).resolve_left hdet)
    ((mul_eq_zero.mp hv₂).resolve_left hdet))

/-- Quantitative angle distortion under an invertible linear transfer.
The factor is determinant divided by the square of a Euclidean growth bound. -/
theorem radialAngleSine_transfer_lower (a b c d : ℝ) {K : ℝ} (hK : 0 < K)
    (hdet : a * d - b * c ≠ 0)
    (hbound : ∀ v : ℝ × ℝ,
      sqrt ((selectedStateTransfer a b c d v).1 ^ 2 +
        (selectedStateTransfer a b c d v).2 ^ 2) ≤ K * sqrt (v.1 ^ 2 + v.2 ^ 2))
    {u v : ℝ × ℝ} (hu : u ≠ (0, 0)) (hv : v ≠ (0, 0)) :
    (|a * d - b * c| / K ^ 2) * radialAngleSine u v ≤
      radialAngleSine (selectedStateTransfer a b c d u)
        (selectedStateTransfer a b c d v) := by
  have hpu := state_length_pos hu
  have hpv := state_length_pos hv
  have hTu := state_length_pos (selectedStateTransfer_ne_zero hdet hu)
  have hTv := state_length_pos (selectedStateTransfer_ne_zero hdet hv)
  have hden :
      sqrt ((selectedStateTransfer a b c d u).1 ^ 2 +
          (selectedStateTransfer a b c d u).2 ^ 2) *
        sqrt ((selectedStateTransfer a b c d v).1 ^ 2 +
          (selectedStateTransfer a b c d v).2 ^ 2) ≤
        K ^ 2 * (sqrt (u.1 ^ 2 + u.2 ^ 2) * sqrt (v.1 ^ 2 + v.2 ^ 2)) := by
    calc
      _ ≤ (K * sqrt (u.1 ^ 2 + u.2 ^ 2)) *
          (K * sqrt (v.1 ^ 2 + v.2 ^ 2)) :=
        mul_le_mul (hbound u) (hbound v) hTv.le (mul_nonneg hK.le hpu.le)
      _ = _ := by ring
  rw [radialAngleSine, radialAngleSine, selectedStateTransfer_det, abs_mul]
  apply (le_div_iff₀ (mul_pos hTu hTv)).mpr
  calc
    _ ≤ (|a * d - b * c| / K ^ 2 *
        (|u.1 * v.2 - u.2 * v.1| /
          (sqrt (u.1 ^ 2 + u.2 ^ 2) * sqrt (v.1 ^ 2 + v.2 ^ 2)))) *
        (K ^ 2 * (sqrt (u.1 ^ 2 + u.2 ^ 2) * sqrt (v.1 ^ 2 + v.2 ^ 2))) :=
      mul_le_mul_of_nonneg_left hden
        (mul_nonneg (div_nonneg (abs_nonneg _) (sq_nonneg _))
          (div_nonneg (abs_nonneg _) (mul_nonneg hpu.le hpv.le)))
    _ = |a * d - b * c| * |u.1 * v.2 - u.2 * v.1| := by
      field_simp [hK.ne', hpu.ne', hpv.ne'] <;> ring

/-- The selected-state frame `(u, -u ± z)`, with one orientation parameter. -/
def selectedStateFrame (ε : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  selectedStateTransfer 1 0 (-1) ε v

/-- The inverse frame when the orientation is `+1` or `-1`. -/
def selectedStateUnframe (ε : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  selectedStateTransfer 1 0 ε ε v

theorem selectedStateUnframe_frame {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (v : ℝ × ℝ) :
    selectedStateUnframe ε (selectedStateFrame ε v) = v := by
  rcases hε with rfl | rfl <;> apply Prod.ext <;>
    simp only [selectedStateUnframe, selectedStateFrame, selectedStateTransfer] <;> ring

private theorem signed_frame_length_le {s t : ℝ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (v : ℝ × ℝ) :
    sqrt (v.1 ^ 2 + (s * v.1 + t * v.2) ^ 2) ≤
      2 * sqrt (v.1 ^ 2 + v.2 ^ 2) := by
  apply (sq_le_sq₀ (sqrt_nonneg _)
    (mul_nonneg (by norm_num) (sqrt_nonneg _))).mp
  rw [sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), mul_pow,
    sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp only [one_mul, neg_one_mul] <;>
    nlinarith only [sq_nonneg (v.1 - v.2), sq_nonneg (v.1 + v.2),
      sq_nonneg v.1, sq_nonneg v.2]

theorem selectedStateFrame_length_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (v : ℝ × ℝ) :
    sqrt ((selectedStateFrame ε v).1 ^ 2 + (selectedStateFrame ε v).2 ^ 2) ≤
      2 * sqrt (v.1 ^ 2 + v.2 ^ 2) := by
  simpa only [selectedStateFrame, selectedStateTransfer, one_mul, zero_mul, add_zero] using
    signed_frame_length_le (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1) hε v

theorem selectedStateUnframe_length_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (v : ℝ × ℝ) :
    sqrt ((selectedStateUnframe ε v).1 ^ 2 + (selectedStateUnframe ε v).2 ^ 2) ≤
      2 * sqrt (v.1 ^ 2 + v.2 ^ 2) := by
  simpa only [selectedStateUnframe, selectedStateTransfer, one_mul, zero_mul, add_zero] using
    signed_frame_length_le hε hε v

theorem selectedStateFrame_ne_zero {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {v : ℝ × ℝ} (hv : v ≠ (0, 0)) : selectedStateFrame ε v ≠ (0, 0) := by
  apply selectedStateTransfer_ne_zero (v := v) _ hv
  rcases hε with rfl | rfl <;> norm_num

theorem radialAngleSine_frame_lower {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {u v : ℝ × ℝ} (hu : u ≠ (0, 0)) (hv : v ≠ (0, 0)) :
    (1 / 4 : ℝ) * radialAngleSine u v ≤
      radialAngleSine (selectedStateFrame ε u) (selectedStateFrame ε v) := by
  have habs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hdet : (1 : ℝ) * ε - 0 * (-1) ≠ 0 := by
    rcases hε with rfl | rfl <;> norm_num
  have h := radialAngleSine_transfer_lower 1 0 (-1) ε (K := 2) (by norm_num) hdet
    (selectedStateFrame_length_le hε) hu hv
  simpa only [selectedStateFrame, one_mul, zero_mul, sub_zero, habs,
    show (2 : ℝ) ^ 2 = 4 by norm_num] using h

theorem radialAngleSine_frame_le_four_mul {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {u v : ℝ × ℝ} (hu : u ≠ (0, 0)) (hv : v ≠ (0, 0)) :
    radialAngleSine (selectedStateFrame ε u) (selectedStateFrame ε v) ≤
      4 * radialAngleSine u v := by
  have habs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hdet : (1 : ℝ) * ε - 0 * ε ≠ 0 := by
    rcases hε with rfl | rfl <;> norm_num
  have h := radialAngleSine_transfer_lower 1 0 ε ε (K := 2) (by norm_num) hdet
    (selectedStateUnframe_length_le hε)
    (selectedStateFrame_ne_zero hε hu) (selectedStateFrame_ne_zero hε hv)
  have hiu : selectedStateTransfer 1 0 ε ε (selectedStateFrame ε u) = u :=
    selectedStateUnframe_frame hε u
  have hiv : selectedStateTransfer 1 0 ε ε (selectedStateFrame ε v) = v :=
    selectedStateUnframe_frame hε v
  rw [hiu, hiv] at h
  simp only [one_mul, zero_mul, sub_zero, habs,
    show (2 : ℝ) ^ 2 = 4 by norm_num] at h
  linarith only [h]

/-- Relative Euclidean errors in both transported states lose at most `4η`
in the selected angle. The same lemma applies at either endpoint. -/
theorem radialAngleSine_perturb_lower {u v u' v' : ℝ × ℝ} {δ η : ℝ}
    (hu : u ≠ (0, 0)) (hv : v ≠ (0, 0))
    (hu' : u' ≠ (0, 0)) (hv' : v' ≠ (0, 0))
    (hsep : δ ≤ radialAngleSine u v)
    (huerr : sqrt ((u.1 - u'.1) ^ 2 + (u.2 - u'.2) ^ 2) ≤
      η * sqrt (u.1 ^ 2 + u.2 ^ 2))
    (hverr : sqrt ((v.1 - v'.1) ^ 2 + (v.2 - v'.2) ^ 2) ≤
      η * sqrt (v.1 ^ 2 + v.2 ^ 2)) :
    δ - 4 * η ≤ radialAngleSine u' v' := by
  have h₁ := morseHeightAngleSine_le_add_perturbation hu hu' hv
  have h₂ := morseHeightAngleSine_le_add_perturbation hv hv' hu'
  rw [radialAngleSine_comm v u', radialAngleSine_comm v' u'] at h₂
  have heu : 2 * sqrt ((u.1 - u'.1) ^ 2 + (u.2 - u'.2) ^ 2) /
      sqrt (u.1 ^ 2 + u.2 ^ 2) ≤ 2 * η := by
    apply (div_le_iff₀ (state_length_pos hu)).mpr
    linarith only [huerr]
  have hev : 2 * sqrt ((v.1 - v'.1) ^ 2 + (v.2 - v'.2) ^ 2) /
      sqrt (v.1 ^ 2 + v.2 ^ 2) ≤ 2 * η := by
    apply (div_le_iff₀ (state_length_pos hv)).mpr
    linarith only [hverr]
  linarith only [hsep, h₁, h₂, heu, hev]

theorem radialAngleSine_perturb_half {u v u' v' : ℝ × ℝ} {δ η : ℝ}
    (hu : u ≠ (0, 0)) (hv : v ≠ (0, 0))
    (hu' : u' ≠ (0, 0)) (hv' : v' ≠ (0, 0))
    (hsep : δ ≤ radialAngleSine u v) (hη : η ≤ δ / 8)
    (huerr : sqrt ((u.1 - u'.1) ^ 2 + (u.2 - u'.2) ^ 2) ≤
      η * sqrt (u.1 ^ 2 + u.2 ^ 2))
    (hverr : sqrt ((v.1 - v'.1) ^ 2 + (v.2 - v'.2) ^ 2) ≤
      η * sqrt (v.1 ^ 2 + v.2 ^ 2)) :
    δ / 2 ≤ radialAngleSine u' v' := by
  have h := radialAngleSine_perturb_lower hu hv hu' hv' hsep huerr hverr
  linarith only [h, hη]

/-- A separated normalized state gives the actual diagonal matching margin.
The scalar determinant/sine identity is the existing matching-algebra lemma. -/
theorem normalized_matching_margin {v : ℝ × ℝ} {d δ : ℝ}
    (hv : v.1 ^ 2 + v.2 ^ 2 = 1) (hsep : δ ≤ radialAngleSine v (1, d)) :
    δ ≤ |v.1 * d - v.2| := by
  have hlen : 1 ≤ sqrt (1 + d ^ 2) := by
    have h := sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + d ^ 2 by linarith only [sq_nonneg d])
    simpa only [sqrt_one] using h
  have hmul : radialAngleSine v (1, d) ≤ sqrt (1 + d ^ 2) * radialAngleSine v (1, d) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hlen (radialAngleSine_nonneg v (1, d))
  rw [abs_mul_sub_eq_sqrt_mul_sine v hv d]
  simpa only [radialAngleSine] using hsep.trans hmul

private theorem normalized_state_ne_zero {v : ℝ × ℝ}
    (hv : v.1 ^ 2 + v.2 ^ 2 = 1) : v ≠ (0, 0) := by
  intro hz
  rw [hz] at hv
  norm_num at hv

private theorem slope_state_ne_zero (d : ℝ) : (1, d) ≠ ((0, 0) : ℝ × ℝ) := by
  intro h
  have h₁ : (1 : ℝ) = 0 := congrArg Prod.fst h
  exact one_ne_zero h₁

/-- Passing from a selected frame to the normalized physical state costs
only the fixed factor four, including the case of zero boundary value. -/
theorem normalized_matching_margin_of_frame {ε d δ : ℝ} {v : ℝ × ℝ}
    (hε : ε = 1 ∨ ε = -1) (hv : v.1 ^ 2 + v.2 ^ 2 = 1)
    (hsep : δ ≤ radialAngleSine (selectedStateFrame ε v)
      (selectedStateFrame ε (1, d))) :
    δ / 4 ≤ |v.1 * d - v.2| := by
  apply normalized_matching_margin hv
  have h := radialAngleSine_frame_le_four_mul hε (normalized_state_ne_zero hv)
    (slope_state_ne_zero d)
  linarith only [hsep, h]

/-- The complete small-transfer-to-matching estimate. Both incoming and
natural states may change by a relative Euclidean error at most `δ/8`. -/
theorem normalized_matching_margin_of_perturbed_frame
    {ε d δ η : ℝ} {u w v : ℝ × ℝ}
    (hε : ε = 1 ∨ ε = -1) (hv : v.1 ^ 2 + v.2 ^ 2 = 1)
    (hu : u ≠ (0, 0)) (hw : w ≠ (0, 0))
    (hsep : δ ≤ radialAngleSine u w) (hη : η ≤ δ / 8)
    (huerr : sqrt ((u.1 - (selectedStateFrame ε v).1) ^ 2 +
      (u.2 - (selectedStateFrame ε v).2) ^ 2) ≤ η * sqrt (u.1 ^ 2 + u.2 ^ 2))
    (hwerr : sqrt ((w.1 - (selectedStateFrame ε (1, d)).1) ^ 2 +
      (w.2 - (selectedStateFrame ε (1, d)).2) ^ 2) ≤ η * sqrt (w.1 ^ 2 + w.2 ^ 2)) :
    δ / 8 ≤ |v.1 * d - v.2| := by
  have hangle := radialAngleSine_perturb_half hu hw
    (selectedStateFrame_ne_zero hε (normalized_state_ne_zero hv))
    (selectedStateFrame_ne_zero hε (slope_state_ne_zero d)) hsep hη huerr hwerr
  have h := normalized_matching_margin_of_frame hε hv hangle
  convert h using 1 <;> ring

/-- The physical flux normalization and the selected state differ by exactly
the signed frame above. Taking `ε = 1` or `ε = -1` covers the two outward radii. -/
theorem radialState_eq_selectedStateFrame (D : ReferenceData) {j : ℕ} {r ε : ℝ}
    (hj : (j : ℝ) ≠ 0) (hr : r ≠ 0) (hw : D.w r ≠ 0)
    (hε : ε = 1 ∨ ε = -1) (u : ℝ → ℝ) :
    radialState D j r (D.w r) u = selectedStateFrame ε
      (u r, ε * D.w r * deriv u r / ((j : ℝ) ^ 2 * D.w r / r)) := by
  rcases hε with rfl | rfl <;> apply Prod.ext <;>
    simp only [radialState, selectedStateFrame, selectedStateTransfer] <;>
    field_simp [hj, hr, hw] <;> ring

end ContinuousFlexibility.Radial
