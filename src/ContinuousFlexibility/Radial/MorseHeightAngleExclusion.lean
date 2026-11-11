import ContinuousFlexibility.Statements.RadialTargets

/-!
# One-coordinate exclusion for the Morse height choice

The height parameter changes the second component of the outgoing state.
The public angle is computed with the Euclidean length of both states.
A small angle confines the height parameter to an interval of controlled length.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory

set_option backward.isDefEq.respectTransparency false

def morseHeightOuterState (Ξ σ : ℝ) (B : ℝ × ℝ) : ℝ × ℝ :=
  (B.1, σ * Ξ * B.2)

def morseHeightAngleBadSet (Ξ δ : ℝ) (incoming : ℝ → ℝ × ℝ) (B : ℝ × ℝ) : Set ℝ :=
  {σ | σ ∈ Icc (1 : ℝ) 2 ∧
    Statements.radialAngleSine (incoming σ) (morseHeightOuterState Ξ σ B) < δ}

private theorem morseHeight_slope_abs_le {a : ℝ} (ha : a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2)) :
    |a| ≤ (3 : ℝ) / 2 := abs_le.mpr ⟨by linarith only [ha.1], ha.2.trans (by norm_num)⟩

private theorem morseHeight_slope_length_le {a : ℝ} (ha : a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2)) :
    sqrt (1 + a ^ 2) ≤ 2 := by
  have hs : a ^ 2 ≤ ((3 : ℝ) / 2) ^ 2 := by
    rw [← sq_abs a]
    exact (sq_le_sq₀ (abs_nonneg a) (by norm_num)).2 (morseHeight_slope_abs_le ha)
  calc
    _ ≤ sqrt ((2 : ℝ) ^ 2) := sqrt_le_sqrt (by linarith only [hs])
    _ = _ := sqrt_sq (by norm_num)

theorem morseHeightAngle_vertical_ge_half {a t : ℝ}
    (ha : a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2)) (ht : t ≠ 0) :
    (1 : ℝ) / 2 ≤ Statements.radialAngleSine (1, a) (0, t) := by
  have hs : 0 < sqrt (1 + a ^ 2) := sqrt_pos.mpr (by positivity)
  have he : Statements.radialAngleSine (1, a) (0, t) = 1 / sqrt (1 + a ^ 2) := by
    change |1 * t - a * 0| / (sqrt (1 ^ 2 + a ^ 2) * sqrt (0 ^ 2 + t ^ 2)) = _
    simp only [one_mul, mul_zero, sub_zero, one_pow, zero_pow (by decide : 2 ≠ 0), zero_add, sqrt_sq_eq_abs]
    simpa only [one_mul] using mul_div_mul_right (1 : ℝ) (sqrt (1 + a ^ 2)) (abs_pos.mpr ht).ne'
  rw [he]
  exact one_div_le_one_div_of_le hs (morseHeight_slope_length_le ha)

/-- The actual height-scaled state gives the slope `σ Ξ B₂ / B₁`. -/
theorem morseHeightAngle_slope_formula (a Ξ σ : ℝ) (B : ℝ × ℝ) (hB₁ : B.1 ≠ 0) :
    Statements.radialAngleSine (1, a) (morseHeightOuterState Ξ σ B) =
      |a - σ * Ξ * B.2 / B.1| /
        (sqrt (1 + a ^ 2) * sqrt (1 + (σ * Ξ * B.2 / B.1) ^ 2)) := by
  let b := σ * Ξ * B.2 / B.1
  have hb : B.1 * b = σ * Ξ * B.2 := mul_div_cancel₀ _ hB₁
  change |1 * (σ * Ξ * B.2) - a * B.1| /
    (sqrt (1 ^ 2 + a ^ 2) * sqrt (B.1 ^ 2 + (σ * Ξ * B.2) ^ 2)) =
      |a - b| / (sqrt (1 + a ^ 2) * sqrt (1 + b ^ 2))
  have hDet : |1 * (σ * Ξ * B.2) - a * B.1| = |a - b| * |B.1| := by
    rw [← hb, show 1 * (B.1 * b) - a * B.1 = (b - a) * B.1 by ring,
      abs_mul, abs_sub_comm b a]
  have hLen : sqrt (B.1 ^ 2 + (σ * Ξ * B.2) ^ 2) = sqrt (1 + b ^ 2) * |B.1| := by
    rw [← hb, show B.1 ^ 2 + (B.1 * b) ^ 2 = B.1 ^ 2 * (1 + b ^ 2) by ring,
      sqrt_mul (sq_nonneg B.1), sqrt_sq_eq_abs, mul_comm]
  rw [hDet, hLen, one_pow, ← mul_assoc]
  exact mul_div_mul_right _ _ (abs_pos.mpr hB₁).ne'

private theorem morseHeight_small_angle_slope {a b δ : ℝ}
    (ha : a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2)) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 24)
    (hbad : |a - b| / (sqrt (1 + a ^ 2) * sqrt (1 + b ^ 2)) < δ) :
    |a - b| < 6 * δ ∧ b < -(1 / 4 : ℝ) := by
  have hSa : 0 < sqrt (1 + a ^ 2) := sqrt_pos.mpr (by positivity)
  have hSb : 0 < sqrt (1 + b ^ 2) := sqrt_pos.mpr (by positivity)
  have hLb : sqrt (1 + b ^ 2) ≤ 1 + |b| := by
    calc
      _ ≤ sqrt ((1 + |b|) ^ 2) := sqrt_le_sqrt (by nlinarith only [abs_nonneg b, sq_abs b])
      _ = _ := sqrt_sq (by positivity)
  have hdist : |a - b| < 2 * δ * (1 + |b|) := by
    refine ((div_lt_iff₀ (mul_pos hSa hSb)).mp hbad).trans_le ?_
    calc
      _ ≤ δ * (2 * (1 + |b|)) := mul_le_mul_of_nonneg_left
        (mul_le_mul (morseHeight_slope_length_le ha) hLb hSb.le (by norm_num)) hδ.le
      _ = _ := by ring
  have hbTriangle : |b| ≤ |a| + |a - b| := by
    calc
      _ = |a + (b - a)| := by congr 1; ring
      _ ≤ |a| + |b - a| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm b a]
  have hbAbs : |b| < 2 := by
    have h := mul_le_mul_of_nonneg_right (show 2 * δ ≤ (1 : ℝ) / 8 by linarith only [hδsmall])
      (show 0 ≤ 1 + |b| by positivity)
    linarith only [h, hdist, hbTriangle, morseHeight_slope_abs_le ha]
  have hclose : |a - b| < 6 * δ := by
    refine hdist.trans_le ?_
    calc
      _ ≤ (2 * δ) * 3 := mul_le_mul_of_nonneg_left (by linarith only [hbAbs]) (by positivity)
      _ = _ := by ring
  exact ⟨hclose, by linarith only [hclose, hδsmall, ha.2, neg_le_abs (a - b)]⟩

/-- The excluded heights for the ideal incoming line lie in an interval of
length at most `96 δ`, uniformly in the positive contrast and outgoing line. -/
theorem morseHeightAngle_ideal_bad_interval {a Ξ δ : ℝ} {B : ℝ × ℝ}
    (ha : a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2)) (hΞ : 0 < Ξ) (hB : B ≠ (0, 0))
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 24) :
    ∃ l u : ℝ, l ≤ u ∧ u - l ≤ 96 * δ ∧
      morseHeightAngleBadSet Ξ δ (fun _ => (1, a)) B ⊆ Icc l u := by
  let bad := morseHeightAngleBadSet Ξ δ (fun _ => (1, a)) B
  by_cases hnonempty : bad.Nonempty
  · obtain ⟨σ₀, hσ₀⟩ := hnonempty
    have hσ₀in : σ₀ ∈ Icc (1 : ℝ) 2 := hσ₀.1
    have hσ₀bad : Statements.radialAngleSine (1, a) (morseHeightOuterState Ξ σ₀ B) < δ := hσ₀.2
    have hB₁ : B.1 ≠ 0 := by
      intro h0
      have hB₂ : B.2 ≠ 0 := fun h => hB (Prod.ext h0 h)
      have ht : σ₀ * Ξ * B.2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (zero_lt_one.trans_le hσ₀in.1).ne' hΞ.ne') hB₂
      have he : morseHeightOuterState Ξ σ₀ B = (0, σ₀ * Ξ * B.2) := Prod.ext h0 rfl
      rw [he] at hσ₀bad
      linarith only [hσ₀bad, morseHeightAngle_vertical_ge_half ha ht, hδsmall]
    let k := Ξ * B.2 / B.1
    have hSlope (σ : ℝ) (hσ : σ ∈ bad) : |a - σ * k| < 6 * δ ∧ σ * k < -(1 / 4 : ℝ) := by
      have hb : Statements.radialAngleSine (1, a) (morseHeightOuterState Ξ σ B) < δ := hσ.2
      rw [morseHeightAngle_slope_formula a Ξ σ B hB₁,
        show σ * Ξ * B.2 / B.1 = σ * k by dsimp [k]; ring] at hb
      exact morseHeight_small_angle_slope ha hδ hδsmall hb
    have hkbound : (1 : ℝ) / 8 ≤ |k| := by
      have hb := (hSlope σ₀ hσ₀).2
      have hh : (1 : ℝ) / 4 ≤ |σ₀ * k| := by linarith only [hb, neg_le_abs (σ₀ * k)]
      rw [abs_mul, abs_of_nonneg (zero_le_one.trans hσ₀in.1)] at hh
      linarith only [hh, mul_le_mul_of_nonneg_right hσ₀in.2 (abs_nonneg k)]
    have hkAbs : 0 < |k| := (by norm_num : (0 : ℝ) < 1 / 8).trans_le hkbound
    have hk : k ≠ 0 := abs_pos.mp hkAbs
    let r := (6 * δ) / |k|
    have hr : 0 < r := div_pos (by positivity) hkAbs
    refine ⟨a / k - r, a / k + r, by linarith only [hr], ?_, ?_⟩
    · have hh : (12 * δ) / |k| ≤ 96 * δ := by
        apply (div_le_iff₀ hkAbs).2
        nlinarith only [mul_le_mul_of_nonneg_left hkbound hδ.le]
      dsimp [r]
      calc
        _ = (12 * δ) / |k| := by ring
        _ ≤ _ := hh
    · intro σ hσ
      have hs := (hSlope σ hσ).1
      have he : σ - a / k = (σ * k - a) / k := by
        rw [sub_div, mul_div_cancel_right₀ σ hk]
      have h : |σ - a / k| < r := by
        rw [he, abs_div, abs_sub_comm (σ * k) a]
        exact div_lt_div_of_pos_right hs hkAbs
      obtain ⟨hl, hu⟩ := abs_le.mp h.le
      exact ⟨by linarith only [hl], by linarith only [hu]⟩
  · refine ⟨0, 0, le_rfl, by linarith only [hδ], ?_⟩
    intro σ hσ
    exact (hnonempty ⟨σ, hσ⟩).elim

private def morseAngleLength (u : ℝ × ℝ) : ℝ := sqrt (u.1 ^ 2 + u.2 ^ 2)

private def morseAngleDet (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

private theorem morseAngleLength_nonneg (u : ℝ × ℝ) : 0 ≤ morseAngleLength u := sqrt_nonneg _

private theorem morseAngleLength_sq (u : ℝ × ℝ) : morseAngleLength u ^ 2 = u.1 ^ 2 + u.2 ^ 2 :=
  sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem morseAngleLength_pos {u : ℝ × ℝ} (h : u ≠ (0, 0)) : 0 < morseAngleLength u := by
  apply sqrt_pos.mpr
  by_cases h₁ : u.1 = 0
  · have h₂ : u.2 ≠ 0 := fun hz => h (Prod.ext h₁ hz)
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h₂)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h₁) (sq_nonneg _)

private theorem morseAngleDet_abs_le (u v : ℝ × ℝ) :
    |morseAngleDet u v| ≤ morseAngleLength u * morseAngleLength v := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (morseAngleLength_nonneg _) (morseAngleLength_nonneg _))).1
  simp only [sq_abs, mul_pow, morseAngleLength_sq, morseAngleDet]
  nlinarith only [sq_nonneg (u.1 * v.1 + u.2 * v.2)]

private theorem morseAngleDot_le (u v : ℝ × ℝ) :
    u.1 * v.1 + u.2 * v.2 ≤ morseAngleLength u * morseAngleLength v := by
  apply (le_abs_self _).trans
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (morseAngleLength_nonneg _) (morseAngleLength_nonneg _))).1
  simp only [sq_abs, mul_pow, morseAngleLength_sq]
  nlinarith only [sq_nonneg (u.1 * v.2 - u.2 * v.1)]

private theorem morseAngleLength_add_le (u v : ℝ × ℝ) :
    morseAngleLength (u + v) ≤ morseAngleLength u + morseAngleLength v := by
  apply (sq_le_sq₀ (morseAngleLength_nonneg _) (add_nonneg (morseAngleLength_nonneg _)
    (morseAngleLength_nonneg _))).1
  rw [morseAngleLength_sq]
  change (u.1 + v.1) ^ 2 + (u.2 + v.2) ^ 2 ≤ (morseAngleLength u + morseAngleLength v) ^ 2
  nlinarith only [morseAngleLength_sq u, morseAngleLength_sq v, morseAngleDot_le u v]

private theorem morseAngleLength_sub_comm (u v : ℝ × ℝ) :
    morseAngleLength (u - v) = morseAngleLength (v - u) := by
  unfold morseAngleLength
  congr 1
  change (u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2 = (v.1 - u.1) ^ 2 + (v.2 - u.2) ^ 2
  ring

private theorem morseAngleLength_le_add_sub (u v : ℝ × ℝ) :
    morseAngleLength v ≤ morseAngleLength u + morseAngleLength (u - v) := by
  calc
    _ = morseAngleLength (u + (v - u)) := by rw [add_comm u, sub_add_cancel]
    _ ≤ morseAngleLength u + morseAngleLength (v - u) := morseAngleLength_add_le _ _
    _ = _ := by rw [morseAngleLength_sub_comm v u]

private theorem morseAngleSine_eq (u v : ℝ × ℝ) : Statements.radialAngleSine u v =
    |morseAngleDet u v| / (morseAngleLength u * morseAngleLength v) := rfl

/-- The angle change is bounded by the actual Euclidean coordinate error.
The bound is independent of the length of the outgoing vector. -/
theorem morseHeightAngleSine_le_add_perturbation {u v B : ℝ × ℝ}
    (hu : u ≠ (0, 0)) (hv : v ≠ (0, 0)) (hB : B ≠ (0, 0)) :
    Statements.radialAngleSine u B ≤ Statements.radialAngleSine v B +
      2 * sqrt ((u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2) / sqrt (u.1 ^ 2 + u.2 ^ 2) := by
  let s := Statements.radialAngleSine v B
  let L := morseAngleLength
  let d := L (u - v)
  have hu₀ : 0 < L u := morseAngleLength_pos hu
  have hv₀ : 0 < L v := morseAngleLength_pos hv
  have hB₀ : 0 < L B := morseAngleLength_pos hB
  have hd : 0 ≤ d := morseAngleLength_nonneg _
  have hs : s = |morseAngleDet v B| / (L v * L B) := morseAngleSine_eq v B
  have hs₀ : 0 ≤ s := by
    rw [hs]
    exact div_nonneg (abs_nonneg _) (mul_nonneg hv₀.le hB₀.le)
  have hs₁ : s ≤ 1 := by
    rw [hs, div_le_iff₀ (mul_pos hv₀ hB₀), one_mul]
    exact morseAngleDet_abs_le _ _
  have hdet : |morseAngleDet u B| ≤ |morseAngleDet v B| + d * L B := by
    calc
      _ = |morseAngleDet v B + morseAngleDet (u - v) B| := by
        unfold morseAngleDet
        congr 1
        change u.1 * B.2 - u.2 * B.1 = v.1 * B.2 - v.2 * B.1 +
          ((u.1 - v.1) * B.2 - (u.2 - v.2) * B.1)
        ring
      _ ≤ |morseAngleDet v B| + |morseAngleDet (u - v) B| := abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl (morseAngleDet_abs_le _ _)
  have hsv : |morseAngleDet v B| = s * (L v * L B) := by
    rw [hs, div_mul_cancel₀ _ (mul_ne_zero hv₀.ne' hB₀.ne')]
  have hvL : L v ≤ L u + d := morseAngleLength_le_add_sub u v
  change |morseAngleDet u B| / (L u * L B) ≤ s + 2 * d / L u
  apply (div_le_iff₀ (mul_pos hu₀ hB₀)).2
  calc
    _ ≤ |morseAngleDet v B| + d * L B := hdet
    _ = s * (L v * L B) + d * L B := by rw [hsv]
    _ ≤ s * ((L u + d) * L B) + d * L B := add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvL hB₀.le) hs₀) le_rfl
    _ ≤ s * (L u * L B) + 2 * d * L B := by
      have h := mul_nonneg (sub_nonneg.mpr hs₁) (mul_nonneg hd hB₀.le)
      nlinarith only [h]
    _ = _ := by
      have hcancel : (2 * d / L u) * (L u * L B) = 2 * d * L B := by
        rw [← mul_assoc, div_mul_cancel₀ _ hu₀.ne']
      rw [add_mul, hcancel]

private theorem morseHeightOuterState_ne_zero {Ξ σ : ℝ} {B : ℝ × ℝ}
    (hΞ : 0 < Ξ) (hσ : σ ∈ Icc (1 : ℝ) 2) (hB : B ≠ (0, 0)) :
    morseHeightOuterState Ξ σ B ≠ (0, 0) := by
  intro h
  have h₁ : B.1 = 0 := congrArg Prod.fst h
  have h₂ : σ * Ξ * B.2 = 0 := congrArg Prod.snd h
  exact hB (Prod.ext h₁ ((mul_eq_zero.mp h₂).resolve_left
    (mul_ne_zero (zero_lt_one.trans_le hσ.1).ne' hΞ.ne')))

private theorem morseHeight_coordinate_error_le {a η : ℝ} {v : ℝ × ℝ} (hη : 0 ≤ η)
    (h₁ : |v.1 - 1| ≤ η) (h₂ : |v.2 - a| ≤ η) :
    sqrt ((1 - v.1) ^ 2 + (a - v.2) ^ 2) ≤ 2 * η := by
  have h₁sq : (v.1 - 1) ^ 2 ≤ η ^ 2 := by
    rw [← sq_abs (v.1 - 1)]
    exact (sq_le_sq₀ (abs_nonneg _) hη).2 h₁
  have h₂sq : (v.2 - a) ^ 2 ≤ η ^ 2 := by
    rw [← sq_abs (v.2 - a)]
    exact (sq_le_sq₀ (abs_nonneg _) hη).2 h₂
  have hs : (1 - v.1) ^ 2 + (a - v.2) ^ 2 ≤ (2 * η) ^ 2 := by
    nlinarith only [h₁sq, h₂sq, sq_nonneg η]
  exact (sqrt_le_sqrt hs).trans_eq (sqrt_sq (by positivity))

/-- A coordinate error at most `η ≤ δ / 4` sends every genuinely bad angle
into the ideal exclusion at tolerance `2 δ`. -/
theorem morseHeightAngle_bad_subset_ideal {a Ξ δ η : ℝ} {Y : ℝ → ℝ × ℝ} {B : ℝ × ℝ}
    (hΞ : 0 < Ξ) (hB : B ≠ (0, 0)) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 48)
    (hη : 0 ≤ η) (hηsmall : η ≤ δ / 4)
    (hY : ∀ σ ∈ Icc (1 : ℝ) 2, |(Y σ).1 - 1| ≤ η ∧ |(Y σ).2 - a| ≤ η) :
    morseHeightAngleBadSet Ξ δ Y B ⊆ morseHeightAngleBadSet Ξ (2 * δ) (fun _ => (1, a)) B := by
  intro σ hσ
  have hσin : σ ∈ Icc (1 : ℝ) 2 := hσ.1
  have hnear := hY σ hσin
  have hu : ((1, a) : ℝ × ℝ) ≠ (0, 0) := fun h => one_ne_zero (congrArg Prod.fst h)
  have hv : Y σ ≠ (0, 0) := by
    intro h
    have h₁ : (Y σ).1 = 0 := congrArg Prod.fst h
    have hn := (abs_le.mp hnear.1).1
    rw [h₁, zero_sub] at hn
    linarith only [hn, hηsmall, hδsmall]
  have hDiff := morseHeightAngleSine_le_add_perturbation hu hv (morseHeightOuterState_ne_zero hΞ hσin hB)
  have hcoord := morseHeight_coordinate_error_le hη hnear.1 hnear.2
  have hs : 1 ≤ sqrt (1 + a ^ 2) := calc
    _ = sqrt 1 := sqrt_one.symm
    _ ≤ _ := sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg a))
  have herror : 2 * sqrt ((1 - (Y σ).1) ^ 2 + (a - (Y σ).2) ^ 2) / sqrt (1 + a ^ 2) ≤ δ := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hs)).2
    linarith only [hcoord, hηsmall, mul_le_mul_of_nonneg_left hs hδ.le]
  change Statements.radialAngleSine (1, a) (morseHeightOuterState Ξ σ B) ≤
    Statements.radialAngleSine (Y σ) (morseHeightOuterState Ξ σ B) +
      2 * sqrt ((1 - (Y σ).1) ^ 2 + (a - (Y σ).2) ^ 2) / sqrt (1 ^ 2 + a ^ 2) at hDiff
  rw [one_pow] at hDiff
  exact ⟨hσin, by linarith only [hDiff, herror, hσ.2]⟩

theorem morseHeightAngle_true_bad_interval {a Ξ δ η : ℝ} {Y : ℝ → ℝ × ℝ} {B : ℝ × ℝ}
    (ha : a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2)) (hΞ : 0 < Ξ) (hB : B ≠ (0, 0))
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 48) (hη : 0 ≤ η) (hηsmall : η ≤ δ / 4)
    (hY : ∀ σ ∈ Icc (1 : ℝ) 2, |(Y σ).1 - 1| ≤ η ∧ |(Y σ).2 - a| ≤ η) :
    ∃ l u : ℝ, l ≤ u ∧ u - l ≤ 192 * δ ∧ morseHeightAngleBadSet Ξ δ Y B ⊆ Icc l u := by
  obtain ⟨l, u, hlu, hlen, hin⟩ := morseHeightAngle_ideal_bad_interval ha hΞ hB
    (show 0 < 2 * δ by positivity) (show 2 * δ ≤ 1 / 24 by linarith only [hδsmall])
  exact ⟨l, u, hlu, by linarith only [hlen],
    (morseHeightAngle_bad_subset_ideal hΞ hB hδ hδsmall hη hηsmall hY).trans hin⟩

/-- The actual one-coordinate bad heights have Lebesgue measure at most
`192 δ`, uniformly in the fixed outgoing line and the height contrast. -/
theorem morseHeightAngle_true_bad_measure_le {a Ξ δ η : ℝ} {Y : ℝ → ℝ × ℝ} {B : ℝ × ℝ}
    (ha : a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2)) (hΞ : 0 < Ξ) (hB : B ≠ (0, 0))
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 48) (hη : 0 ≤ η) (hηsmall : η ≤ δ / 4)
    (hY : ∀ σ ∈ Icc (1 : ℝ) 2, |(Y σ).1 - 1| ≤ η ∧ |(Y σ).2 - a| ≤ η) :
    volume (morseHeightAngleBadSet Ξ δ Y B) ≤ ENNReal.ofReal (192 * δ) := by
  obtain ⟨l, u, _, hlen, hin⟩ := morseHeightAngle_true_bad_interval ha hΞ hB hδ hδsmall hη hηsmall hY
  refine (measure_mono hin).trans ?_
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_le_ofReal hlen

end ContinuousFlexibility.Radial
