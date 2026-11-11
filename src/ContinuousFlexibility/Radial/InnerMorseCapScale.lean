import ContinuousFlexibility.Radial.MorseCellMassTravel

/-!
# The physical speed-to-mass ratio on both Morse caps

The estimates use the actual radius with its prescribed relative speed
at the right turning point. Normalizing that radius, applying the
retained-cell ODE bounds, and undoing the normalization proves the
uniform ratio needed in the physical leading Poisson estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff

/-- The positive portions used for the short and long buffers. -/
def innerMorseCapInterval (A B : ℝ) (right : Bool) : Set ℝ :=
  if right then Icc (morseRightTurn A B + log 4) (morseRightCapEnd A B (1 / 100))
  else Icc morseCellLeftCut morseShortLeftCapCut

/-- A fixed mass lower bound from the actual Morse potential on the cap. -/
def innerMorseCapMass (A B j : ℝ) (right : Bool) : ℝ :=
  j * sqrt (if right then B / 2 else A / 4)

theorem innerMorseCapMass_spec {A B j : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hj : 0 < j) (right : Bool) {x : ℝ} (hx : x ∈ innerMorseCapInterval A B right) :
    0 < innerMorseCapMass A B j right ∧
      innerMorseCapMass A B j right ^ 2 ≤ j ^ 2 * (-morseRho A B x) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hc : 0 < (if right then B / 2 else A / 4) := by
    cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> positivity
  have hρ : (if right then B / 2 else A / 4) ≤ -morseRho A B x := by
    cases right with
    | false =>
      simp only [innerMorseCapInterval, Bool.false_eq_true, ite_false] at hx ⊢
      exact morseShortLeftCap_negRho_lower hB hAB hx.2
    | true =>
      simp only [innerMorseCapInterval, ite_true] at hx ⊢
      exact morseRho_right_cap_lower hB hAB hx.1
  refine ⟨mul_pos hj (sqrt_pos.mpr hc), ?_⟩
  rw [innerMorseCapMass, mul_pow, sq_sqrt hc.le]
  exact mul_le_mul_of_nonneg_left hρ (sq_nonneg j)

/-- The velocity-to-radius ratio is invariant under the physical radius
scale. Its long-cap bound retains the crucial fifth power of A. -/
theorem innerMorse_upsilon_bounds {A B s : ℝ} {R : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA₀ : A ≤ 1 / 1000)
    (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9)
    (hs : 0 < s) (hR : ContDiff ℝ ∞ R)
    (hroot : R (morseRightTurn A B) = s)
    (hspeed : deriv R (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 * s)
    (hEq : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      deriv (deriv R) x = -morseRho A B x * R x)
    (right : Bool) {x : ℝ}
    (hx : x ∈ if right then Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100))
      else Icc morseCellLeftCut (morseRightTurn A B)) :
    |deriv R x / R x| ≤ if right then (3 / 50 : ℝ) * A ^ 5 else 14 * A := by
  let r : ℝ → ℝ := fun y => R y / s
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hab := (morseCellLeftCut_lt_rightTurn hB hAB).le
  have hbe : morseRightTurn A B ≤ morseRightCapEnd A B (1 / 100) :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num)).le
  have hr : ContDiff ℝ ∞ r := hR.div_const s
  have hd (y : ℝ) : deriv r y = deriv R y / s :=
    ((hR.differentiable (by simp) y).hasDerivAt.div_const s).deriv
  have hdd (y : ℝ) : deriv (deriv r) y = deriv (deriv R) y / s := by
    rw [show deriv r = (fun z => deriv R z / s) from funext hd]
    exact (((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp) y).hasDerivAt.div_const s).deriv
  have hrb : r (morseRightTurn A B) = 1 := by
    dsimp only [r]
    rw [hroot, div_self hs.ne']
  have hvb : deriv r (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 := by
    rw [hd, hspeed, mul_div_cancel_right₀ _ hs.ne']
  have hEq' (y : ℝ) (hy : y ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100))) :
      deriv (deriv r) y = -morseRho A B y * r y := by
    rw [hdd, hEq y hy]
    dsimp only [r]
    ring
  have hLeft := (morseLeftCap_radius_bounds hB hAB hA₀ hBAlo hBAhi hr hrb hvb
    (fun y hy => hEq' y ⟨hy.1, hy.2.trans hbe⟩)).1
  have hRight := morseRightCap_radius_bounds hB hAB (hA₀.trans (by norm_num)) hBAhi
    (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (1 / 100 : ℝ) ≤ 1 / 4)
    (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (1 / 100 : ℝ) ≤ 1 / 4)
    hr hrb hvb (fun y hy => hEq' y ⟨hab.trans hy.1, hy.2⟩)
  have hratio (y : ℝ) (hry : 0 < r y) : deriv R y / R y = deriv r y / r y := by
    have he : s * r y = R y := by dsimp only [r]; field_simp [hs.ne']
    have hRy : 0 < R y := by rw [← he]; exact mul_pos hs hry
    rw [hd]
    dsimp only [r]
    field_simp [hs.ne', hRy.ne'] <;> ring
  have hinit : 0 ≤ (1 / 100 : ℝ) * A ^ 5 := by positivity
  cases right with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hx ⊢
    obtain ⟨hc, hrp, _, hvl, hvu⟩ := hLeft x hx
    have hhalf : (1 / 2 : ℝ) ≤ r x := by linarith only [(abs_le.mp hc).1, hA₀]
    rw [hratio x hrp, abs_of_nonneg (div_nonneg (hinit.trans hvl) hrp.le)]
    apply (div_le_iff₀ hrp).mpr
    have h := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 14 * A)
    nlinarith only [h, hvu]
  | true =>
    simp only [ite_true] at hx ⊢
    obtain ⟨hc, hrp, _, hvl, hvu⟩ := hRight x hx
    norm_num only at hc hvu
    have hhalf : (1 / 2 : ℝ) ≤ r x := by linarith only [(abs_le.mp hc).1, hA₀]
    rw [hratio x hrp, abs_of_nonneg (div_nonneg (hinit.trans hvl) hrp.le)]
    apply (div_le_iff₀ hrp).mpr
    have h := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ (3 / 50 : ℝ) * A ^ 5)
    nlinarith only [h, hvu]

/-- The same fixed constant works for both caps, every positive frequency,
and every physical radius scale. In particular there is no residual
negative power of A on the long cap. -/
theorem innerMorse_cap_upsilon_over_mass {A B s j : ℝ} {R : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA₀ : A ≤ 1 / 1000)
    (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9)
    (hs : 0 < s) (hR : ContDiff ℝ ∞ R)
    (hroot : R (morseRightTurn A B) = s)
    (hspeed : deriv R (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 * s)
    (hEq : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      deriv (deriv R) x = -morseRho A B x * R x)
    (hj : 0 < j) (right : Bool) {x : ℝ} (hx : x ∈ innerMorseCapInterval A B right) :
    |deriv R x / R x| / innerMorseCapMass A B j right ≤ 30000 / j := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hA₁ : A ≤ 1 := hA₀.trans (by norm_num)
  have hc : 0 < (if right then B / 2 else A / 4) := by
    cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> positivity
  have hspeedBound : |deriv R x / R x| ≤ 30000 * sqrt (if right then B / 2 else A / 4) := by
    cases right with
    | false =>
      simp only [innerMorseCapInterval, Bool.false_eq_true, ite_false] at hx ⊢
      have hx' : x ∈ Icc morseCellLeftCut (morseRightTurn A B) :=
        ⟨hx.1, hx.2.trans
          ((morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)).le⟩
      have hv := innerMorse_upsilon_bounds hB hAB hA₀ hBAlo hBAhi hs hR hroot hspeed hEq false hx'
      simp only [Bool.false_eq_true, ite_false] at hv
      apply hv.trans
      apply (sq_le_sq₀ (by positivity : 0 ≤ 14 * A) (by positivity)).mp
      rw [mul_pow, mul_pow, sq_sqrt (div_nonneg hA.le (by norm_num))]
      have hA₂ : A ^ 2 ≤ A := by
        nlinarith only [mul_nonneg hA.le (sub_nonneg.mpr hA₁)]
      nlinarith only [hA₂, hA.le]
    | true =>
      simp only [innerMorseCapInterval, ite_true] at hx ⊢
      have hx' : x ∈ Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)) :=
        ⟨by linarith only [hx.1, log_pos (by norm_num : (1 : ℝ) < 4)], hx.2⟩
      have hv := innerMorse_upsilon_bounds hB hAB hA₀ hBAlo hBAhi hs hR hroot hspeed hEq true hx'
      simp only [ite_true] at hv
      have hsq : (A ^ 5) ^ 2 ≤ (9 : ℝ) ^ 9 * B := by
        calc
          (A ^ 5) ^ 2 = A ^ 9 * A := by ring
          _ ≤ A ^ 9 * 1 := mul_le_mul_of_nonneg_left hA₁ (pow_nonneg hA.le 9)
          _ = A ^ 9 := mul_one _
          _ ≤ _ := by
            have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < (9 : ℝ) ^ 9)).mp hBAlo
            simpa only [mul_comm B] using h
      have hsmall : (3 / 50 : ℝ) * A ^ 5 ≤ A ^ 5 := by
        nlinarith only [pow_nonneg hA.le 5]
      apply (hv.trans hsmall).trans
      apply (sq_le_sq₀ (pow_nonneg hA.le 5) (by positivity)).mp
      rw [mul_pow, sq_sqrt (div_nonneg hB.le (by norm_num))]
      nlinarith only [hsq, hB.le]
  calc
    _ ≤ (30000 * sqrt (if right then B / 2 else A / 4)) /
        innerMorseCapMass A B j right :=
      div_le_div_of_nonneg_right hspeedBound (innerMorseCapMass_spec hB hAB hj right hx).1.le
    _ = 30000 / j := by
      rw [innerMorseCapMass]
      field_simp [hj.ne', (sqrt_pos.mpr hc).ne']

end ContinuousFlexibility.Radial
