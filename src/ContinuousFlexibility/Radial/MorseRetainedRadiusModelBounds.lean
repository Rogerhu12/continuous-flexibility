module

public import ContinuousFlexibility.Radial.MorseCellMassResistanceBounds

/-!
# Model estimates after normalizing a retained radius

The prescribed speed is relative to the radius at the right turning point.
Dividing by that positive radius puts any realized cell into the normalized
initial-value problem used by the finite-cell estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff

theorem morseRetainedRadius_model_bounds {A B s : ℝ} {R : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA₀ : A ≤ 1 / 1000)
    (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9)
    (hs : 0 < s) (hR : ContDiff ℝ ∞ R)
    (hroot : R (morseRightTurn A B) = s)
    (hspeed : deriv R (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 * s)
    (hEq : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      deriv (deriv R) x = -morseRho A B x * R x)
    (hRp : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)), 0 < R x)
    (hVp : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)), 0 < deriv R x) :
    let a := morseCellLeftCut
    let b := morseRightTurn A B
    let e := morseRightCapEnd A B (1 / 100)
    let mass := ∫ x in a..b, (deriv R x) ^ 2 * R x ^ 6
    let resistance := ∫ x in a..b, (R x ^ 8)⁻¹
    let capMass := ∫ x in b..e, (deriv R x) ^ 2 * R x ^ 6
    let capResistance := ∫ x in b..e, (R x ^ 8)⁻¹
    (s ^ 8 * (morseShortLeftCapLength / 1024 * A ^ 2) ≤ mass ∧
      mass ≤ s ^ 8 * (2688 * A ^ 2)) ∧
    resistance ≤ (s ^ 8)⁻¹ * (512 * log (A / B)) ∧
    capMass ≤ s ^ 8 * A ^ 6 ∧
    ((s ^ 8)⁻¹ * ((A ^ 4)⁻¹ / 25600) ≤ capResistance ∧
      capResistance ≤ (s ^ 8)⁻¹ * (3 * (A ^ 4)⁻¹)) ∧
    deriv R a ≤ 7 * s * A ∧
    s / 100 * A ^ 5 ≤ deriv R e := by
  let a := morseCellLeftCut
  let b := morseRightTurn A B
  let e := morseRightCapEnd A B (1 / 100)
  let r : ℝ → ℝ := fun x => R x / s
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hab : a ≤ b := (morseCellLeftCut_lt_rightTurn hB hAB).le
  have hbe : b ≤ e :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hae : a ≤ e := hab.trans hbe
  have hI : Icc a b ⊆ Icc a e := fun _ hx => ⟨hx.1, hx.2.trans hbe⟩
  have hC : Icc b e ⊆ Icc a e := fun _ hx => ⟨hab.trans hx.1, hx.2⟩
  have hr : ContDiff ℝ ∞ r := hR.div_const s
  have hd (x : ℝ) : deriv r x = deriv R x / s :=
    (((hR.differentiable (by simp) x).hasDerivAt).div_const s).deriv
  have hdd (x : ℝ) : deriv (deriv r) x = deriv (deriv R) x / s := by
    have he : deriv r = fun y => deriv R y / s := funext hd
    rw [he]
    exact ((((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp) x).hasDerivAt).div_const s).deriv
  have hrb : r b = 1 := by dsimp only [r]; rw [hroot, div_self hs.ne']
  have hvb : deriv r b = (1 / 100 : ℝ) * A ^ 5 := by
    rw [hd, hspeed, mul_div_cancel_right₀ _ hs.ne']
  have hEq' (x : ℝ) (hx : x ∈ Icc a e) :
      deriv (deriv r) x = -morseRho A B x * r x := by
    rw [hdd, hEq x hx]
    dsimp only [r]
    ring
  obtain ⟨hLeft, _, hvLeft, _⟩ := morseLeftCap_radius_bounds hB hAB hA₀ hBAlo hBAhi
    hr hrb hvb (fun x hx => hEq' x (hI hx))
  have hRight := morseRightCap_radius_bounds hB hAB (hA₀.trans (by norm_num)) hBAhi
    (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (1 / 100 : ℝ) ≤ 1 / 4)
    (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (1 / 100 : ℝ) ≤ 1 / 4)
    hr hrb hvb (fun x hx => hEq' x (hC hx))
  have hBounds (x : ℝ) (hx : x ∈ Icc a e) :
      1 / 2 ≤ r x ∧ r x ≤ 2 ∧
      (1 / 100 : ℝ) * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ 7 * A := by
    by_cases hxb : x ≤ b
    · obtain ⟨hclose, _, hu, hlv, huv⟩ := hLeft x ⟨hx.1, hxb⟩
      exact ⟨by linarith only [(abs_le.mp hclose).1, hA₀], hu, hlv, huv⟩
    · obtain ⟨hclose, _, hu, hlv, huv⟩ := hRight x ⟨le_of_not_ge hxb, hx.2⟩
      have hA5 : A ^ 5 ≤ A := calc
        _ = A * A ^ 4 := by ring
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ hA.le (hA₀.trans (by norm_num))) hA.le
        _ = A := mul_one _
      refine ⟨?_, hu, hlv, ?_⟩
      · norm_num at hclose
        linarith only [(abs_le.mp hclose).1, hA₀]
      · norm_num at huv
        linarith only [huv, hA5, hA]
  have hrp (x : ℝ) (hx : x ∈ Icc a e) : 0 < r x :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hBounds x hx).1
  have hvp (x : ℝ) (hx : x ∈ Icc a e) : 0 < deriv r x :=
    (by positivity : (0 : ℝ) < (1 / 100 : ℝ) * A ^ 5).trans_le (hBounds x hx).2.2.1
  have hmono := morseCell_strictMonoOn hR hVp
  let w := morseCellRadialProfile R a e 1
  have hwR (x : ℝ) (hx : x ∈ Icc a e) : w (R x) = deriv R x := by
    simpa only [w, one_mul] using morseCellRadialProfile_apply 1 hmono hx
  have hmul (x : ℝ) : s * r x = R x := by dsimp only [r]; field_simp [hs.ne']
  have hmulD (x : ℝ) : s * deriv r x = deriv R x := by rw [hd]; field_simp [hs.ne']
  have hw (x : ℝ) (hx : x ∈ Icc a e) : w (s * r x) = 1 * s * deriv r x := by
    rw [hmul, hwR x hx, one_mul, hmulD]
  have hCap (x : ℝ) (hx : x ∈ Icc b e) : deriv r x ≤ (3 / 100 : ℝ) * A ^ 5 := by
    simpa only [show (1 / 100 : ℝ) + 2 * (1 / 100) = 3 / 100 by norm_num]
      using (hRight x hx).2.2.2.2
  have hmodel := morseRetainedCell_physical_mass_resistance_bounds hB hAB
    (by norm_num : (0 : ℝ) < 1) hs hr hrb (hLeft a (left_mem_Icc.mpr hab)).1
    (fun x hx => hEq' x (hI hx))
    (fun x hx => ⟨(hBounds x hx).1, (hBounds x hx).2.1⟩)
    (fun x hx => (hBounds x hx).2.2) hvLeft hCap hw
  have hw1 (x : ℝ) (hx : x ∈ Icc a e) : w (1 * R x) = 1 * 1 * deriv R x := by
    simpa only [one_mul] using hwR x hx
  obtain ⟨hMI, hRI⟩ := morseCell_physical_mass_resistance_change hae hab hI
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) hR hRp hVp hw1
  obtain ⟨hMC, hRC⟩ := morseCell_physical_mass_resistance_change hae hbe hC
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) hR hRp hVp hw1
  dsimp only at hmodel
  simp only [hmul, one_mul, one_pow, inv_one] at hmodel hMI hRI hMC hRC
  rw [hMI, hRI, hMC, hRC] at hmodel
  refine ⟨hmodel.1, hmodel.2.1.2, hmodel.2.2.1.2, hmodel.2.2.2, ?_, ?_⟩
  · rw [← hmulD]
    calc
      _ ≤ s * (7 * A) := mul_le_mul_of_nonneg_left (hBounds a (left_mem_Icc.mpr hae)).2.2.2 hs.le
      _ = _ := by ring
  · rw [← hmulD]
    calc
      s / 100 * A ^ 5 = s * ((1 / 100 : ℝ) * A ^ 5) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hBounds e (right_mem_Icc.mpr hae)).2.2.1 hs.le

end ContinuousFlexibility.Radial
