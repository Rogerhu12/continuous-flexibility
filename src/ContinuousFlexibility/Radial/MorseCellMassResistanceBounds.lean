module

public import ContinuousFlexibility.Radial.MorseCellMassTravel
public import ContinuousFlexibility.Radial.MorseJoinHeightContrast
public import ContinuousFlexibility.Radial.MorseAdjacentJoin

/-!
# Physical mass and resistance of one Morse cell

The mass interval runs from the short left cap to the right turning
point. The resistance interval continues along the long cap and its
following connector in increasing physical radius.
-/

@[expose] public section

noncomputable section
namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The two densities from §5 on a dilated model subinterval, computed
with the same physical profile as on the entire retained cell. -/
theorem morseCell_physical_mass_resistance_change {r w : ℝ → ℝ} {a b c d lam s : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b)
    (hlam : 0 < lam) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hrpos : ∀ x ∈ Icc a b, 0 < r x) (hv : ∀ x ∈ Icc a b, 0 < deriv r x)
    (hw : ∀ x ∈ Icc a b, w (s * r x) = lam * s * deriv r x) :
    (∫ z in s * r c..s * r d, w z * z ^ 6) =
        (lam * s ^ 8) * (∫ x in c..d, (deriv r x) ^ 2 * r x ^ 6) ∧
      (∫ z in s * r c..s * r d, (w z * z ^ 8)⁻¹) =
        (lam * s ^ 8)⁻¹ * (∫ x in c..d, (r x ^ 8)⁻¹) := by
  let R : ℝ → ℝ := fun x => s * r x
  let W := morseCellRadialProfile R a b lam
  have hRs : ContDiff ℝ ∞ R := contDiff_const.mul hr
  have hD (x : ℝ) : deriv R x = s * deriv r x :=
    (((hr.differentiable (by simp) x).hasDerivAt).const_mul s).deriv
  have hRpos (x : ℝ) (hx : x ∈ Icc a b) : 0 < R x := mul_pos hs (hrpos x hx)
  have hRv (x : ℝ) (hx : x ∈ Icc a b) : 0 < deriv R x := by
    rw [hD]
    exact mul_pos hs (hv x hx)
  have hmono := morseCell_strictMonoOn hRs hRv
  have hcdR : R c ≤ R d :=
    hmono.monotoneOn (hsub (left_mem_Icc.mpr hcd)) (hsub (right_mem_Icc.mpr hcd)) hcd
  have hwW (z : ℝ) (hz : z ∈ uIcc (R c) (R d)) : w z = W z := by
    rw [uIcc_of_le hcdR] at hz
    have hc := hsub (left_mem_Icc.mpr hcd)
    have hd := hsub (right_mem_Icc.mpr hcd)
    have hz' : z ∈ Icc (R a) (R b) :=
      ⟨(hmono.monotoneOn (left_mem_Icc.mpr hab) hc hc.1).trans hz.1,
        hz.2.trans (hmono.monotoneOn hd (right_mem_Icc.mpr hab) hd.2)⟩
    obtain ⟨hx, heq⟩ := morseCellModelCoordinate_right hab hRs hmono hz'
    rw [← heq]
    dsimp only [W]
    rw [morseCellRadialProfile_apply lam hmono hx, hD]
    change w (s * r (morseCellModelCoordinate R a b z)) =
      lam * (s * deriv r (morseCellModelCoordinate R a b z))
    rw [hw _ hx, mul_assoc]
  obtain ⟨_, _, hMe, hRe⟩ :=
    morseCell_chain_mass_resistance_change hcd hsub hlam hRs hRpos hRv
  have hm (x : ℝ) : (deriv R x) ^ 2 * R x ^ 6 =
      s ^ 8 * ((deriv r x) ^ 2 * r x ^ 6) := by
    rw [hD]
    dsimp only [R]
    ring
  have hri (x : ℝ) : (R x ^ 8)⁻¹ = (s ^ 8)⁻¹ * (r x ^ 8)⁻¹ := by
    dsimp only [R]
    rw [mul_pow, mul_inv_rev, mul_comm]
  refine ⟨?_, ?_⟩
  · calc
      (∫ z in R c..R d, w z * z ^ 6) = ∫ z in R c..R d, W z * z ^ 6 := by
        apply intervalIntegral.integral_congr
        intro z hz
        change w z * z ^ 6 = W z * z ^ 6
        rw [hwW z hz]
      _ = lam * (∫ x in c..d, (deriv R x) ^ 2 * R x ^ 6) := hMe
      _ = _ := by simp only [hm, intervalIntegral.integral_const_mul, mul_assoc]
  · calc
      (∫ z in R c..R d, (w z * z ^ 8)⁻¹) = ∫ z in R c..R d, (W z * z ^ 8)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro z hz
        change (w z * z ^ 8)⁻¹ = (W z * z ^ 8)⁻¹
        rw [hwW z hz]
      _ = lam⁻¹ * (∫ x in c..d, (R x ^ 8)⁻¹) := hRe
      _ = _ := by rw [mul_inv_rev]; simp only [hri, intervalIntegral.integral_const_mul]; ring

private theorem morseCell_weighted_model_integrals {r : ℝ → ℝ} {c d : ℝ}
    (hcd : c ≤ d) (hr : ContDiff ℝ ∞ r) (hR : ∀ x ∈ Icc c d, 1 / 2 ≤ r x ∧ r x ≤ 2) :
    (1 / 64 : ℝ) * (∫ x in c..d, (deriv r x) ^ 2) ≤
        (∫ x in c..d, (deriv r x) ^ 2 * r x ^ 6) ∧
      (∫ x in c..d, (deriv r x) ^ 2 * r x ^ 6) ≤
        64 * (∫ x in c..d, (deriv r x) ^ 2) ∧
      (d - c) / 256 ≤ (∫ x in c..d, (r x ^ 8)⁻¹) ∧
      (∫ x in c..d, (r x ^ 8)⁻¹) ≤ 256 * (d - c) := by
  have hV := ((contDiff_infty_iff_deriv.mp hr).2.continuous.pow 2)
  have hM := hV.mul (hr.continuous.pow 6)
  have hp (x : ℝ) (hx : x ∈ Icc c d) : 0 < r x :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hR x hx).1
  have hRi : IntervalIntegrable (fun x => (r x ^ 8)⁻¹) volume c d :=
    ((hr.continuous.continuousOn.pow 8).inv₀
      (fun x hx => pow_ne_zero 8 (hp x hx).ne')).intervalIntegrable_of_Icc hcd
  have hLo (x : ℝ) (hx : x ∈ Icc c d) :
      (1 / 64 : ℝ) * (deriv r x) ^ 2 ≤ (deriv r x) ^ 2 * r x ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (hR x hx).1 6
    have h' : (1 / 64 : ℝ) ≤ r x ^ 6 := by norm_num at h ⊢; exact h
    rw [mul_comm (1 / 64 : ℝ)]
    exact mul_le_mul_of_nonneg_left h' (sq_nonneg _)
  have hHi (x : ℝ) (hx : x ∈ Icc c d) :
      (deriv r x) ^ 2 * r x ^ 6 ≤ 64 * (deriv r x) ^ 2 := by
    have h := pow_le_pow_left₀ (hp x hx).le (hR x hx).2 6
    have h' : r x ^ 6 ≤ 64 := by norm_num at h ⊢; exact h
    rw [mul_comm (64 : ℝ)]
    exact mul_le_mul_of_nonneg_left h' (sq_nonneg _)
  have hlo : (∫ x in c..d, (1 / 64 : ℝ) * (deriv r x) ^ 2) ≤
      (∫ x in c..d, (deriv r x) ^ 2 * r x ^ 6) := intervalIntegral.integral_mono_on hcd
    (continuous_const.mul hV |>.intervalIntegrable c d) (hM.intervalIntegrable c d) hLo
  have hhi : (∫ x in c..d, (deriv r x) ^ 2 * r x ^ 6) ≤
      (∫ x in c..d, (64 : ℝ) * (deriv r x) ^ 2) := intervalIntegral.integral_mono_on hcd
    (hM.intervalIntegrable c d) (continuous_const.mul hV |>.intervalIntegrable c d) hHi
  rw [intervalIntegral.integral_const_mul] at hlo hhi
  refine ⟨hlo, hhi, ?_, ?_⟩
  · calc
      (d - c) / 256 = ∫ _ in c..d, (1 / 256 : ℝ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv, one_div]
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hcd (continuous_const.intervalIntegrable _ _) hRi
        intro x hx
        have h := pow_le_pow_left₀ (hp x hx).le (hR x hx).2 8
        have h' : r x ^ 8 ≤ 256 := by norm_num at h ⊢; exact h
        simpa only [one_div] using one_div_le_one_div_of_le (pow_pos (hp x hx) 8) h'
  · calc
      _ ≤ ∫ _ in c..d, (256 : ℝ) := by
        apply intervalIntegral.integral_mono_on hcd hRi (continuous_const.intervalIntegrable _ _)
        intro x hx
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (hR x hx).1 8
        have h' := one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) 8) h
        norm_num [one_div] at h' ⊢
        exact h'
      _ = 256 * (d - c) := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

private theorem morseCell_left_length_bounds {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    log (A / B) / 2 ≤ morseLeftMassLength A B ∧
      morseLeftMassLength A B ≤ 2 * log (A / B) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hq : (4 : ℝ) < A / B := (lt_div_iff₀ hB).mpr hAB
  have hlog2 : 2 * log (2 : ℝ) ≤ log (A / B) := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 4) hq.le
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow] at h
    simpa only [Nat.cast_ofNat] using h
  have hlog3 : log (3 / 2 : ℝ) ≤ log (A / B) :=
    log_le_log (by norm_num) ((by norm_num : (3 / 2 : ℝ) ≤ 4).trans hq.le)
  have hl := (morseRightTurn_log_bounds hB hAB).1
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (div_ne_zero hB.ne' hA.ne'),
    log_div hB.ne' hA.ne'] at hl
  rw [log_div hA.ne' hB.ne'] at hlog2
  constructor
  · rw [morseLeftMassLength, morseCellLeftCut, log_div hA.ne' hB.ne']
    linarith only [hl, hlog2, log_pos (by norm_num : (1 : ℝ) < 3 / 2)]
  · linarith only [morseLeftMassLength_log_le hB hAB, hlog3]

private theorem morseCell_right_velocity_mass_bounds {A B : ℝ} (hA : 0 < A)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r)
    (hv : ∀ x ∈ Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)),
      (1 / 100 : ℝ) * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ (3 / 100 : ℝ) * A ^ 5) :
    A ^ 6 / 1000000 ≤
        (∫ x in morseRightTurn A B..morseRightCapEnd A B (1 / 100), (deriv r x) ^ 2) ∧
      (∫ x in morseRightTurn A B..morseRightCapEnd A B (1 / 100), (deriv r x) ^ 2) ≤
        9 * A ^ 6 / 1000000 := by
  let b := morseRightTurn A B
  let e := morseRightCapEnd A B (1 / 100)
  have hbe : b ≤ e :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hV := (contDiff_infty_iff_deriv.mp hr).2.continuous.pow 2
  have hLow (x : ℝ) (hx : x ∈ Icc b e) : ((1 / 100 : ℝ) * A ^ 5) ^ 2 ≤ (deriv r x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (hv x hx).1 2
  have hHigh (x : ℝ) (hx : x ∈ Icc b e) : (deriv r x) ^ 2 ≤ ((3 / 100 : ℝ) * A ^ 5) ^ 2 :=
    pow_le_pow_left₀ ((by positivity : 0 ≤ (1 / 100 : ℝ) * A ^ 5).trans (hv x hx).1)
      (hv x hx).2 2
  have hl := intervalIntegral.integral_mono_on (μ := volume) hbe
    (continuous_const.intervalIntegrable _ _) (hV.intervalIntegrable _ _) hLow
  have hu := intervalIntegral.integral_mono_on (μ := volume) hbe
    (hV.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hHigh
  rw [intervalIntegral.integral_const, smul_eq_mul] at hl hu
  have hwidth : e - b = (1 / 100 : ℝ) / A ^ 4 := by
    simp only [e, b, morseRightCapEnd, morseRightCapLength, add_sub_cancel_left]
  have hL : (e - b) * ((1 / 100 : ℝ) * A ^ 5) ^ 2 = A ^ 6 / 1000000 := by
    rw [hwidth]
    field_simp [hA.ne']
    ring
  have hU : (e - b) * ((3 / 100 : ℝ) * A ^ 5) ^ 2 = 9 * A ^ 6 / 1000000 := by
    rw [hwidth]
    field_simp [hA.ne']
    ring
  rw [hL] at hl
  rw [hU] at hu
  exact ⟨hl, hu⟩

/-- The mass and resistance estimates on both parts of a single retained
cell. The factor `lam * s^8` is computed for its actual physical profile. -/
theorem morseRetainedCell_physical_mass_resistance_bounds {A B lam s : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hlam : 0 < lam) (hs : 0 < s)
    {r w : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hrb : r (morseRightTurn A B) = 1)
    (hclose : |r morseCellLeftCut - 1| ≤ 6 * A)
    (hEq : ∀ x ∈ Icc morseCellLeftCut (morseRightTurn A B),
      deriv (deriv r) x = -morseRho A B x * r x)
    (hR : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      1 / 2 ≤ r x ∧ r x ≤ 2)
    (hv : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      (1 / 100 : ℝ) * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ 7 * A)
    (hvL : A / 4 ≤ deriv r morseCellLeftCut)
    (hvR : ∀ x ∈ Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)),
      deriv r x ≤ (3 / 100 : ℝ) * A ^ 5)
    (hw : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      w (s * r x) = lam * s * deriv r x) :
    let a := s * r morseCellLeftCut
    let b := s * r (morseRightTurn A B)
    let e := s * r (morseRightCapEnd A B (1 / 100))
    let D := lam * s ^ 8
    let massI := ∫ z in a..b, w z * z ^ 6
    let resI := ∫ z in a..b, (w z * z ^ 8)⁻¹
    let massCap := ∫ z in b..e, w z * z ^ 6
    let resCap := ∫ z in b..e, (w z * z ^ 8)⁻¹
    (D * (morseShortLeftCapLength / 1024 * A ^ 2) ≤ massI ∧ massI ≤ D * (2688 * A ^ 2)) ∧
    (D⁻¹ * (log (A / B) / 512) ≤ resI ∧ resI ≤ D⁻¹ * (512 * log (A / B))) ∧
    (D * (A ^ 6 / 64000000) ≤ massCap ∧ massCap ≤ D * A ^ 6) ∧
    (D⁻¹ * ((A ^ 4)⁻¹ / 25600) ≤ resCap ∧ resCap ≤ D⁻¹ * (3 * (A ^ 4)⁻¹)) := by
  let a := morseCellLeftCut
  let b := morseRightTurn A B
  let e := morseRightCapEnd A B (1 / 100)
  let D := lam * s ^ 8
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hab : a ≤ b := (morseCellLeftCut_lt_rightTurn hB hAB).le
  have hbe : b ≤ e :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hae := hab.trans hbe
  have hI : Icc a b ⊆ Icc a e := fun _ hx => ⟨hx.1, hx.2.trans hbe⟩
  have hC : Icc b e ⊆ Icc a e := fun _ hx => ⟨hab.trans hx.1, hx.2⟩
  have hpos (x : ℝ) (hx : x ∈ Icc a e) : 0 < r x :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hR x hx).1
  have hvpos (x : ℝ) (hx : x ∈ Icc a e) : 0 < deriv r x :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 100) (pow_pos hA 5)).trans_le (hv x hx).1
  obtain ⟨hmI, hrI⟩ := morseCell_physical_mass_resistance_change hae hab hI
    hlam hs hr hpos hvpos hw
  obtain ⟨hmC, hrC⟩ := morseCell_physical_mass_resistance_change hae hbe hC
    hlam hs hr hpos hvpos hw
  have hwI := morseCell_weighted_model_integrals hab hr (fun x hx => hR x (hI hx))
  have hwC := morseCell_weighted_model_integrals hbe hr (fun x hx => hR x (hC hx))
  have hvmI := morseLeftCell_velocity_mass_bounds hB hAB hr hrb hclose hEq
    (fun x hx => (hpos x (hI hx)).le) hvL (fun x hx => ⟨(hvpos x (hI hx)).le, (hv x (hI hx)).2⟩)
  have hvmC := morseCell_right_velocity_mass_bounds hA hr (fun x hx => ⟨(hv x (hC hx)).1, hvR x hx⟩)
  have hlI := morseCell_left_length_bounds hB hAB
  change log (A / B) / 2 ≤ b - a ∧ b - a ≤ 2 * log (A / B) at hlI
  have hlC : e - b = (1 / 100 : ℝ) * (A ^ 4)⁻¹ := by
    simp only [e, b, morseRightCapEnd, morseRightCapLength, add_sub_cancel_left, div_eq_mul_inv]
  change _ ≤ (∫ x in a..b, (deriv r x) ^ 2) ∧ (∫ x in a..b, (deriv r x) ^ 2) ≤ _ at hvmI
  have hD : 0 < D := mul_pos hlam (pow_pos hs 8)
  have hDi : 0 ≤ D⁻¹ := (inv_pos.mpr hD).le
  dsimp only
  rw [hmI, hrI, hmC, hrC]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact mul_le_mul_of_nonneg_left (by linarith only [hwI.1, hvmI.1]) hD.le
  · exact mul_le_mul_of_nonneg_left (by linarith only [hwI.2.1, hvmI.2]) hD.le
  · exact mul_le_mul_of_nonneg_left (by linarith only [hwI.2.2.1, hlI.1]) hDi
  · exact mul_le_mul_of_nonneg_left (by linarith only [hwI.2.2.2, hlI.2]) hDi
  · exact mul_le_mul_of_nonneg_left (by linarith only [hwC.1, hvmC.1]) hD.le
  · exact mul_le_mul_of_nonneg_left
      (by linarith only [hwC.2.1, hvmC.2, pow_nonneg hA.le 6]) hD.le
  · exact mul_le_mul_of_nonneg_left (by linarith only [hwC.2.2.1, hlC]) hDi
  · exact mul_le_mul_of_nonneg_left
      (by linarith only [hwC.2.2.2, hlC, inv_nonneg.mpr (pow_nonneg hA.le 4)]) hDi

/-- The short connector estimates relative to the departure cell scales.
Here `a` is the outgoing physical radius and `b` the incoming one, even
on the left tail. -/
theorem morseAdjacentJoin_physical_mass_resistance_bounds {a b c A A' lam s U : ℝ}
    {w : ℝ → ℝ}
    (hA : 0 < A) (hA1 : A ≤ 1) (hA' : 0 < A') (hc : 0 < c) (hc1 : c ≤ 1)
    (hlam : 0 < lam) (hs : 0 < s) (ha : s / 2 ≤ a) (ha' : a ≤ 2 * s)
    (hab : a ≤ b) (hwidth : b - a = c * a * (min A A') ^ 12)
    (hwc : Continuous w) (hw : ∀ z ∈ Icc a b, 0 < w z) (hmono : MonotoneOn w (Icc a b))
    (hWL : lam * s * (A ^ 5 / 100) ≤ w a)
    (hWU : w a ≤ lam * s * ((3 / 100) * A ^ 5))
    (hcontrast : log (w b / w a) ≤ U) :
    let D := lam * s ^ 8
    (∫ z in a..b, w z * z ^ 6) ≤ 300 * c * (D * A ^ 6) * (A ^ 11 * exp U) ∧
      (∫ z in a..b, (w z * z ^ 8)⁻¹) ≤
        51200 * c * (D⁻¹ * (A ^ 4)⁻¹) * A ^ 11 := by
  let D := lam * s ^ 8
  have hap : 0 < a := (by positivity : 0 < s / 2).trans_le ha
  have haMem : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hbMem : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hWa := hw a haMem
  have hWb := hw b hbMem
  have hmin : 0 < min A A' := lt_min hA hA'
  have hminA : min A A' ≤ A := min_le_left _ _
  have hminPow := pow_le_pow_left₀ hmin.le hminA 12
  have hminOne : (min A A') ^ 12 ≤ 1 := pow_le_one₀ hmin.le (hminA.trans hA1)
  have hb4 : b ≤ 4 * s := by
    have hcA : c * a ≤ a := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hap.le
    have h := mul_le_mul_of_nonneg_left hminOne (mul_nonneg hc.le hap.le)
    rw [mul_one, ← hwidth] at h
    linarith only [h, hcA, ha']
  have hwidth' : b - a ≤ 2 * c * s * A ^ 12 := by
    rw [hwidth]
    calc
      _ ≤ (c * a) * A ^ 12 := mul_le_mul_of_nonneg_left hminPow (mul_nonneg hc.le hap.le)
      _ ≤ (c * (2 * s)) * A ^ 12 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha' hc.le) (pow_nonneg hA.le _)
      _ = _ := by ring
  have hWb' : w b ≤ exp U * (lam * s * ((3 / 100) * A ^ 5)) := by
    have h := exp_le_exp.mpr hcontrast
    rw [exp_log (div_pos hWb hWa)] at h
    exact ((div_le_iff₀ hWa).mp h).trans (mul_le_mul_of_nonneg_left hWU (exp_pos U).le)
  let M := exp U * (lam * s * ((3 / 100) * A ^ 5)) * (4 * s) ^ 6
  let R := (lam * s * (A ^ 5 / 100) * (s / 2) ^ 8)⁻¹
  have hMp : 0 ≤ M := by dsimp only [M]; positivity
  have hRp : 0 ≤ R := by dsimp only [R]; positivity
  have hMass (x : ℝ) (hx : x ∈ Icc a b) : w x * x ^ 6 ≤ M :=
    mul_le_mul ((hmono hx hbMem hx.2).trans hWb')
      (pow_le_pow_left₀ (hap.le.trans hx.1) (hx.2.trans hb4) 6) (pow_nonneg (hap.le.trans hx.1) _)
      (by positivity)
  have hRes (x : ℝ) (hx : x ∈ Icc a b) : (w x * x ^ 8)⁻¹ ≤ R := by
    have h : lam * s * (A ^ 5 / 100) * (s / 2) ^ 8 ≤ w x * x ^ 8 :=
      mul_le_mul (hWL.trans (hmono haMem hx hx.1))
        (pow_le_pow_left₀ (by positivity) (ha.trans hx.1) 8) (by positivity) (hw x hx).le
    have hp : 0 < lam * s * (A ^ 5 / 100) * (s / 2) ^ 8 := by positivity
    simpa only [R, one_div] using one_div_le_one_div_of_le hp h
  have hMi : IntervalIntegrable (fun x => w x * x ^ 6) volume a b :=
    (hwc.mul (continuous_id.pow 6)).intervalIntegrable _ _
  have hRi : IntervalIntegrable (fun x => (w x * x ^ 8)⁻¹) volume a b :=
    ((hwc.continuousOn.mul (continuous_id.continuousOn.pow 8)).inv₀
      (fun x hx => (mul_pos (hw x hx) (pow_pos (hap.trans_le hx.1) 8)).ne')).intervalIntegrable_of_Icc hab
  have hM := intervalIntegral.integral_mono_on (μ := volume) hab hMi
    (continuous_const.intervalIntegrable _ _) hMass
  have hR := intervalIntegral.integral_mono_on (μ := volume) hab hRi
    (continuous_const.intervalIntegrable _ _) hRes
  rw [intervalIntegral.integral_const, smul_eq_mul] at hM hR
  constructor
  · calc
      _ ≤ (b - a) * M := hM
      _ ≤ (2 * c * s * A ^ 12) * M := mul_le_mul_of_nonneg_right hwidth' hMp
      _ ≤ 300 * c * (D * A ^ 6) * (A ^ 11 * exp U) := by
        have hp : 0 ≤ c * (D * A ^ 6) * (A ^ 11 * exp U) := by dsimp only [D]; positivity
        dsimp only [M, D] at hp ⊢
        nlinarith only [hp]
  · calc
      _ ≤ (b - a) * R := hR
      _ ≤ (2 * c * s * A ^ 12) * R := mul_le_mul_of_nonneg_right hwidth' hRp
      _ = 51200 * c * (D⁻¹ * (A ^ 4)⁻¹) * A ^ 11 := by
        dsimp only [R, D]
        field_simp [hlam.ne', hs.ne', hA.ne']
        ring

private theorem morseCell_A_pow11_le (T : Statements.MorseChainData) (n : ℕ)
    (hd : T.d n = morseChainInteger n) :
    Statements.morseChainA T n ^ 11 ≤ (9 : ℝ) ^ 11 * exp (-11 * (n : ℝ) ^ 2) := by
  have hA := morseChainA_exp_bounds T n hd
  have hp : 0 ≤ Statements.morseChainA T n :=
    ((by positivity : 0 < exp (-(n : ℝ) ^ 2) / 3).trans_le hA.1).le
  have he : ((11 : ℕ) : ℝ) * (-(n : ℝ) ^ 2) = -11 * (n : ℝ) ^ 2 := by
    norm_num [mul_neg, neg_mul]
  calc
    _ ≤ (9 * exp (-(n : ℝ) ^ 2)) ^ 11 := pow_le_pow_left₀ hp hA.2 11
    _ = _ := by rw [mul_pow, ← Real.exp_nat_mul, he]

/-- The two relative short-join errors for the actual amplitudes, in
either adjacent orientation. The departure index is `n`. -/
theorem morseAdjacentJoin_physical_error_bounds (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m : ℕ} (hn : 100 ≤ n)
    (hNn : T.index ≤ n) (hNm : T.index ≤ m) (hadj : m = n + 1 ∨ n = m + 1)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m)
    {a b c sL sR vn vm : ℝ} {w : ℝ → ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hsL : 0 < sL) (hsR : 0 < sR)
    (hS : |log (sR / sL)| ≤ 3) (ha : sL / 2 ≤ a) (ha' : a ≤ 2 * sL) (hab : a ≤ b)
    (hwidth : b - a = c * a * (min (Statements.morseChainA T n) (Statements.morseChainA T m)) ^ 12)
    (hwc : Continuous w) (hw : ∀ z ∈ Icc a b, 0 < w z) (hmono : MonotoneOn w (Icc a b))
    (hvn : (1 / 100 : ℝ) * Statements.morseChainA T n ^ 5 ≤ vn ∧
      vn ≤ (3 / 100 : ℝ) * Statements.morseChainA T n ^ 5)
    (hvm : Statements.morseChainA T m / 4 ≤ vm ∧ vm ≤ 7 * Statements.morseChainA T m)
    (hWa : w a = Statements.morseChainAmplitude T σ n * sL * vn)
    (hWb : w b = Statements.morseChainAmplitude T σ m * sR * vm) :
    let A := Statements.morseChainA T n
    let D := Statements.morseChainAmplitude T σ n * sL ^ 8
    let E := 10 * (n : ℝ) ^ (3 / 2 : ℝ) + 2 * (n : ℝ) + 63
    (∫ z in a..b, w z * z ^ 6) ≤
        (300 * c * 9 ^ 11 * exp (-7 * (n : ℝ) ^ 2 + E)) * (D * A ^ 6) ∧
      (∫ z in a..b, (w z * z ^ 8)⁻¹) ≤
        (51200 * c * 9 ^ 11 * exp (-11 * (n : ℝ) ^ 2)) * (D⁻¹ * (A ^ 4)⁻¹) ∧
      exp (-7 * (n : ℝ) ^ 2 + E) ≤ 1 := by
  let A := Statements.morseChainA T n
  let lam := Statements.morseChainAmplitude T σ n
  let D := lam * sL ^ 8
  let E : ℝ := 10 * (n : ℝ) ^ (3 / 2 : ℝ) + 2 * (n : ℝ) + 63
  let U : ℝ := 4 * (n : ℝ) ^ 2 + E
  have hA : 0 < A :=
    (by positivity : 0 < exp (-(n : ℝ) ^ 2) / 3).trans_le (morseChainA_exp_bounds T n hdn).1
  have hAm : 0 < Statements.morseChainA T m :=
    (by positivity : 0 < exp (-(m : ℝ) ^ 2) / 3).trans_le (morseChainA_exp_bounds T m hdm).1
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog9 : log (9 : ℝ) ≤ 8 := by
    simpa only [show (9 : ℝ) - 1 = 8 by norm_num] using log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
  have hA1 : A ≤ 1 :=
    morseChainA_le_of_sq_ge_log T n hdn (by norm_num) (by
      rw [div_one]
      have hnSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hnR 2
      linarith only [hlog9, hnSq])
  have hlam : 0 < lam := morseChainAmplitude_pos T σ hσ n
  have hErr := (morseJoin_height_log_contrast T σ hσ ((by norm_num : 1 ≤ 100).trans hn)
    hNn hNm hadj hdn hdm hsL hsR hS hvn hvm).2.2.1
  have hLog : log (w b / w a) ≤ U := by
    rw [hWa, hWb]
    dsimp only [U, E]
    linarith only [(abs_le.mp hErr).2]
  have hLo : lam * sL * (A ^ 5 / 100) ≤ w a := by
    rw [hWa, show A ^ 5 / 100 = (1 / 100 : ℝ) * A ^ 5 by ring]
    exact mul_le_mul_of_nonneg_left hvn.1 (mul_nonneg hlam.le hsL.le)
  have hHi : w a ≤ lam * sL * ((3 / 100) * A ^ 5) := by
    rw [hWa]
    exact mul_le_mul_of_nonneg_left hvn.2 (mul_nonneg hlam.le hsL.le)
  obtain ⟨hM, hR⟩ := morseAdjacentJoin_physical_mass_resistance_bounds hA hA1 hAm
    hc hc1 hlam hsL ha ha' hab hwidth hwc hw hmono hLo hHi hLog
  have hPow := morseCell_A_pow11_le T n hdn
  have hME : A ^ 11 * exp U ≤ (9 : ℝ) ^ 11 * exp (-7 * (n : ℝ) ^ 2 + E) := by
    calc
      _ ≤ ((9 : ℝ) ^ 11 * exp (-11 * (n : ℝ) ^ 2)) * exp U :=
        mul_le_mul_of_nonneg_right hPow (exp_pos U).le
      _ = _ := by
        rw [mul_assoc, ← exp_add]
        have he : -11 * (n : ℝ) ^ 2 + U = -7 * (n : ℝ) ^ 2 + E := by dsimp only [U]; ring
        rw [he]
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ 300 * c * (D * A ^ 6) * (A ^ 11 * exp U) := hM
      _ ≤ 300 * c * (D * A ^ 6) * (9 ^ 11 * exp (-7 * (n : ℝ) ^ 2 + E)) :=
        mul_le_mul_of_nonneg_left hME (by dsimp only [D]; positivity)
      _ = _ := by ring
  · calc
      _ ≤ 51200 * c * (D⁻¹ * (A ^ 4)⁻¹) * A ^ 11 := hR
      _ ≤ 51200 * c * (D⁻¹ * (A ^ 4)⁻¹) * (9 ^ 11 * exp (-11 * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hPow (by dsimp only [D]; positivity)
      _ = _ := by ring
  · have hE : 0 ≤ E := by dsimp only [E]; positivity
    have h := morseJoin_height_log_range_of_error (x := U) hn (by
      dsimp only [U]
      rw [add_sub_cancel_left, abs_of_nonneg hE])
    apply exp_le_one_iff.mpr
    dsimp only [U] at h
    linarith only [h.2, sq_nonneg (n : ℝ)]

/-- The long cap and its following short join form one resistance
interval in increasing physical radius. Both integrals are exactly
additive, and the cap lower bound survives the short join. -/
theorem morseCell_departure_interval_bounds {b e d A D EM ER : ℝ} {w : ℝ → ℝ}
    (hb : 0 < b) (hbe : b ≤ e) (hed : e ≤ d)
    (hwc : Continuous w) (hwp : ∀ z ∈ Icc b d, 0 < w z)
    (hMcap : (∫ z in b..e, w z * z ^ 6) ≤ D * A ^ 6)
    (hRcap : D⁻¹ * ((A ^ 4)⁻¹ / 25600) ≤ (∫ z in b..e, (w z * z ^ 8)⁻¹) ∧
      (∫ z in b..e, (w z * z ^ 8)⁻¹) ≤ D⁻¹ * (3 * (A ^ 4)⁻¹))
    (hMjoin : (∫ z in e..d, w z * z ^ 6) ≤ EM * (D * A ^ 6))
    (hRjoin : (∫ z in e..d, (w z * z ^ 8)⁻¹) ≤ ER * (D⁻¹ * (A ^ 4)⁻¹)) :
    (∫ z in b..d, w z * z ^ 6) = (∫ z in b..e, w z * z ^ 6) + (∫ z in e..d, w z * z ^ 6) ∧
    (∫ z in b..d, (w z * z ^ 8)⁻¹) =
        (∫ z in b..e, (w z * z ^ 8)⁻¹) + (∫ z in e..d, (w z * z ^ 8)⁻¹) ∧
    (∫ z in b..d, w z * z ^ 6) ≤ (1 + EM) * (D * A ^ 6) ∧
    D⁻¹ * ((A ^ 4)⁻¹ / 25600) ≤ (∫ z in b..d, (w z * z ^ 8)⁻¹) ∧
    (∫ z in b..d, (w z * z ^ 8)⁻¹) ≤ (3 + ER) * (D⁻¹ * (A ^ 4)⁻¹) := by
  have hMc : Continuous (fun z => w z * z ^ 6) := hwc.mul (continuous_id.pow 6)
  have hRc : ContinuousOn (fun z => (w z * z ^ 8)⁻¹) (Icc b d) :=
    (hwc.continuousOn.mul (continuous_id.continuousOn.pow 8)).inv₀
      (fun z hz => (mul_pos (hwp z hz) (pow_pos (hb.trans_le hz.1) 8)).ne')
  have hM := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hMc.intervalIntegrable b e) (hMc.intervalIntegrable e d)
  have hR := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hRc.mono (fun _ hx => ⟨hx.1, hx.2.trans hed⟩)).intervalIntegrable_of_Icc hbe)
    ((hRc.mono (fun _ hx => ⟨hbe.trans hx.1, hx.2⟩)).intervalIntegrable_of_Icc hed)
  have hRnonneg : 0 ≤ ∫ z in e..d, (w z * z ^ 8)⁻¹ :=
    intervalIntegral.integral_nonneg hed (fun z hz => inv_nonneg.mpr
      (mul_nonneg (hwp z ⟨hbe.trans hz.1, hz.2⟩).le (pow_nonneg (hb.le.trans (hbe.trans hz.1)) _)))
  refine ⟨hM.symm, hR.symm, ?_, ?_, ?_⟩
  · rw [← hM]
    calc
      _ ≤ (D * A ^ 6) + EM * (D * A ^ 6) := add_le_add hMcap hMjoin
      _ = _ := by ring
  · rw [← hR]
    exact hRcap.1.trans (le_add_of_nonneg_right hRnonneg)
  · rw [← hR]
    calc
      _ ≤ D⁻¹ * (3 * (A ^ 4)⁻¹) + ER * (D⁻¹ * (A ^ 4)⁻¹) := add_le_add hRcap.2 hRjoin
      _ = _ := by ring

/-- The normalized cross-cell product in §5, with the physical scales
of the two different cells retained. The departure index is `n`. -/
theorem morseCell_cross_scale_log_error (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m : ℕ} (hn : 1 ≤ n)
    (hNn : T.index ≤ n) (hNm : T.index ≤ m) (hadj : m = n + 1 ∨ n = m + 1)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m)
    {sL sR : ℝ} (hsL : 0 < sL) (hsR : 0 < sR) (hS : |log (sR / sL)| ≤ 3) :
    let An := Statements.morseChainA T n
    let Am := Statements.morseChainA T m
    let ln := Statements.morseChainAmplitude T σ n
    let lm := Statements.morseChainAmplitude T σ m
    let Q := (lm / ln) * (sR / sL) ^ 8 * (Am ^ 2 / An ^ 4)
    0 < Q ∧
      |log Q - 2 * (n : ℝ) ^ 2| ≤ 10 * (n : ℝ) ^ (3 / 2 : ℝ) + 4 * (n : ℝ) + 75 := by
  let An := Statements.morseChainA T n
  let Am := Statements.morseChainA T m
  let ln := Statements.morseChainAmplitude T σ n
  let lm := Statements.morseChainAmplitude T σ m
  let Q := (lm / ln) * (sR / sL) ^ 8 * (Am ^ 2 / An ^ 4)
  have hAn : 0 < An :=
    (by positivity : 0 < exp (-(n : ℝ) ^ 2) / 3).trans_le (morseChainA_exp_bounds T n hdn).1
  have hAm : 0 < Am :=
    (by positivity : 0 < exp (-(m : ℝ) ^ 2) / 3).trans_le (morseChainA_exp_bounds T m hdm).1
  have hln : 0 < ln := morseChainAmplitude_pos T σ hσ n
  have hlm : 0 < lm := morseChainAmplitude_pos T σ hσ m
  have hL : 0 < (lm / ln) * (sR / sL) ^ 8 := by positivity
  have hA : 0 < Am ^ 2 / An ^ 4 := by positivity
  have hLog : log Q = log (lm / ln) + 8 * log (sR / sL) + 2 * log Am - 4 * log An := by
    dsimp only [Q]
    rw [log_mul hL.ne' hA.ne', log_mul (div_ne_zero hlm.ne' hln.ne')
      (pow_ne_zero 8 (div_ne_zero hsR.ne' hsL.ne')),
      log_div (pow_ne_zero 2 hAm.ne') (pow_ne_zero 4 hAn.ne')]
    simp only [log_pow, Nat.cast_ofNat]
    ring
  have hsq : |(m : ℝ) ^ 2 - (n : ℝ) ^ 2| ≤ 2 * (n : ℝ) + 1 := by
    rcases hadj with he | he
    · have hm : (m : ℝ) = (n : ℝ) + 1 := by exact_mod_cast he
      rw [hm]
      exact abs_le.mpr ⟨by nlinarith only [Nat.cast_nonneg (α := ℝ) n], by nlinarith only []⟩
    · have hn' : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast he
      rw [hn']
      exact abs_le.mpr ⟨by nlinarith only [], by nlinarith only [Nat.cast_nonneg (α := ℝ) m]⟩
  have hl := morseChainAmplitude_log_adjacent_bound T σ hσ hn hNn hNm hadj
  have hAl := morseChainA_log_error T n hdn
  have hAr := morseChainA_log_error T m hdm
  refine ⟨mul_pos hL hA, ?_⟩
  change |log Q - 2 * (n : ℝ) ^ 2| ≤ _
  rw [hLog]
  exact abs_le.mpr ⟨
    by linarith only [(abs_le.mp hl).1, (abs_le.mp hS).1, (abs_le.mp hAl).2,
      (abs_le.mp hAr).1, (abs_le.mp hsq).2],
    by linarith only [(abs_le.mp hl).2, (abs_le.mp hS).2, (abs_le.mp hAl).1,
      (abs_le.mp hAr).2, (abs_le.mp hsq).1]⟩

end ContinuousFlexibility.Radial
