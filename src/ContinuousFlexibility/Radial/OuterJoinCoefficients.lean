import ContinuousFlexibility.Radial.OuterCoreEnergy

/-!
# Separate coefficient integrals on the actual positive connector

No lower bound for the connector width is used.  The ordinary state
prefactor is controlled from its departure and arrival heights.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem morseConnector_coefficient_integrals {w : ℝ → ℝ} {a l r : ℝ}
    (ha : 0 < a) (hal : a ≤ l) (hlr : l < r) (hw : ContDiff ℝ ∞ w)
    (hwp : ∀ x ∈ Icc l r, 0 < w x) (hmono : MonotoneOn w (Icc l r)) :
    (0 ≤ ∫ x in l..r, (w x)⁻¹) ∧
      (∫ x in l..r, (w x)⁻¹) ≤ (r - l) / w l ∧
      (0 ≤ ∫ x in l..r, deriv w x / x) ∧
      (∫ x in l..r, deriv w x / x) ≤ w r / a := by
  have hl : l ∈ Icc l r := left_mem_Icc.mpr hlr.le
  have hx₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 < x := ha.trans_le (hal.trans hx.1)
  have hd (x : ℝ) : HasDerivAt w (deriv w x) x :=
    (hw.differentiable (by simp) x).hasDerivAt
  have hdc : Continuous (deriv w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hderiv₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 ≤ deriv w x := by
    have h := hmono.derivWithin_nonneg (x := x)
    rwa [(hd x).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hlr x hx)] at h
  have hI : IntervalIntegrable (fun x => (w x)⁻¹) volume l r :=
    (hw.continuous.continuousOn.inv₀ (fun x hx => (hwp x hx).ne')).intervalIntegrable_of_Icc hlr.le
  have hJ : IntervalIntegrable (fun x => deriv w x / x) volume l r :=
    (hdc.continuousOn.div continuousOn_id (fun x hx => (hx₀ x hx).ne')).intervalIntegrable_of_Icc hlr.le
  refine ⟨intervalIntegral.integral_nonneg hlr.le (fun x hx => inv_nonneg.mpr (hwp x hx).le), ?_,
    intervalIntegral.integral_nonneg hlr.le
      (fun x hx => div_nonneg (hderiv₀ x hx) (hx₀ x hx).le), ?_⟩
  · have hpoint (x : ℝ) (hx : x ∈ Icc l r) : (w x)⁻¹ ≤ (w l)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (hwp l hl) (hmono hl hx hx.1)
    have hh := intervalIntegral.integral_mono_on hlr.le hI
      (continuous_const.intervalIntegrable l r) hpoint
    simpa only [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using hh
  · have hFTC : (∫ x in l..r, deriv w x) = w r - w l :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
        (hdc.intervalIntegrable l r)
    have hpoint (x : ℝ) (hx : x ∈ Icc l r) : deriv w x / x ≤ deriv w x / a :=
      div_le_div_of_nonneg_left (hderiv₀ x hx) ha (hal.trans hx.1)
    have hh := intervalIntegral.integral_mono_on hlr.le hJ
      ((hdc.div_const a).intervalIntegrable l r) hpoint
    rw [intervalIntegral.integral_div, hFTC] at hh
    exact hh.trans (div_le_div_of_nonneg_right (sub_le_self _ (hwp l hl).le) ha.le)

theorem outer_state_integral_identities (D : ReferenceData) (j scale l r : ℝ) :
    (∫ x in l..r, scale / D.w x) = scale * (∫ x in l..r, (D.w x)⁻¹) ∧
      (∫ x in l..r, j ^ 2 * deriv D.w x / (scale * x)) =
        (j ^ 2 / scale) * (∫ x in l..r, deriv D.w x / x) := by
  constructor
  · simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul]
  · have heq : (fun x => j ^ 2 * deriv D.w x / (scale * x)) =
        (fun x => (j ^ 2 / scale) * (deriv D.w x / x)) := by
      funext x
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq, intervalIntegral.integral_const_mul]

/-- The two actual state integrals before their numerical scales are
absorbed into the frequency-band exponential. -/
theorem morseRealizedJoin_state_integrals {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {K j scale : ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale)
    (side : Bool) (k : ℕ) (hk : T.index ≤ k) :
    let n := if side then k else k + 1
    let m := if side then k + 1 else k
    let a := ∫ x in T.joinLeft side k..T.joinRight side k, scale / D.w x
    let b := ∫ x in T.joinLeft side k..T.joinRight side k, j ^ 2 * deriv D.w x / (scale * x)
    0 ≤ a ∧ 0 ≤ b ∧
      a ≤ C 0 * K * (max (morseChainA T n) (morseChainA T m)) ^ 12 *
        (scale / morseChainAmplitude T σ n) * (morseChainA T n)⁻¹ ^ 5 ∧
      b ≤ (K / D.a) * j ^ 2 * (morseChainAmplitude T σ m / scale) * morseChainA T m := by
  let n := if side then k else k + 1
  let m := if side then k + 1 else k
  let A := morseChainA T n
  let B := morseChainA T m
  let lam := morseChainAmplitude T σ n
  let eta := morseChainAmplitude T σ m
  let l := T.joinLeft side k
  let r := T.joinRight side k
  obtain ⟨hn, hm, hadj, hjl, hjr, hwidth⟩ := morseRealizedJoin_endpoints h side k hk
  have horder (i : ℕ) (hi : T.index ≤ i) : T.leftX side i ≤ T.rightX side i :=
    ((h.retained_data side i hi).2.2.2.1.trans
      (h.retained_data side i hi).2.2.2.2.1).le
  have hnr := right_mem_Icc.mpr (horder n hn)
  have hml := left_mem_Icc.mpr (horder m hm)
  have hlD : l ∈ radialCore D := by
    change T.joinLeft side k ∈ radialCore D
    rw [hjl]
    exact h.radius_mem_core side n hn _ hnr
  have hrD : r ∈ radialCore D := by
    change T.joinRight side k ∈ radialCore D
    rw [hjr]
    exact h.radius_mem_core side m hm _ hml
  have ha : 0 < D.a := h.geometry.1
  have hwp (x : ℝ) (hx : x ∈ Icc l r) : 0 < D.w x :=
    h.geometry.2.2.2.2.1 x ⟨hlD.1.trans_le hx.1, hx.2.trans_lt hrD.2⟩
  have hw : ContDiff ℝ ∞ D.w := h.geometry.2.2.1.1
  have hj := h.join_data side k hk
  have hmono := morseConnector_monotone_of_logSlope hw (ha.trans hlD.1) hwp hj.2.2.2.2
  have hA : 0 < A :=
    (mul_pos (by norm_num : (0 : ℝ) < 4) (h.retained_data side n hn).1).trans
      (h.retained_data side n hn).2.1
  have hlam : 0 < lam := morseChainAmplitude_pos T σ hσ n
  have heta : 0 < eta := morseChainAmplitude_pos T σ hσ m
  have hK : 0 < K := hcell.pos
  have hC : 0 < C 0 := h.constants_pos 0
  have harrival : D.w r ≤ eta * K * B := by
    change D.w (T.joinRight side k) ≤ eta * K * B
    rw [hjr, h.profile_eq side m hm _ hml]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hcell.left_speed_upper side m hm) heta.le
  have hdeparture : lam * A ^ 5 / K ≤ D.w l := by
    change lam * A ^ 5 / K ≤ D.w (T.joinLeft side k)
    rw [hjl, h.profile_eq side n hn _ hnr]
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left (hcell.right_speed_lower side n hn) hlam.le
  have hi := morseConnector_coefficient_integrals ha hlD.1.le hj.1 hw hwp hmono
  have heq := outer_state_integral_identities D j scale l r
  dsimp only
  rw [heq.1, heq.2]
  refine ⟨mul_nonneg hscale.le hi.1, mul_nonneg (div_nonneg (sq_nonneg j) hscale.le) hi.2.2.1, ?_, ?_⟩
  · calc
      _ ≤ scale * ((r - l) / D.w l) := mul_le_mul_of_nonneg_left hi.2.1 hscale.le
      _ ≤ scale * ((C 0 * (max A B) ^ 12) / (lam * A ^ 5 / K)) := by
        apply mul_le_mul_of_nonneg_left _ hscale.le
        exact (div_le_div_of_nonneg_right hwidth (hwp l (left_mem_Icc.mpr hj.1.le)).le).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hdeparture)
      _ = _ := by
        change scale * ((C 0 * (max A B) ^ 12) / (lam * A ^ 5 / K)) =
          C 0 * K * (max A B) ^ 12 * (scale / lam) * A⁻¹ ^ 5
        field_simp [hlam.ne', hK.ne', hA.ne'] <;> ring
  · calc
      _ ≤ (j ^ 2 / scale) * (D.w r / D.a) :=
        mul_le_mul_of_nonneg_left hi.2.2.2 (div_nonneg (sq_nonneg j) hscale.le)
      _ ≤ (j ^ 2 / scale) * ((eta * K * B) / D.a) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right harrival ha.le)
          (div_nonneg (sq_nonneg j) hscale.le)
      _ = _ := by field_simp [ha.ne', hscale.ne'] <;> ring

end ContinuousFlexibility.Radial
