import ContinuousFlexibility.Radial.OuterJoinScale
import ContinuousFlexibility.Radial.MorseRealizedConnectorBounds

/-!
# The actual positive-glue transfer product

The two scalar integrals in the balanced first-order estimate are
controlled by the departure height, arrival height, and physical width
of the connector.  The explicit Morse scales then put this product on
the action scale of either adjacent cell.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem morseConnector_balanced_product_le {w : ℝ → ℝ} {a l r : ℝ}
    (ha : 0 < a) (hal : a ≤ l) (hlr : l < r) (hw : ContDiff ℝ ∞ w)
    (hwp : ∀ x ∈ Icc l r, 0 < w x) (hmono : MonotoneOn w (Icc l r)) :
    (∫ x in l..r, (w x)⁻¹) * (∫ x in l..r, deriv w x / x) ≤
      (r - l) * w r / (a * w l) := by
  have hl : l ∈ Icc l r := left_mem_Icc.mpr hlr.le
  have hr : r ∈ Icc l r := right_mem_Icc.mpr hlr.le
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
  have hi : (∫ x in l..r, (w x)⁻¹) ≤ (r - l) / w l := by
    have hpoint (x : ℝ) (hx : x ∈ Icc l r) : (w x)⁻¹ ≤ (w l)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (hwp l hl) (hmono hl hx hx.1)
    have h := intervalIntegral.integral_mono_on hlr.le hI
      (continuous_const.intervalIntegrable l r) hpoint
    simpa only [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using h
  have hFTC : (∫ x in l..r, deriv w x) = w r - w l :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hdc.intervalIntegrable l r)
  have hj : (∫ x in l..r, deriv w x / x) ≤ w r / a := by
    have hpoint (x : ℝ) (hx : x ∈ Icc l r) : deriv w x / x ≤ deriv w x / a :=
      div_le_div_of_nonneg_left (hderiv₀ x hx) ha (hal.trans hx.1)
    have h := intervalIntegral.integral_mono_on hlr.le hJ
      ((hdc.div_const a).intervalIntegrable l r) hpoint
    rw [intervalIntegral.integral_div_const, hFTC] at h
    exact h.trans (div_le_div_of_nonneg_right (sub_le_self _ (hwp l hl).le) ha.le)
  have hj₀ : 0 ≤ ∫ x in l..r, deriv w x / x :=
    intervalIntegral.integral_nonneg hlr.le
      (fun x hx => div_nonneg (hderiv₀ x hx) (hx₀ x hx).le)
  calc
    _ ≤ ((r - l) / w l) * (w r / a) :=
      mul_le_mul hi hj hj₀ (div_nonneg (sub_nonneg.mpr hlr.le) (hwp l hl).le)
    _ = _ := by field_simp [ha.ne', (hwp l hl).ne'] <;> ring

/-- A realized glue costs the smaller adjacent cap action.  In particular,
the glue preceding cell `n` can be charged to `j sqrt(A_n)`. -/
theorem morseRealizedJoin_balanced_product_le {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {K : ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K)
    (side : Bool) (k : ℕ) (hk : T.index ≤ k) :
    let n := if side then k else k + 1
    let m := if side then k + 1 else k
    (∫ x in T.joinLeft side k..T.joinRight side k, (D.w x)⁻¹) *
        (∫ x in T.joinLeft side k..T.joinRight side k, deriv D.w x / x) ≤
      (C 0 * K ^ 2 / D.a) * exp 400 * min (morseChainA T n) (morseChainA T m) := by
  let n := if side then k else k + 1
  let m := if side then k + 1 else k
  let A := morseChainA T n
  let B := morseChainA T m
  let H := max A B
  let L := min A B
  let lam := morseChainAmplitude T σ n
  let eta := morseChainAmplitude T σ m
  let l := T.joinLeft side k
  let r := T.joinRight side k
  obtain ⟨hn, hm, hadj, hjl, hjr, hwidth⟩ := morseRealizedJoin_endpoints h side k hk
  have horder (i : ℕ) (hi : T.index ≤ i) : T.leftX side i ≤ T.rightX side i :=
    ((h.retained_data side i hi).2.2.2.1.trans
      (h.retained_data side i hi).2.2.2.2.1).le
  have hnr : T.rightX side n ∈ Icc (T.leftX side n) (T.rightX side n) :=
    right_mem_Icc.mpr (horder n hn)
  have hml : T.leftX side m ∈ Icc (T.leftX side m) (T.rightX side m) :=
    left_mem_Icc.mpr (horder m hm)
  have hlD : l ∈ radialCore D := by rw [hjl]; exact h.radius_mem_core side n hn _ hnr
  have hrD : r ∈ radialCore D := by rw [hjr]; exact h.radius_mem_core side m hm _ hml
  have ha : 0 < D.a := h.geometry.1
  have hwp (x : ℝ) (hx : x ∈ Icc l r) : 0 < D.w x :=
    h.geometry.2.2.2.2.1 x ⟨hlD.1.trans_le hx.1, hx.2.trans_lt hrD.2⟩
  have hw : ContDiff ℝ ∞ D.w := h.geometry.2.2.1.1
  have hj := h.join_data side k hk
  have hmono := morseConnector_monotone_of_logSlope hw (ha.trans hlD.1)
    hwp hj.2.2.2.2
  have hA : 0 < A :=
    (mul_pos (by norm_num : (0 : ℝ) < 4) (h.retained_data side n hn).1).trans
      (h.retained_data side n hn).2.1
  have hB : 0 < B :=
    (mul_pos (by norm_num : (0 : ℝ) < 4) (h.retained_data side m hm).1).trans
      (h.retained_data side m hm).2.1
  have hH : 0 < H := hA.trans_le (le_max_left _ _)
  have hL : 0 < L := lt_min hA hB
  have hlam : 0 < lam := morseChainAmplitude_pos T σ hσ n
  have heta : 0 < eta := morseChainAmplitude_pos T σ hσ m
  have hK : 0 < K := hcell.pos
  have hC : 0 < C 0 := h.constants_pos 0
  have harrival : D.w r ≤ eta * K * B := by
    rw [hjr, h.profile_eq side m hm _ hml]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hcell.left_speed_upper side m hm) heta.le
  have hdeparture : lam * A ^ 5 / K ≤ D.w l := by
    rw [hjl, h.profile_eq side n hn _ hnr]
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left (hcell.right_speed_lower side n hn) hlam.le
  have hdep : 0 < lam * A ^ 5 / K := by positivity
  have htop : (r - l) * D.w r ≤ (C 0 * H ^ 12) * (eta * K * B) :=
    mul_le_mul hwidth harrival (hwp r (right_mem_Icc.mpr hj.1.le)).le (by positivity)
  have hratio : (r - l) * D.w r / (D.a * D.w l) ≤
      ((C 0 * H ^ 12) * (eta * K * B)) / (D.a * (lam * A ^ 5 / K)) := by
    calc
      _ ≤ ((C 0 * H ^ 12) * (eta * K * B)) / (D.a * D.w l) :=
        div_le_div_of_nonneg_right htop
          (mul_pos ha (hwp l (left_mem_Icc.mpr hj.1.le))).le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
        (mul_pos ha hdep)
        (mul_le_mul_of_nonneg_left hdeparture ha.le)
  have hscale := morseAdjacentScale_transfer_factor_le T σ hσ hn hm hadj
    (h.d_eq n hn) (h.d_eq m hm)
  have hcoef : 0 ≤ C 0 * K ^ 2 / D.a := by positivity
  calc
    _ ≤ (r - l) * D.w r / (D.a * D.w l) :=
      morseConnector_balanced_product_le ha hlD.1.le hj.1 hw hwp hmono
    _ ≤ ((C 0 * H ^ 12) * (eta * K * B)) / (D.a * (lam * A ^ 5 / K)) := hratio
    _ = (C 0 * K ^ 2 / D.a) * ((eta / lam) * B * H ^ 12 / (A ^ 5 * L)) * L := by
      field_simp [ha.ne', hlam.ne', hA.ne', hK.ne', hL.ne'] <;> ring
    _ ≤ (C 0 * K ^ 2 / D.a) * exp 400 * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hcoef) hL.le

end ContinuousFlexibility.Radial
