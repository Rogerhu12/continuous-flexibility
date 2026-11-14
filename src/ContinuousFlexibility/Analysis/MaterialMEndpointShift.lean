module

public import ContinuousFlexibility.Analysis.MaterialSampleShift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The actual material weight under a bounded endpoint displacement

The logarithmic derivative of the model weight is bounded by its actual
`E0` exponent. The mean value theorem therefore preserves every real
power of `M`, including negative powers, at the cost of a fixed `E0`
power. No extra material order or change of material data is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

private theorem materialE0Exponent_one_le {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ materialE0Exponent x := by
  have hl : 1 ≤ materialLogFactor x := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (le_add_of_nonneg_right hx : Real.exp 1 ≤ Real.exp 1 + x)
    simpa only [Real.log_exp, materialLogFactor] using h
  have ht := mul_nonneg (Real.rpow_nonneg hx (5 / 2 : ℝ)) (zero_le_one.trans hl)
  change 1 ≤ 1 + x ^ (5 / 2 : ℝ) * materialLogFactor x
  linarith only [ht]

private theorem materialMExponent_hasDerivAt {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt materialMExponent
      ((5 / 2 : ℝ) * x ^ (3 / 2 : ℝ) * materialLogFactor x ^ 2 +
        x ^ (5 / 2 : ℝ) *
          (2 * materialLogFactor x * (Real.exp 1 + x)⁻¹)) x := by
  have hp : HasDerivAt (fun t : ℝ => t ^ (5 / 2 : ℝ))
      ((5 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) x := by
    convert Real.hasDerivAt_rpow_const (x := x) (p := (5 / 2 : ℝ))
      (Or.inr (by norm_num)) using 1 <;> norm_num
  have hl : HasDerivAt materialLogFactor ((Real.exp 1 + x)⁻¹) x := by
    have hfun : materialLogFactor = fun y : ℝ => Real.log (Real.exp 1 + y) := by
      funext y
      rw [materialLogFactor]
    rw [hfun]
    simpa only [one_div] using
      (((hasDerivAt_id' x).const_add (Real.exp 1)).log
        (add_pos_of_pos_of_nonneg (Real.exp_pos 1) hx).ne')
  have hl2 : HasDerivAt (fun t : ℝ => materialLogFactor t ^ 2)
      (2 * materialLogFactor x * (Real.exp 1 + x)⁻¹) x := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hl.fun_pow 2
  exact (hp.mul hl2).const_add 1

private theorem materialMExponent_derivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x →
      |deriv materialMExponent x| ≤ C * materialE0Exponent x := by
  let c : ℝ := Real.exp 1 + 1
  let C : ℝ := (5 / 2 : ℝ) * c ^ 2 + 2
  have hc : 1 ≤ c := by dsimp only [c]; linarith only [Real.exp_pos 1]
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun x hx => ?_⟩
  have hxpow := Real.rpow_nonneg hx (3 / 2 : ℝ)
  have hxpow' := Real.rpow_nonneg hx (5 / 2 : ℝ)
  have hl : 1 ≤ materialLogFactor x := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (le_add_of_nonneg_right hx : Real.exp 1 ≤ Real.exp 1 + x)
    simpa only [Real.log_exp, materialLogFactor] using h
  have hl0 : 0 ≤ materialLogFactor x := zero_le_one.trans hl
  have he : 1 ≤ materialE0Exponent x := materialE0Exponent_one_le hx
  have hexp : 1 ≤ Real.exp 1 + x :=
    (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans
      (le_add_of_nonneg_right hx)
  have hlog := Real.log_le_sub_one_of_pos
    (add_pos_of_pos_of_nonneg (Real.exp_pos 1) hx)
  change materialLogFactor x ≤ Real.exp 1 + x - 1 at hlog
  have hterm : x ^ (3 / 2 : ℝ) * materialLogFactor x ^ 2 ≤
      c ^ 2 * materialE0Exponent x := by
    by_cases hx1 : x ≤ 1
    · have hp : x ^ (3 / 2 : ℝ) ≤ 1 := by
        simpa only [Real.one_rpow] using
          Real.rpow_le_rpow hx hx1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
      have hlc : materialLogFactor x ≤ c := by
        dsimp only [c]
        linarith only [hlog, hx1]
      have hs : materialLogFactor x ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hl0 hlc 2
      have hb := mul_le_mul hp hs (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have hb' : x ^ (3 / 2 : ℝ) * materialLogFactor x ^ 2 ≤ c ^ 2 := by
        simpa only [one_mul] using hb
      exact hb'.trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he (sq_nonneg c))
    · have hx1' : 1 ≤ x := le_of_not_ge hx1
      have hxc : materialLogFactor x ≤ c * x := by
        have hm := mul_le_mul_of_nonneg_left hx1' (Real.exp_pos 1).le
        dsimp only [c]
        nlinarith only [hlog, hm]
      have hp : x ^ (3 / 2 : ℝ) * x = x ^ (5 / 2 : ℝ) := by
        rw [← Real.rpow_add_one (zero_lt_one.trans_le hx1').ne']
        norm_num
      have hc2 : c ≤ c ^ 2 := by nlinarith only [hc, sq_nonneg (c - 1)]
      calc
        _ = (x ^ (3 / 2 : ℝ) * materialLogFactor x) * materialLogFactor x := by ring
        _ ≤ (x ^ (3 / 2 : ℝ) * materialLogFactor x) * (c * x) :=
          mul_le_mul_of_nonneg_left hxc (mul_nonneg hxpow hl0)
        _ = c * (x ^ (5 / 2 : ℝ) * materialLogFactor x) := by rw [← hp]; ring
        _ ≤ c ^ 2 * (x ^ (5 / 2 : ℝ) * materialLogFactor x) :=
          mul_le_mul_of_nonneg_right hc2 (mul_nonneg hxpow' hl0)
        _ ≤ c ^ 2 * materialE0Exponent x :=
          mul_le_mul_of_nonneg_left (by
            change x ^ (5 / 2 : ℝ) * materialLogFactor x ≤
              1 + x ^ (5 / 2 : ℝ) * materialLogFactor x
            linarith) (sq_nonneg c)
  have hinv : (Real.exp 1 + x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hexp
  have hsecond : x ^ (5 / 2 : ℝ) *
      (2 * materialLogFactor x * (Real.exp 1 + x)⁻¹) ≤ 2 * materialE0Exponent x := by
    have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hl0)) hxpow'
    dsimp only [materialE0Exponent]
    nlinarith only [hm]
  have hnonneg : 0 ≤
      (5 / 2 : ℝ) * x ^ (3 / 2 : ℝ) * materialLogFactor x ^ 2 +
        x ^ (5 / 2 : ℝ) *
          (2 * materialLogFactor x * (Real.exp 1 + x)⁻¹) := by
    positivity
  rw [(materialMExponent_hasDerivAt hx).deriv, abs_of_nonneg hnonneg]
  have hfirst := mul_le_mul_of_nonneg_left hterm
    (by norm_num : (0 : ℝ) ≤ 5 / 2)
  dsimp only [C]
  nlinarith only [hfirst, hsecond]

private theorem materialMExponent_bounded_shift {L : ℝ} (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |x - y| ≤ L →
      |materialMExponent x - materialMExponent y| ≤ B * materialE0Exponent y := by
  obtain ⟨C, hC, hderiv⟩ := materialMExponent_derivative_bound
  obtain ⟨K, P, hK, hP, hshift⟩ :=
    materialE0_rpow_oneSided_shift (R := (1 : ℝ)) zero_le_one hL
  let A := |Real.log K| + P
  have hA : 0 ≤ A := add_nonneg (abs_nonneg _) hP
  have hcompare (t y : ℝ) (ht : 0 ≤ t) (hy : 0 ≤ y) (hty : t ≤ y + L) :
      materialE0Exponent t ≤ A * materialE0Exponent y := by
    have hb : materialE0 t ≤ K * materialE0 y ^ P := by
      simpa only [Real.rpow_one] using hshift t y ht hy hty
    have hg := Real.log_le_log (materialE0_pos t) hb
    rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos (materialE0_pos y) P).ne',
      Real.log_rpow (materialE0_pos y)] at hg
    have hg' : materialE0Exponent t ≤ Real.log K + P * materialE0Exponent y := by
      simpa only [materialE0, Real.log_exp] using hg
    have hh := mul_le_mul_of_nonneg_left (materialE0Exponent_one_le hy)
      (abs_nonneg (Real.log K))
    dsimp only [A]
    nlinarith only [hg', hh, le_abs_self (Real.log K)]
  refine ⟨C * A * L, mul_nonneg (mul_nonneg hC.le hA) hL, fun x y hx hy hxy => ?_⟩
  have hmax : max x y ≤ y + L := max_le
    (by linarith only [(abs_le.mp hxy).2]) (le_add_of_nonneg_right hL)
  have hzero : 0 ≤ min x y := le_min hx hy
  have hfd (t : ℝ) (ht : t ∈ Icc (min x y) (max x y)) :
      DifferentiableAt ℝ materialMExponent t :=
    (materialMExponent_hasDerivAt (hzero.trans ht.1)).differentiableAt
  have hbound (t : ℝ) (ht : t ∈ Icc (min x y) (max x y)) :
      ‖deriv materialMExponent t‖ ≤ C * A * materialE0Exponent y := by
    rw [Real.norm_eq_abs]
    exact (hderiv t (hzero.trans ht.1)).trans
      ((mul_le_mul_of_nonneg_left
        (hcompare t y (hzero.trans ht.1) hy (ht.2.trans hmax)) hC.le).trans_eq
          (by ring))
  have hmvt := (convex_Icc (min x y) (max x y)).norm_image_sub_le_of_norm_deriv_le
    hfd hbound (show y ∈ Icc (min x y) (max x y) from ⟨min_le_right _ _, le_max_right _ _⟩)
    (show x ∈ Icc (min x y) (max x y) from ⟨min_le_left _ _, le_max_left _ _⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hnonneg : 0 ≤ C * A * materialE0Exponent y :=
    mul_nonneg (mul_nonneg hC.le hA) (zero_le_one.trans (materialE0Exponent_one_le hy))
  exact hmvt.trans ((mul_le_mul_of_nonneg_left hxy hnonneg).trans_eq (by ring))

/-- A bounded displacement preserves the specified real power of the
actual model `M`. All loss is paid by a fixed power of `E0`. -/
theorem materialM_rpow_bounded_shift_E0
    (γ : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |x - y| ≤ L →
      materialM x ^ γ ≤ materialM y ^ γ * materialE0 y ^ A := by
  obtain ⟨B, hB, hb⟩ := materialMExponent_bounded_shift hL
  refine ⟨|γ| * B, mul_nonneg (abs_nonneg _) hB, fun x y hx hy hxy => ?_⟩
  have hm := mul_le_mul_of_nonneg_left (hb x y hx hy hxy) (abs_nonneg γ)
  have habs : γ * (materialMExponent x - materialMExponent y) ≤
      |γ| * |materialMExponent x - materialMExponent y| := by
    simpa only [abs_mul] using
      le_abs_self (γ * (materialMExponent x - materialMExponent y))
  have h := habs.trans hm
  simp only [materialM, materialE0, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
  nlinarith only [h]

end ContinuousFlexibility.Analysis
