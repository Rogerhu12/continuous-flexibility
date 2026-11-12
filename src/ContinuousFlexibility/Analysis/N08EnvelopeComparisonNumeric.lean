import ContinuousFlexibility.Analysis.MaterialWeights

/-!
# An endpoint height comparison controls the slower envelope

The cubic exponent of the height weight bounds the endpoint coordinate
linearly. The logarithmic envelope then changes by only a fixed power.
The constants are uniform in both endpoint coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

private theorem n08_logFactor_one_le {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ materialLogFactor x := by
  have h := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hx)
  simpa only [materialLogFactor, Real.log_exp] using h

private theorem n08_materialMExponent_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    materialMExponent x ≤ materialMExponent y := by
  have hlog : materialLogFactor x ≤ materialLogFactor y :=
    Real.log_le_log (add_pos_of_pos_of_nonneg (Real.exp_pos 1) hx)
      (add_le_add_right hxy _)
  have hxlog : 0 ≤ materialLogFactor x := zero_le_one.trans (n08_logFactor_one_le hx)
  change 1 + x ^ (5 / 2 : ℝ) * materialLogFactor x ^ 2 ≤
    1 + y ^ (5 / 2 : ℝ) * materialLogFactor y ^ 2
  apply add_le_add le_rfl
  exact mul_le_mul (Real.rpow_le_rpow hx hxy (by norm_num : (0 : ℝ) ≤ 5 / 2))
    (pow_le_pow_left₀ hxlog hlog 2) (sq_nonneg _)
    (Real.rpow_nonneg (hx.trans hxy) _)

theorem n08_materialMExponent_affine_bound {K : ℝ} (hK : 1 ≤ K) :
    ∃ A : ℝ, 0 < A ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y ≤ K * (1 + x) →
      materialMExponent y ≤ A * materialMExponent x := by
  let L : ℝ := 2 * K
  let B : ℝ := L ^ (5 / 2 : ℝ) * (Real.log L + 1) ^ 2
  let A : ℝ := 1 + materialMExponent L + B
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hB : 0 ≤ B := mul_nonneg (Real.rpow_nonneg hLp.le _) (sq_nonneg _)
  have hML : 1 ≤ materialMExponent L := by
    exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hLp.le _) (sq_nonneg _))
  have hA : 0 < A := by dsimp only [A]; linarith
  have hAone : 1 ≤ A := by dsimp only [A]; linarith
  refine ⟨A, hA, fun x y hx hy hxy => ?_⟩
  have hMx : 1 ≤ materialMExponent x :=
    le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hx _) (sq_nonneg _))
  by_cases hx1 : 1 ≤ x
  · have hyL : y ≤ L * x := by
      dsimp only [L]
      nlinarith [mul_nonneg (zero_le_one.trans hK) (sub_nonneg.mpr hx1)]
    have hpow : y ^ (5 / 2 : ℝ) ≤ L ^ (5 / 2 : ℝ) * x ^ (5 / 2 : ℝ) := by
      rw [← Real.mul_rpow hLp.le hx]
      exact Real.rpow_le_rpow hy hyL (by norm_num)
    have hlog0 : 0 ≤ materialLogFactor y := zero_le_one.trans (n08_logFactor_one_le hy)
    have hlog : materialLogFactor y ≤ (Real.log L + 1) * materialLogFactor x := by
      have hexp : Real.exp 1 + y ≤ L * (Real.exp 1 + x) := by
        nlinarith only [hyL, mul_nonneg (sub_nonneg.mpr hL) (Real.exp_pos 1).le]
      have hl := Real.log_le_log (add_pos_of_pos_of_nonneg (Real.exp_pos 1) hy) hexp
      rw [Real.log_mul hLp.ne' (add_pos_of_pos_of_nonneg (Real.exp_pos 1) hx).ne'] at hl
      change materialLogFactor y ≤ Real.log L + materialLogFactor x at hl
      nlinarith only [hl, mul_nonneg (Real.log_nonneg hL)
        (sub_nonneg.mpr (n08_logFactor_one_le hx))]
    have hterm : y ^ (5 / 2 : ℝ) * materialLogFactor y ^ 2 ≤
        B * (x ^ (5 / 2 : ℝ) * materialLogFactor x ^ 2) := by
      calc
        _ ≤ (L ^ (5 / 2 : ℝ) * x ^ (5 / 2 : ℝ)) *
            ((Real.log L + 1) * materialLogFactor x) ^ 2 :=
          mul_le_mul hpow (pow_le_pow_left₀ hlog0 hlog 2) (sq_nonneg _)
            (mul_nonneg (Real.rpow_nonneg hLp.le _) (Real.rpow_nonneg hx _))
        _ = _ := by dsimp only [B]; ring
    have hBA : B ≤ A := by dsimp only [A]; linarith
    have hAA : 1 + B * (materialMExponent x - 1) ≤ A * materialMExponent x := by
      nlinarith only [hBA, hMx, hAone, hB,
        mul_nonneg (sub_nonneg.mpr hBA) (sub_nonneg.mpr hMx)]
    apply le_trans _ hAA
    change 1 + y ^ (5 / 2 : ℝ) * materialLogFactor y ^ 2 ≤ _
    dsimp only [materialMExponent]
    linarith only [hterm]
  · have hyL : y ≤ L := by
      dsimp only [L]
      nlinarith [mul_nonneg (zero_le_one.trans hK) (sub_nonneg.mpr (le_of_not_ge hx1))]
    have hyM := n08_materialMExponent_mono hy hyL
    have hMA : materialMExponent L ≤ A := by dsimp only [A]; linarith
    have hAM : A ≤ A * materialMExponent x := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hMx hA.le
    exact (hyM.trans hMA).trans hAM

theorem n08_endpoint_height_envelope_comparison {a b C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) :
    ∃ N : ℝ, 0 < N ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      materialH x ^ a ≤ C * materialH y ^ b → materialM y ≤ materialM x ^ N := by
  let A : ℝ := a / b
  let B : ℝ := 3 * |Real.log C| / (2 * b)
  let K : ℝ := 1 + A + B
  have hA : 0 ≤ A := (div_pos ha hb).le
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (by positivity)
  have hK : 1 ≤ K := by dsimp only [K]; linarith
  obtain ⟨N, hN, henv⟩ := n08_materialMExponent_affine_bound hK
  refine ⟨N, hN, fun x y hx hy hc => ?_⟩
  have hl := Real.log_le_log (Real.rpow_pos_of_pos (materialH_pos x) a) hc
  rw [Real.log_rpow (materialH_pos x),
    Real.log_mul hC.ne' (Real.rpow_pos_of_pos (materialH_pos y) b).ne',
    Real.log_rpow (materialH_pos y), materialH, materialH, Real.log_exp, Real.log_exp] at hl
  have hy3 : y ^ 3 ≤ A * x ^ 3 + B := by
    have heq : A * x ^ 3 + B = (2 * a * x ^ 3 + 3 * |Real.log C|) / (2 * b) := by
      dsimp only [A, B]
      field_simp
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < 2 * b)).mpr
    nlinarith only [hl, le_abs_self (Real.log C)]
  have hAK : A ≤ K := by dsimp only [K]; linarith
  have hBK : B ≤ K := by dsimp only [K]; linarith
  have hcube : y ^ 3 ≤ (K * (1 + x)) ^ 3 := by
    have hs : 1 + x ^ 3 ≤ (1 + x) ^ 3 := by nlinarith [sq_nonneg x]
    have hk3 : K ≤ K ^ 3 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hK) (sq_nonneg K),
        mul_nonneg (sub_nonneg.mpr hK) (zero_le_one.trans hK)]
    calc
      y ^ 3 ≤ A * x ^ 3 + B := hy3
      _ ≤ K * x ^ 3 + K := add_le_add
        (mul_le_mul_of_nonneg_right hAK (pow_nonneg hx 3)) hBK
      _ = K * (1 + x ^ 3) := by ring
      _ ≤ K * (1 + x) ^ 3 := mul_le_mul_of_nonneg_left hs (zero_le_one.trans hK)
      _ ≤ K ^ 3 * (1 + x) ^ 3 := mul_le_mul_of_nonneg_right hk3 (by positivity)
      _ = _ := (mul_pow _ _ _).symm
  have hyK : y ≤ K * (1 + x) :=
    le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity) hcube
  change Real.exp (materialMExponent y) ≤ (Real.exp (materialMExponent x)) ^ N
  rw [← Real.exp_mul]
  exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using henv x y hx hy hyK)

end ContinuousFlexibility.Analysis
