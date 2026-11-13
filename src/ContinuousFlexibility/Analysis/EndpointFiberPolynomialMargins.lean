import ContinuousFlexibility.Analysis.EndpointFiberInterpolation
import ContinuousFlexibility.Analysis.PositiveReferenceIdentity

/-!
# Explicit reciprocal costs of the actual fiber collars

The finite minimum defining each collar has a polynomial reciprocal
bound. The same actual integral interpolation has a radial lower bound
independent of its higher-jet envelope. Together these control the
displayed determinant lower bound without an uncontrolled small width.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

private theorem reciprocal_min_le_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (min a b)⁻¹ ≤ a⁻¹ + b⁻¹ := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hb.le)
  · rw [min_eq_right h]
    exact le_add_of_nonneg_left (inv_nonneg.mpr ha.le)

private theorem reciprocal_min_five_le {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    (min a (min b (min c (min d e))))⁻¹ ≤ a⁻¹ + b⁻¹ + c⁻¹ + d⁻¹ + e⁻¹ := by
  have h₁ := reciprocal_min_le_add ha (lt_min hb (lt_min hc (lt_min hd he)))
  have h₂ := reciprocal_min_le_add hb (lt_min hc (lt_min hd he))
  have h₃ := reciprocal_min_le_add hc (lt_min hd he)
  have h₄ := reciprocal_min_le_add hd he
  linarith only [h₁, h₂, h₃, h₄]

theorem prescribedEndpointWidth_inv_le (n : ℕ) {span ρ κ M Mslope m : ℝ}
    (hspan : 0 < span) (hρ : 0 < ρ) (hκ : 0 < κ)
    (hM : 0 ≤ M) (hMslope : 0 ≤ Mslope) (hm : 0 < m) :
    (prescribedEndpointWidth n span ρ κ M Mslope m)⁻¹ ≤
      2 + 4 / span + 2 / ρ +
        (4 * ((n + 1 : ℕ) : ℝ) * (M + 1)) / κ + 8 * (Mslope + 1) / m := by
  have hN : 0 < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hd : 0 < 4 * ((n + 1 : ℕ) : ℝ) * (M + 1) := by positivity
  have he : 0 < 8 * (Mslope + 1) := by positivity
  have h := reciprocal_min_five_le
    (by norm_num : (0 : ℝ) < 1 / 2)
    (div_pos hspan (by norm_num : (0 : ℝ) < 4))
    (div_pos hρ (by norm_num : (0 : ℝ) < 2)) (div_pos hκ hd) (div_pos hm he)
  simpa only [prescribedEndpointWidth, inv_div, div_one] using h

/-- A common upper bound for forward jets and reciprocal slopes and gaps
pays only degree two in the actual prescribed collar reciprocal. -/
theorem prescribedEndpointWidth_fiber_polynomial_inv_le (n : ℕ)
    {span κ M U : ℝ} (hspan : 0 < span) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hU : 1 ≤ U) (hMU : M ≤ U) (hκU : κ⁻¹ ≤ U) (hspanU : span⁻¹ ≤ U) :
    (prescribedEndpointWidth n span 1 κ M
      (max (M + ((n + 1 : ℕ) : ℝ) * M) 1) span)⁻¹ ≤
        (24 + 16 * ((n + 1 : ℕ) : ℝ)) * U ^ 2 := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let L : ℝ := max (M + N * M) 1
  have hN : 1 ≤ N := by
    show (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.le_add_left 1 n
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hU2 : U ≤ U ^ 2 := by nlinarith only [hU, sq_nonneg (U - 1)]
  have hM1 : M + 1 ≤ 2 * U := by linarith only [hMU, hU]
  have hL : L ≤ (N + 1) * U := by
    apply max_le
    · have h := mul_le_mul_of_nonneg_left hMU (show 0 ≤ N + 1 by linarith)
      nlinarith only [h]
    · exact one_le_mul_of_one_le_of_one_le (by linarith only [hN]) hU
  have hL1 : L + 1 ≤ (N + 2) * U := by nlinarith only [hL, hU]
  have hjet : (4 * N * (M + 1)) / κ ≤ 8 * N * U ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (4 * N * (2 * U)) * U :=
        mul_le_mul (mul_le_mul_of_nonneg_left hM1 (by positivity)) hκU
          (inv_nonneg.mpr hκ.le) (by positivity)
      _ = _ := by ring
  have hmass : 8 * (L + 1) / span ≤ 8 * (N + 2) * U ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (8 * ((N + 2) * U)) * U :=
        mul_le_mul (mul_le_mul_of_nonneg_left hL1 (by norm_num)) hspanU
          (inv_nonneg.mpr hspan.le) (by positivity)
      _ = _ := by ring
  have hgap : 4 / span ≤ 4 * U ^ 2 := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hspanU.trans hU2) (by norm_num)
  have hconst : (4 : ℝ) ≤ 4 * U ^ 2 :=
    by nlinarith only [hU.trans hU2]
  have hraw := prescribedEndpointWidth_inv_le n hspan zero_lt_one hκ hM
    (zero_le_one.trans (le_max_right (M + N * M) 1)) hspan
  change (prescribedEndpointWidth n span 1 κ M L span)⁻¹ ≤
    (24 + 16 * N) * U ^ 2
  have hraw' : (prescribedEndpointWidth n span 1 κ M L span)⁻¹ ≤
      4 + 4 / span + (4 * N * (M + 1)) / κ + 8 * (L + 1) / span := by
    calc
      _ ≤ 2 + 4 / span + 2 / 1 + (4 * N * (M + 1)) / κ +
          8 * (L + 1) / span := hraw
      _ = _ := by ring
  nlinarith only [hraw', hjet, hmass, hgap, hconst]

theorem endpointFiberWidths_polynomial_inv_le (n : ℕ) {l r c d κ M U : ℝ}
    (hlc : l < c) (hdr : d < r) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hU : 1 ≤ U) (hMU : M ≤ U) (hκU : κ⁻¹ ≤ U)
    (hleft : (c - l)⁻¹ ≤ U) (hright : (r - d)⁻¹ ≤ U) (side : Bool) :
    (endpointFiberWidths n l r c d κ M side)⁻¹ ≤
      (24 + 16 * ((n + 1 : ℕ) : ℝ)) * U ^ 2 := by
  cases side
  · exact prescribedEndpointWidth_fiber_polynomial_inv_le n
      (sub_pos.mpr hlc) hκ hM hU hMU hκU hleft
  · exact prescribedEndpointWidth_fiber_polynomial_inv_le n
      (sub_pos.mpr hdr) hκ hM hU hMU hκU hright

/-- The actual interpolated radial slope has this lower bound even when
the endpoint-jet envelope is large. -/
theorem endpointFiberLower_ge_reference (n : ℕ) {l r c d κ M : ℝ}
    (hlc : l < c) (hdr : d < r) (hκ : 0 < κ) (hM : 0 ≤ M) :
    min (κ / 2) (1 / 2) ≤ endpointFiberLower n l r c d κ M := by
  have hL := prescribedEndpointWidth_margins n (sub_pos.mpr hlc) zero_lt_one hκ hM
    (zero_le_one.trans (le_max_right (M + ((n + 1 : ℕ) : ℝ) * M) 1)) (sub_pos.mpr hlc)
  have hR := prescribedEndpointWidth_margins n (sub_pos.mpr hdr) zero_lt_one hκ hM
    (zero_le_one.trans (le_max_right (M + ((n + 1 : ℕ) : ℝ) * M) 1)) (sub_pos.mpr hdr)
  have hleft := prescribedPositiveCollarLower_reference_lower (κ := κ) hL.1 hL.2.2.2.1
  have hright := prescribedPositiveCollarLower_reference_lower (κ := κ) hR.1 hR.2.2.2.1
  exact le_min hleft (le_min
    ((min_le_right _ _).trans (by norm_num : (1 / 2 : ℝ) ≤ 1)) hright)

/-- Inverting the displayed positive determinant lower bound costs one
fixed quadratic power of the reciprocal endpoint slopes. -/
theorem endpointFiberJacobianLower_polynomial_inv_le (n : ℕ)
    {l r c d κφ κX M U : ℝ} (hlc : l < c) (hdr : d < r)
    (hκφ : 0 < κφ) (hκX : 0 < κX) (hM : 0 ≤ M)
    (hU : 1 ≤ U) (hφU : κφ⁻¹ ≤ U) (hXU : κX⁻¹ ≤ U) :
    0 < endpointFiberLower n l r c d κX M * (κφ / 2) ∧
      (endpointFiberLower n l r c d κX M * (κφ / 2))⁻¹ ≤ 8 * U ^ 2 := by
  let k : ℝ := min (κX / 2) (1 / 2)
  let B : ℝ := endpointFiberLower n l r c d κX M
  have hk : 0 < k := lt_min (half_pos hκX) (by norm_num)
  have hkB : k ≤ B := endpointFiberLower_ge_reference n hlc hdr hκX hM
  have hB : 0 < B := hk.trans_le hkB
  have hBinv : B⁻¹ ≤ k⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hk hkB
  have hkinv : k⁻¹ ≤ 4 * U := by
    have h := reciprocal_min_le_add (half_pos hκX) (by norm_num : (0 : ℝ) < 1 / 2)
    have h' : k⁻¹ ≤ 2 * κX⁻¹ + 2 := by
      calc
        k⁻¹ ≤ (κX / 2)⁻¹ + (1 / 2)⁻¹ := h
        _ = 2 * κX⁻¹ + 2 := by rw [inv_div, inv_div, div_one, div_eq_mul_inv]
    linarith only [h', hXU, hU]
  have hφinv : (κφ / 2)⁻¹ ≤ 2 * U := by
    rw [inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hφU (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨mul_pos hB (half_pos hκφ), ?_⟩
  change (B * (κφ / 2))⁻¹ ≤ 8 * U ^ 2
  rw [mul_inv_rev]
  calc
    _ ≤ (2 * U) * (4 * U) :=
      mul_le_mul hφinv (hBinv.trans hkinv) (inv_nonneg.mpr hB.le)
        (mul_nonneg (by norm_num) (zero_le_one.trans hU))
    _ = _ := by ring

end ContinuousFlexibility.Analysis
