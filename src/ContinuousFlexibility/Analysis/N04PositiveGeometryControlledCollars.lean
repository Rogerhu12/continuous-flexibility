import ContinuousFlexibility.Analysis.EndpointFiberPolynomialMargins
import ContinuousFlexibility.Analysis.EndpointAngularInterpolation
import ContinuousFlexibility.Analysis.OneSidedEndpointHeight

/-!
# Polynomial costs of the actual positive-component collars

The widths here are the stored angular, integral-fiber and height widths.
An actual inverse-fiber envelope `Mσ ≤ Cσ * M ^ degree` is converted to
one common fixed power for all three reciprocal widths and the displayed
Jacobian lower bound. The constants precede every radius and field datum.
No bound for a future global transport is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

private theorem positive_core_reciprocal_bounds {l r c d U : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r) (hU : 1 ≤ U)
    (hleft : (c - l)⁻¹ ≤ U) (hright : (r - d)⁻¹ ≤ U) :
    (r - l)⁻¹ ≤ U ∧ (min (c - l) (r - d))⁻¹ ≤ U ∧
      (min ((r - l) / 4) (min (c - l) (r - d)))⁻¹ ≤ 4 * U := by
  have hspan : 0 < r - l := sub_pos.mpr (hlc.trans (hcd.trans hdr))
  have hs : (r - l)⁻¹ ≤ U :=
    ((inv_le_inv₀ hspan (sub_pos.mpr hlc)).mpr
      (sub_le_sub_right (hcd.trans hdr).le l)).trans hleft
  have hm : (min (c - l) (r - d))⁻¹ ≤ U := by
    rcases le_total (c - l) (r - d) with h | h
    · simpa only [min_eq_left h] using hleft
    · simpa only [min_eq_right h] using hright
  refine ⟨hs, hm, ?_⟩
  rcases le_total ((r - l) / 4) (min (c - l) (r - d)) with h | h
  · rw [min_eq_left h, inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hs (by norm_num)
  · rw [min_eq_right h]
    exact hm.trans (by linarith only [hU])

theorem n04PositiveGeometry_endpointAngularWidth_polynomial_inv_le (n : ℕ) {l r c d κ M U : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκ : 0 < κ) (hM : 0 ≤ M) (hU : 1 ≤ U)
    (hMU : M ≤ U) (hκU : κ⁻¹ ≤ U)
    (hleft : (c - l)⁻¹ ≤ U) (hright : (r - d)⁻¹ ≤ U) :
    (endpointAngularWidth n l r c d κ M)⁻¹ ≤
      (16 + 8 * ((n + 1 : ℕ) : ℝ)) * U ^ 2 := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let ρ : ℝ := min (c - l) (r - d)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hspan : 0 < r - l := sub_pos.mpr (hlc.trans (hcd.trans hdr))
  have hρ : 0 < ρ := lt_min (sub_pos.mpr hlc) (sub_pos.mpr hdr)
  have hcost := positive_core_reciprocal_bounds hlc hcd hdr hU hleft hright
  have hU2 : U ≤ U ^ 2 := by
    simpa only [pow_one] using pow_le_pow_right₀ hU (by decide : 1 ≤ 2)
  have hMone : M + 1 ≤ 2 * U := by linarith only [hMU, hU]
  have hjet : (4 * N * (M + 1)) / κ ≤ 8 * N * U ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (4 * N * (2 * U)) * U :=
        mul_le_mul (mul_le_mul_of_nonneg_left hMone (by positivity)) hκU
          (inv_nonneg.mpr hκ.le) (by positivity)
      _ = _ := by ring
  have hspanTerm : 4 / (r - l) ≤ 4 * U ^ 2 := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hcost.1.trans hU2) (by norm_num)
  have hρTerm : 2 / ρ ≤ 2 * U ^ 2 := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hcost.2.1.trans hU2) (by norm_num)
  have hconst : (10 : ℝ) ≤ 10 * U ^ 2 := by
    nlinarith only [hU.trans hU2]
  have hraw := prescribedEndpointWidth_inv_le n (Mslope := 0) (m := 1)
    hspan hρ hκ hM (by norm_num) zero_lt_one
  have hraw' : (endpointAngularWidth n l r c d κ M)⁻¹ ≤
      2 + 4 / (r - l) + 2 / ρ + (4 * N * (M + 1)) / κ + 8 := by
    simpa only [endpointAngularWidth, zero_add, mul_one, div_one] using hraw
  change (endpointAngularWidth n l r c d κ M)⁻¹ ≤ (16 + 8 * N) * U ^ 2
  nlinarith only [hraw', hjet, hspanTerm, hρTerm, hconst]

theorem n04PositiveGeometry_oneSidedEndpointHeightWidth_polynomial_inv_le (n : ℕ)
    {l r c d Clog H U : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hClog : 0 ≤ Clog) (hH : 1 ≤ H) (hU : 1 ≤ U) (hHU : H ≤ U)
    (hleft : (c - l)⁻¹ ≤ U) (hright : (r - d)⁻¹ ≤ U) :
    (oneSidedEndpointHeightWidth n
      (min ((r - l) / 4) (min (c - l) (r - d))) (Clog * H ^ (2 * n + 1)))⁻¹ ≤
        (5 + ((n + 1 : ℕ) : ℝ) * (Clog + 1)) * U ^ (2 * n + 1) := by
  have hρ := (positive_core_reciprocal_bounds hlc hcd hdr hU hleft hright).2.2
  have hUp : U ≤ U ^ (2 * n + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hU (by omega : 1 ≤ 2 * n + 1)
  have hOne : 1 ≤ U ^ (2 * n + 1) := one_le_pow₀ hU
  have hlog : Clog * H ^ (2 * n + 1) ≤ Clog * U ^ (2 * n + 1) :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans hH) hHU _) hClog
  have hsum : Clog * H ^ (2 * n + 1) + 1 ≤ (Clog + 1) * U ^ (2 * n + 1) := by
    nlinarith only [hlog, hOne]
  have hN : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hsum hN
  rw [oneSidedEndpointHeightWidth, inv_inv]
  nlinarith only [hρ, hUp, hOne, hscaled]

/-- The same inverse envelope supplied by the actual transport factory
controls every displayed collar. The coefficient and exponent are fixed
before the component radii, state family and numerical input envelope. -/
theorem n04PositiveGeometry_exists_wholePositiveCollar_polynomial_envelope
    (n degree : ℕ) (Cσ Clog : ℝ) (hCσ : 1 ≤ Cσ) (hClog : 0 ≤ Clog) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ outDegree : ℕ,
    ∀ {l r c d κφ κX M Mσ H U : ℝ},
      l < c → c < d → d < r → 0 < κφ → 0 < κX →
      1 ≤ M → 1 ≤ Mσ → 1 ≤ H → 1 ≤ U → M ≤ U → H ≤ U →
      Mσ ≤ Cσ * M ^ degree → κφ⁻¹ ≤ U → κX⁻¹ ≤ U →
      (c - l)⁻¹ ≤ U → (r - d)⁻¹ ≤ U →
      (endpointAngularWidth (n + 1) l r c d κφ M)⁻¹ ≤ A * U ^ outDegree ∧
      (∀ side, (endpointFiberWidths n l r c d κX Mσ side)⁻¹ ≤ A * U ^ outDegree) ∧
      0 < endpointFiberLower n l r c d κX Mσ * (κφ / 2) ∧
      (endpointFiberLower n l r c d κX Mσ * (κφ / 2))⁻¹ ≤ A * U ^ outDegree ∧
      (oneSidedEndpointHeightWidth n
        (min ((r - l) / 4) (min (c - l) (r - d))) (Clog * H ^ (2 * n + 1)))⁻¹ ≤
        A * U ^ outDegree := by
  let Aa : ℝ := 16 + 8 * ((n + 2 : ℕ) : ℝ)
  let Af : ℝ := (24 + 16 * ((n + 1 : ℕ) : ℝ)) * Cσ ^ 2
  let Ah : ℝ := 5 + ((n + 1 : ℕ) : ℝ) * (Clog + 1)
  let A : ℝ := max 1 (max Aa (max Af (max Ah 8)))
  let outDegree : ℕ := max (2 * (degree + 1)) (2 * n + 1)
  have hA : 1 ≤ A := le_max_left _ _
  have hAa : Aa ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hAf : Af ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAh : Ah ≤ A := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hA8 : (8 : ℝ) ≤ A := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have htwo : 2 ≤ outDegree :=
    (by omega : 2 ≤ 2 * (degree + 1)).trans (Nat.le_max_left _ _)
  refine ⟨A, hA, outDegree, ?_⟩
  intro l r c d κφ κX M Mσ H U hlc hcd hdr hκφ hκX hM hMσ hH hU
    hMU hHU hcost hφU hXU hleft hright
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have lift_bound {B X : ℝ} {k : ℕ}
      (hx : X ≤ B * U ^ k) (hBA : B ≤ A) (hk : k ≤ outDegree) :
      X ≤ A * U ^ outDegree :=
    hx.trans (mul_le_mul hBA (pow_le_pow_right₀ hU hk)
      (pow_nonneg hU0 _) (zero_le_one.trans hA))
  have hang := n04PositiveGeometry_endpointAngularWidth_polynomial_inv_le (n + 1) hlc hcd hdr hκφ
    (zero_le_one.trans hM) hU hMU hφU hleft hright
  change (endpointAngularWidth (n + 1) l r c d κφ M)⁻¹ ≤ Aa * U ^ 2 at hang
  let W : ℝ := Cσ * U ^ (degree + 1)
  have hUW : U ≤ W := calc
    U ≤ 1 * U ^ (degree + 1) := by
      simpa only [one_mul, pow_one] using
        pow_le_pow_right₀ hU (by omega : 1 ≤ degree + 1)
    _ ≤ W := mul_le_mul_of_nonneg_right hCσ (pow_nonneg hU0 _)
  have hσW : Mσ ≤ W := calc
    Mσ ≤ Cσ * M ^ degree := hcost
    _ ≤ Cσ * U ^ degree := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans hM) hMU _) (zero_le_one.trans hCσ)
    _ ≤ W := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU (Nat.le_succ degree))
      (zero_le_one.trans hCσ)
  have hfiber (side : Bool) : (endpointFiberWidths n l r c d κX Mσ side)⁻¹ ≤
      Af * U ^ (2 * (degree + 1)) := by
    have hb := endpointFiberWidths_polynomial_inv_le n hlc hdr hκX
      (zero_le_one.trans hMσ) (hU.trans hUW) hσW (hXU.trans hUW)
      (hleft.trans hUW) (hright.trans hUW) side
    calc
      _ ≤ (24 + 16 * ((n + 1 : ℕ) : ℝ)) * W ^ 2 := hb
      _ = Af * (U ^ (degree + 1)) ^ 2 := by dsimp only [W, Af]; ring
      _ = Af * U ^ (2 * (degree + 1)) := by
        rw [← pow_mul, Nat.mul_comm (degree + 1) 2]
  have hJ := endpointFiberJacobianLower_polynomial_inv_le n hlc hdr hκφ hκX
    (zero_le_one.trans hMσ) hU hφU hXU
  have hheight := n04PositiveGeometry_oneSidedEndpointHeightWidth_polynomial_inv_le n hlc hcd hdr
    hClog hH hU hHU hleft hright
  refine ⟨lift_bound hang hAa htwo,
    (fun side => lift_bound (hfiber side) hAf (Nat.le_max_left _ _)),
    hJ.1, lift_bound hJ.2 hA8 htwo, ?_⟩
  exact lift_bound hheight hAh (Nat.le_max_right _ _)

end ContinuousFlexibility.Analysis
