import ContinuousFlexibility.Analysis.MaterialRhoGrowth
import ContinuousFlexibility.Radial.MorseChainScales

/-!
# Quantitative size of a complete radial plateau

The actual cell bounds control the inverse collar width. The supplied
material coordinate has only cubic endpoint growth, so the full plateau
also has a radial material support bounded by a fixed radial weight.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis (endpointX)

set_option backward.isDefEq.respectTransparency false

theorem natCast_le_radialQ (n : ℕ) : (n : ℝ) ≤ radialQ n := by
  by_cases hn : n = 0
  · subst n
    norm_num [radialQ]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact (by nlinarith only [hn1] : (n : ℝ) ≤ (n : ℝ) ^ 2).trans
      (Radial.radial_nat_sq_le_Q n)

theorem natCast_add_one_le_radialE (n : ℕ) : (n : ℝ) + 1 ≤ radialE n :=
  (Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr (natCast_le_radialQ n))

/-- The width chosen from the two annular endpoints costs at most a
fixed square of the radial coefficient weight. -/
theorem materialCell_plateau_inverse_width_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      (endpointPlateauWidth D l r)⁻¹ ≤ K * radialE (D.cellIndex j) ^ 2 := by
  obtain ⟨C, hC, hwidth⟩ := materialCell_plateau_width_lower hD
  let K : ℝ := 1 + 2 * C * Real.exp 2
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro j l r hl hlr hr hcell
  let n : ℕ := D.cellIndex j
  let c : ℝ := C⁻¹ * Real.exp (-((n : ℝ) + 1) ^ 2)
  have hc : 0 < c := mul_pos (inv_pos.mpr hC) (Real.exp_pos _)
  have hδ : 0 < endpointPlateauWidth D l r := endpointPlateauWidth_pos hl hr
  have hδlower : min 1 (c / 2) ≤ endpointPlateauWidth D l r :=
    hwidth j l r hlr hcell
  have hinv : (endpointPlateauWidth D l r)⁻¹ ≤ 1 + 2 / c := by
    by_cases hcase : 1 ≤ c / 2
    · have hone : 1 ≤ endpointPlateauWidth D l r := by
        simpa only [min_eq_left hcase] using hδlower
      have hh : (endpointPlateauWidth D l r)⁻¹ ≤ 1 := by
        simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hone
      exact hh.trans (le_add_of_nonneg_right (div_nonneg (by norm_num) hc.le))
    · have hh : c / 2 ≤ endpointPlateauWidth D l r := by
        simpa only [min_eq_right (le_of_not_ge hcase)] using hδlower
      have hi := one_div_le_one_div_of_le (div_pos hc (by norm_num)) hh
      have hi' : (endpointPlateauWidth D l r)⁻¹ ≤ 2 / c := by
        simpa only [one_div, inv_div, one_mul] using hi
      exact hi'.trans (le_add_of_nonneg_left zero_le_one)
  have hcinv : 2 / c = 2 * C * Real.exp (((n : ℝ) + 1) ^ 2) := by
    dsimp only [c]
    rw [Real.exp_neg, div_eq_mul_inv, mul_inv_rev, inv_inv, inv_inv]
    ring
  have hquad : ((n : ℝ) + 1) ^ 2 ≤ 2 + 2 * radialQ n := by
    have hq := Radial.radial_nat_sq_le_Q n
    nlinarith only [hq, sq_nonneg ((n : ℝ) - 1)]
  have hexp : Real.exp (((n : ℝ) + 1) ^ 2) ≤ Real.exp 2 * radialE n ^ 2 := by
    calc
      _ ≤ Real.exp (2 + 2 * radialQ n) := Real.exp_le_exp.mpr hquad
      _ = _ := by
        rw [Real.exp_add, radialE, ← Real.exp_nat_mul]
        norm_num
  have hE : 1 ≤ radialE n :=
    (le_add_of_nonneg_left (Nat.cast_nonneg n)).trans (natCast_add_one_le_radialE n)
  have hE2 : 1 ≤ radialE n ^ 2 := one_le_pow₀ hE
  calc
    _ ≤ 1 + 2 * C * Real.exp (((n : ℝ) + 1) ^ 2) := by simpa only [hcinv] using hinv
    _ ≤ 1 + 2 * C * (Real.exp 2 * radialE n ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp (by positivity))
    _ ≤ K * radialE n ^ 2 := by dsimp only [K]; nlinarith only [hE2]

/-- On the full expanded support the endpoint coordinate differs from
the actual containing cell index by at most a fixed upper shift. -/
theorem materialCell_plateau_endpointX_index_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    {d₀ : ℝ} (hd₀ : 0 < d₀) :
    ∃ B : ℝ, 0 < B ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
        endpointX d₀ (endpointDistance D t) ≤ (D.cellIndex j : ℝ) + B := by
  obtain ⟨L, hL, hband⟩ := materialCell_plateau_scaled_endpointX_bound hT hD hd₀
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _, hcmp⟩ := hT
  obtain ⟨C, _, hC, _, hc⟩ := hcmp
  obtain ⟨_, hdata⟩ := hD
  refine ⟨L + C + Real.sqrt |Real.log d₀|, by positivity, ?_⟩
  intro j l r hl hlr hr hcell t ht
  have hs := hdata.2.1.2.2.2.1 j (hsamp j)
  have hscale := (abs_le.mp (endpointX_scale_comparison hd₀
    (endpointDistance_positive hs))).2
  have hsample := (abs_le.mp (hc j (T.sample j) (hsamp j)).1).2
  have ht' := hband j l r hl hlr hr hcell t ht
  linarith only [ht', hscale, hsample]

/-- A uniform fourth radial power bounds the material coordinate of the
entire plateau. No relation between the plateau and a nominal control
label is required. -/
theorem materialCell_plateau_rho_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
        |T.rho t| ≤ K * radialE (D.cellIndex j) ^ 4 := by
  obtain ⟨d₀, A, hd₀, hA, hρ⟩ := materialRho_endpoint_polynomial_bound hT
  obtain ⟨B, hB, hband⟩ := materialCell_plateau_endpointX_index_bound hT hD hd₀
  let K : ℝ := A + (B + 1) ^ 2 + (2 / 3 : ℝ) * (B + 1) ^ 3
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro j l r hl hlr hr hcell t ht
  let n : ℕ := D.cellIndex j
  let X : ℝ := endpointX d₀ (endpointDistance D t)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hE : 1 ≤ radialE n :=
    (le_add_of_nonneg_left (Nat.cast_nonneg n)).trans (natCast_add_one_le_radialE n)
  have hE0 : 0 ≤ radialE n := zero_le_one.trans hE
  have hXE : X ≤ (B + 1) * radialE n := by
    calc
      X ≤ (n : ℝ) + B := hband j l r hl hlr hr hcell t ht
      _ ≤ (B + 1) * ((n : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      _ ≤ _ := mul_le_mul_of_nonneg_left (natCast_add_one_le_radialE n) (by positivity)
  have hX2 : X ^ 2 ≤ (B + 1) ^ 2 * radialE n ^ 4 := by
    calc
      _ ≤ ((B + 1) * radialE n) ^ 2 := pow_le_pow_left₀ hX hXE 2
      _ = (B + 1) ^ 2 * radialE n ^ 2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hE (by decide : 2 ≤ 4)) (sq_nonneg _)
  have hX3 : X ^ 3 ≤ (B + 1) ^ 3 * radialE n ^ 4 := by
    calc
      _ ≤ ((B + 1) * radialE n) ^ 3 := pow_le_pow_left₀ hX hXE 3
      _ = (B + 1) ^ 3 * radialE n ^ 3 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hE (by decide : 3 ≤ 4)) (by positivity)
  have hAE : A ≤ A * radialE n ^ 4 :=
    le_mul_of_one_le_right hA.le (one_le_pow₀ hE)
  have hb := hρ t (endpointPlateau_support_subset hl hr ht)
  dsimp only [K]
  nlinarith only [hb, hX2, hX3, hAE]

end ContinuousFlexibility.Statements
