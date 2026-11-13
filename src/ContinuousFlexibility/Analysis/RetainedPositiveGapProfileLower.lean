import ContinuousFlexibility.Analysis.RetainedMorsePositiveGapComponents
import ContinuousFlexibility.Analysis.RetainedMorsePositiveGapMaterialWidth
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax

/-!
# Physical profile lower bounds on the actual retained positive gaps

The installed Morse estimate concerns the original physical profile.
The retained derivative identity transports it with the exact fixed
height divided by radius cubed. The actual midpoint cell then controls
both its model weight and reciprocal gap length. The resulting linear
endpoint lower bound belongs to the same profile and material sample.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem retainedReference_positive_gap_profile_product_lower
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    {D : ReferenceData} (hw : D.w = P.pair.profile) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ (side : Bool) (n : ℕ), S.chain.index ≤ n →
      ∀ r ∈ Icc (n06MorsePositiveLeft S.chain side n) (n06MorsePositiveRight S.chain side n),
        c * radialE (n + 1) ^ (-A) *
            (P.sideRadius side * r - P.sideRadius side * n06MorsePositiveLeft S.chain side n) *
            (P.sideRadius side * n06MorsePositiveRight S.chain side n - P.sideRadius side * r) ≤
          deriv D.w (P.sideRadius side * r) / (P.sideRadius side * r) := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  obtain ⟨c, A, hc, hA, hprofile⟩ :=
    n06_morseRealization_positive_gap_product_lower hreal hS.2.2.1
  let k : Bool → ℝ := fun side => c * P.sideHeight side / P.sideRadius side ^ 3
  have hk (side : Bool) : 0 < k side :=
    div_pos (mul_pos hc (P.sideHeight_pos side)) (pow_pos (P.sideRadius_pos side) 3)
  let b : ℝ := min (k false) (k true)
  have hb : 0 < b := lt_min (hk false) (hk true)
  have hbk (side : Bool) : b ≤ k side := by
    cases side
    · exact min_le_left _ _
    · exact min_le_right _ _
  refine ⟨b, A, hb, hA, ?_⟩
  intro side n hn r hr
  let R : ℝ := P.sideRadius side
  let H : ℝ := P.sideHeight side
  let l : ℝ := n06MorsePositiveLeft S.chain side n
  let u : ℝ := n06MorsePositiveRight S.chain side n
  have hR : 0 < R := P.sideRadius_pos side
  have hH : 0 < H := P.sideHeight_pos side
  have hgeom := n06_morsePositive_gap_geometry hreal side hn
  have hrpos : 0 < r := hreal.geometry.1.trans (hgeom.1.trans_le hr.1)
  let Z : ℝ := radialE (n + 1) ^ (-A) * (R * r - R * l) * (R * u - R * r)
  have hZ : 0 ≤ Z := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (exp_pos _).le _)
      (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hr.1 hR.le)))
    (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hr.2 hR.le))
  have hderiv : deriv D.w (R * r) = H * deriv (S.family S.sigma).w r :=
    retainedReference_positive_gap_deriv P hS hband hw side hn hr
  calc
    b * radialE (n + 1) ^ (-A) * (R * r - R * l) * (R * u - R * r) = b * Z := by
      dsimp only [Z]
      ring
    _ ≤ k side * Z := mul_le_mul_of_nonneg_right (hbk side) hZ
    _ = (H / R) * (c * radialE (n + 1) ^ (-A) * (r - l) * (u - r)) := by
      dsimp only [k, Z, H, R]
      field_simp [(P.sideRadius_pos side).ne']
      <;> ring
    _ ≤ (H / R) * (deriv (S.family S.sigma).w r / r) :=
      mul_le_mul_of_nonneg_left (hprofile side n hn r hr) (div_pos hH hR).le
    _ = deriv D.w (R * r) / (R * r) := by
      rw [hderiv]
      field_simp [hR.ne', hrpos.ne']
      <;> ring

/-- The reciprocal lower coefficient is controlled by the actual cell
containing the physical midpoint. The whole gap need not lie in that cell. -/
theorem retainedReference_positive_gap_profile_material_lower
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ (side : Bool) (n : ℕ), S.chain.index ≤ n → ∀ j,
      P.sideRadius side * ((n06MorsePositiveLeft S.chain side n +
        n06MorsePositiveRight S.chain side n) / 2) ∈ Γ.reference.cells j →
      ∀ x ∈ Icc (P.sideRadius side * n06MorsePositiveLeft S.chain side n)
        (P.sideRadius side * n06MorsePositiveRight S.chain side n),
        (B * T.E0 (T.sample j) ^ A)⁻¹ *
            min (x - P.sideRadius side * n06MorsePositiveLeft S.chain side n)
              (P.sideRadius side * n06MorsePositiveRight S.chain side n - x) ≤
          deriv Γ.reference.w x / x := by
  obtain ⟨c, P0, hc, hP0, hprofile⟩ :=
    retainedReference_positive_gap_profile_product_lower P hS hband hw
  obtain ⟨Cw, Aw, hCw, hAw, hweight⟩ :=
    retainedReference_positive_gap_weight_bound P hS hband hΓ hcoordinates hT hP0.le
  obtain ⟨Cs, As, hCs, hAs, hwidth⟩ :=
    retainedReference_positive_gap_inverse_width_bound P hS hband hΓ hcoordinates hT
  let B : ℝ := 2 * c⁻¹ * Cw * Cs
  have htwo : 0 < 2 * c⁻¹ := mul_pos (by norm_num) (inv_pos.mpr hc)
  have hB : 0 < B := mul_pos (mul_pos htwo hCw) hCs
  refine ⟨B, Aw + As, hB, add_nonneg hAw hAs, ?_⟩
  intro side n hn j hj x hx
  let R : ℝ := P.sideRadius side
  let l : ℝ := n06MorsePositiveLeft S.chain side n
  let u : ℝ := n06MorsePositiveRight S.chain side n
  let d : ℝ := R * u - R * l
  have hR : 0 < R := P.sideRadius_pos side
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hg := n06_morsePositive_gap_geometry hreal side hn
  have hlu : l < u := hg.2.1.trans (hg.2.2.1.trans hg.2.2.2.1)
  have hd : 0 < d := sub_pos.mpr (mul_lt_mul_of_pos_left hlu hR)
  have hmid : (l + u) / 2 ∈ Icc l u := by constructor <;> linarith only [hlu]
  have hmodel : radialE (n + 1) ^ P0 ≤ Cw * T.E0 (T.sample j) ^ Aw :=
    hweight side n hn j ((l + u) / 2) hmid hj
  have hspan : d⁻¹ ≤ Cs * T.E0 (T.sample j) ^ As := hwidth side n hn j hj
  have hEj : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hΓ.2.1 hT j)).2.2.1
  have hp : 0 < radialE (n + 1) ^ (-P0) := Real.rpow_pos_of_pos (exp_pos _) _
  let κ : ℝ := c * radialE (n + 1) ^ (-P0) * d / 2
  have hκ : 0 < κ := div_pos (mul_pos (mul_pos hc hp) hd) (by norm_num)
  have hκcost : κ⁻¹ ≤ B * T.E0 (T.sample j) ^ (Aw + As) := by
    calc
      κ⁻¹ = (2 * c⁻¹) * radialE (n + 1) ^ P0 * d⁻¹ := by
        dsimp only [κ]
        have hE0 : 0 ≤ radialE (n + 1) := (exp_pos _).le
        rw [inv_div, div_eq_mul_inv, mul_inv_rev, mul_inv_rev,
          Real.rpow_neg hE0, inv_inv]
        ring
      _ ≤ (2 * c⁻¹) * (Cw * T.E0 (T.sample j) ^ Aw) *
          (Cs * T.E0 (T.sample j) ^ As) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmodel htwo.le) hspan
          (inv_pos.mpr hd).le
          (mul_nonneg htwo.le (mul_nonneg hCw.le (Real.rpow_nonneg hEj.le _)))
      _ = B * T.E0 (T.sample j) ^ (Aw + As) := by
        rw [Real.rpow_add hEj]
        dsimp only [B]
        ring
  have hsmall : (B * T.E0 (T.sample j) ^ (Aw + As))⁻¹ ≤ κ := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hκ) hκcost
  let r : ℝ := x / R
  have hr : r ∈ Icc l u := by
    constructor
    · exact (le_div_iff₀ hR).mpr (by simpa only [mul_comm] using hx.1)
    · exact (div_le_iff₀ hR).mpr (by simpa only [mul_comm] using hx.2)
  have he : R * r = x := by
    dsimp only [r]
    field_simp [hR.ne']
    <;> ring
  have hproduct : c * radialE (n + 1) ^ (-P0) * (x - R * l) * (R * u - x) ≤
      deriv Γ.reference.w x / x := by
    have hh : c * radialE (n + 1) ^ (-P0) * (R * r - R * l) * (R * u - R * r) ≤
        deriv Γ.reference.w (R * r) / (R * r) := hprofile side n hn r hr
    simpa only [he] using hh
  have hmin : 0 ≤ min (x - R * l) (R * u - x) :=
    le_min (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)
  have hsum : max (x - R * l) (R * u - x) + min (x - R * l) (R * u - x) = d := by
    rw [max_add_min]
    dsimp only [d]
    ring
  have hhalf : d / 2 ≤ max (x - R * l) (R * u - x) := by
    have hm : min (x - R * l) (R * u - x) ≤ max (x - R * l) (R * u - x) := min_le_max
    linarith only [hsum, hm]
  have hdist : (d / 2) * min (x - R * l) (R * u - x) ≤
      (x - R * l) * (R * u - x) := by
    calc
      _ ≤ max (x - R * l) (R * u - x) * min (x - R * l) (R * u - x) :=
        mul_le_mul_of_nonneg_right hhalf hmin
      _ = _ := max_mul_min _ _
  calc
    (B * T.E0 (T.sample j) ^ (Aw + As))⁻¹ * min (x - R * l) (R * u - x) ≤
        κ * min (x - R * l) (R * u - x) := mul_le_mul_of_nonneg_right hsmall hmin
    _ = (c * radialE (n + 1) ^ (-P0)) * ((d / 2) * min (x - R * l) (R * u - x)) := by
      dsimp only [κ]
      ring
    _ ≤ (c * radialE (n + 1) ^ (-P0)) * ((x - R * l) * (R * u - x)) :=
      mul_le_mul_of_nonneg_left hdist (mul_pos hc hp).le
    _ = c * radialE (n + 1) ^ (-P0) * (x - R * l) * (R * u - x) := by ring
    _ ≤ deriv Γ.reference.w x / x := hproduct

end ContinuousFlexibility.Radial
