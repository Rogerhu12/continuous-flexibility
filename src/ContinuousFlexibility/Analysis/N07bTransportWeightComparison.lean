import ContinuousFlexibility.Analysis.N07bReferencePDEDecay

/-!
# Image height weights from actual geometric ratio bounds

The height and envelope at the image of a transport are controlled by
their ratios to the original weights. The two fixed `E0` powers combine
before the material-envelope estimate is used; a strict height-exponent
gap then absorbs the resulting two envelope powers. No regularity, source
membership, or operator-domain conclusion is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

/-- Pure geometric height and envelope ratio estimates imply the actual
image-weight estimate needed for a transported height member. The two
ratio constants and exponents may be different and need not depend on
the point. -/
theorem n07b_transport_weight_bound_of_ratios
    {D : ReferenceData} {T : MaterialData} {τ : PolarPoint → PolarPoint}
    (hT : IsMaterialData D T)
    (hmap : MapsTo τ (annularOpen D) (annularOpen D))
    {β δ CH CM AH AM : ℝ} (hβ : 0 < β) (hδβ : δ < β)
    (hCH : 0 ≤ CH) (hCM : 0 ≤ CM)
    (hHratio : ∀ x ∈ annularOpen D,
      T.H (τ x).1 / T.H x.1 ≤ CH * T.E0 x.1 ^ AH)
    (hMratio : ∀ x ∈ annularOpen D,
      T.M (τ x).1 / T.M x.1 ≤ CM * T.E0 x.1 ^ AM) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ annularOpen D,
      T.H (τ x).1 ^ β * T.M (τ x).1 ≤ C * T.H x.1 ^ δ := by
  obtain ⟨CE, hCE, hEbound⟩ :=
    hT.2.2.2.2.2.2.2.2.2.2.2.1 (AH * β + AM)
  obtain ⟨CL, hCL, hgap⟩ := n07b_material_height_gap_bound hT hδβ (2 : ℝ)
  let C₀ : ℝ := CH ^ β * CM * CE * CL
  have hC₀ : 0 ≤ C₀ :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hCH β) hCM) hCE.le) hCL.le
  refine ⟨C₀ + 1, by linarith, fun x hx => ?_⟩
  have hpos := hT.2.1 x.1 hx.1
  have hτpos := hT.2.1 (τ x).1 (hmap hx).1
  have hH : 0 < T.H x.1 := hpos.2.1
  have hE : 0 < T.E0 x.1 := hpos.2.2.1
  have hM : 0 < T.M x.1 := zero_lt_one.trans_le hpos.2.2.2
  have hτH : 0 < T.H (τ x).1 := hτpos.2.1
  have hτM : 0 ≤ T.M (τ x).1 := zero_le_one.trans hτpos.2.2.2
  have hEH : 0 ≤ T.E0 x.1 ^ AH := (Real.rpow_pos_of_pos hE AH).le
  have hEHβ : 0 ≤ T.E0 x.1 ^ (AH * β) :=
    (Real.rpow_pos_of_pos hE (AH * β)).le
  have hHβ : 0 ≤ T.H x.1 ^ β := (Real.rpow_pos_of_pos hH β).le
  have hHδ : 0 ≤ T.H x.1 ^ δ := (Real.rpow_pos_of_pos hH δ).le
  have hHimage : T.H (τ x).1 ≤ CH * T.E0 x.1 ^ AH * T.H x.1 :=
    (div_le_iff₀ hH).mp (hHratio x hx)
  have hMimage : T.M (τ x).1 ≤ CM * T.E0 x.1 ^ AM * T.M x.1 :=
    (div_le_iff₀ hM).mp (hMratio x hx)
  have hHpower : T.H (τ x).1 ^ β ≤
      CH ^ β * T.E0 x.1 ^ (AH * β) * T.H x.1 ^ β := by
    have hh := Real.rpow_le_rpow hτH.le hHimage hβ.le
    rw [Real.mul_rpow (mul_nonneg hCH hEH) hH.le,
      Real.mul_rpow hCH hEH, ← Real.rpow_mul hE.le] at hh
    exact hh
  have hprefactor : 0 ≤ (CH ^ β * CM) * (T.H x.1 ^ β * T.M x.1) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hCH β) hCM) (mul_nonneg hHβ hM.le)
  have hgap' : T.H x.1 ^ β * T.M x.1 ^ 2 ≤ CL * T.H x.1 ^ δ := by
    simpa only [Real.rpow_two] using hgap x.1 hx.1
  calc
    _ ≤ (CH ^ β * T.E0 x.1 ^ (AH * β) * T.H x.1 ^ β) *
        (CM * T.E0 x.1 ^ AM * T.M x.1) :=
      mul_le_mul hHpower hMimage hτM
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hCH β) hEHβ) hHβ)
    _ = (CH ^ β * CM) * (T.H x.1 ^ β * T.M x.1) *
        T.E0 x.1 ^ (AH * β + AM) := by
      rw [Real.rpow_add hE]
      ring
    _ ≤ (CH ^ β * CM) * (T.H x.1 ^ β * T.M x.1) * (CE * T.M x.1) :=
      mul_le_mul_of_nonneg_left (hEbound x.1 hx.1) hprefactor
    _ = (CH ^ β * CM * CE) * (T.H x.1 ^ β * T.M x.1 ^ 2) := by ring
    _ ≤ (CH ^ β * CM * CE) * (CL * T.H x.1 ^ δ) :=
      mul_le_mul_of_nonneg_left hgap'
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hCH β) hCM) hCE.le)
    _ = C₀ * T.H x.1 ^ δ := by dsimp [C₀]; ring
    _ ≤ (C₀ + 1) * T.H x.1 ^ δ :=
      mul_le_mul_of_nonneg_right (by linarith) hHδ

end ContinuousFlexibility.Analysis
