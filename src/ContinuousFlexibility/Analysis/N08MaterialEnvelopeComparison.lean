import ContinuousFlexibility.Analysis.N08EnvelopeComparisonNumeric
import ContinuousFlexibility.Statements.Analysis

/-!
# Moving envelope losses from a control label to its physical cell

Actual material weights agree with the endpoint model in both collars.
A single compact middle interval supplies the comparison constants
elsewhere. Consequently any fixed positive-power comparison of height
weights gives a fixed-power comparison of the material envelopes.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem n08_material_model_comparison {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ r ∈ Ioo D.a D.b, ∃ x : ℝ, 0 ≤ x ∧
      materialH x ≤ K * T.H r ∧ T.H r ≤ K * materialH x ∧
      materialM x ≤ K * T.M r ∧ T.M r ≤ K * materialM x := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hend, _⟩ := hdata
  obtain ⟨d0, δ, hd0, hδ, hδb, hleft, hright⟩ := hend
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : middle ⊆ Ioo D.a D.b := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  have hH : ContinuousOn T.H (Ioo D.a D.b) :=
    (hT.1 T.H (by simp)).continuousOn
  have hM : ContinuousOn T.M (Ioo D.a D.b) :=
    (hT.1 T.M (by simp)).continuousOn
  have hI : ContinuousOn (fun r => (T.H r)⁻¹) (Ioo D.a D.b) :=
    hH.inv₀ (fun r hr => (hT.2.1 r hr).2.1.ne')
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact middle).bddAbove_image
    (((hH.add hI).add hM).mono hmiddle)
  let K : ℝ := 1 + |B| + Real.exp 1
  have hK : 1 ≤ K := by dsimp only [K]; linarith only [abs_nonneg B, Real.exp_pos 1]
  have hKe : Real.exp 1 ≤ K := by dsimp only [K]; linarith only [abs_nonneg B]
  have hBK : B ≤ K := by dsimp only [K]; linarith only [le_abs_self B, Real.exp_pos 1]
  refine ⟨K, hK, fun r hr => ?_⟩
  have hposH : 0 < T.H r := (hT.2.1 r hr).2.1
  have hposM : 1 ≤ T.M r := (hT.2.1 r hr).2.2.2
  have hmodel (x : ℝ) (hx : 0 ≤ x) (hHx : T.H r = materialH x)
      (hMx : T.M r = materialM x) :
      ∃ x : ℝ, 0 ≤ x ∧ materialH x ≤ K * T.H r ∧ T.H r ≤ K * materialH x ∧
        materialM x ≤ K * T.M r ∧ T.M r ≤ K * materialM x := by
    refine ⟨x, hx, ?_, ?_, ?_, ?_⟩ <;> simp only [hHx, hMx]
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (materialH_pos x).le
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (materialH_pos x).le
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (materialM_pos x).le
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (materialM_pos x).le
  by_cases hl : r < D.a + δ
  · have he := hleft r ⟨hr.1, hl⟩
    exact hmodel (endpointX d0 (r - D.a)) (Real.sqrt_nonneg _) he.2.1 he.2.2.2
  by_cases hh : D.b - δ < r
  · have he := hright r ⟨hh, hr.2⟩
    exact hmodel (endpointX d0 (D.b - r)) (Real.sqrt_nonneg _) he.2.1 he.2.2.2
  have hrm : r ∈ middle := ⟨le_of_not_gt hl, le_of_not_gt hh⟩
  have hb : T.H r + (T.H r)⁻¹ + T.M r ≤ B := hB ⟨r, hrm, rfl⟩
  have hHupper : T.H r ≤ K := by
    linarith only [hb, hBK, (inv_pos.mpr hposH).le, hposM]
  have hIupper : (T.H r)⁻¹ ≤ K := by linarith only [hb, hBK, hposH.le, hposM]
  have hMupper : T.M r ≤ K := by linarith only [hb, hBK, hposH.le, (inv_pos.mpr hposH).le]
  have hHlower : 1 ≤ K * T.H r := by
    calc
      1 = (T.H r)⁻¹ * T.H r := (inv_mul_cancel₀ hposH.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hIupper hposH.le
  refine ⟨0, le_rfl, ?_, ?_, ?_, ?_⟩
  · simpa only [materialH, zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero,
      zero_div, Real.exp_zero] using hHlower
  · simpa only [materialH, zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero,
      zero_div, Real.exp_zero, mul_one] using hHupper
  · have hm0 : materialM 0 = Real.exp 1 := by norm_num [materialM, materialMExponent]
    rw [hm0]
    have hKM : K ≤ K * T.M r := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hposM (zero_le_one.trans hK)
    exact hKe.trans hKM
  · have hm0 : materialM 0 = Real.exp 1 := by norm_num [materialM, materialMExponent]
    rw [hm0]
    have hKe' : K ≤ K * Real.exp 1 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) (zero_le_one.trans hK)
    exact hMupper.trans hKe'

theorem n08_material_envelope_comparison {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) :
    ∃ K N : ℝ, 0 < K ∧ 0 < N ∧ ∀ r s,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
      T.H r ^ a ≤ C * T.H s ^ b → T.M s ≤ K * T.M r ^ N := by
  obtain ⟨L, hL, hmodel⟩ := n08_material_model_comparison hT
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hconstant : 0 < L ^ a * C * L ^ b := by positivity
  obtain ⟨N, hN, hcompare⟩ := n08_endpoint_height_envelope_comparison ha hb hconstant
  refine ⟨L * L ^ N, N, by positivity, hN, fun r s hr hs hc => ?_⟩
  obtain ⟨x, hx, hxH, hxH', hxM, hxM'⟩ := hmodel r hr
  obtain ⟨y, hy, hyH, hyH', hyM, hyM'⟩ := hmodel s hs
  have hHr : 0 < T.H r := (hT.2.1 r hr).2.1
  have hHs : 0 < T.H s := (hT.2.1 s hs).2.1
  have hxy : materialH x ^ a ≤ (L ^ a * C * L ^ b) * materialH y ^ b := by
    calc
      _ ≤ (L * T.H r) ^ a := Real.rpow_le_rpow (materialH_pos x).le hxH ha.le
      _ = L ^ a * T.H r ^ a := Real.mul_rpow hLp.le hHr.le
      _ ≤ L ^ a * (C * T.H s ^ b) :=
        mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hLp.le _)
      _ ≤ L ^ a * (C * (L * materialH y) ^ b) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hHs.le hyH' hb.le) hC.le)
          (Real.rpow_nonneg hLp.le _)
      _ = _ := by rw [Real.mul_rpow hLp.le (materialH_pos y).le]; ring
  have hMr : 0 ≤ T.M r := zero_le_one.trans (hT.2.1 r hr).2.2.2
  calc
    T.M s ≤ L * materialM y := hyM'
    _ ≤ L * materialM x ^ N := mul_le_mul_of_nonneg_left (hcompare x y hx hy hxy) hLp.le
    _ ≤ L * (L * T.M r) ^ N := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (materialM_pos x).le hxM hN.le) hLp.le
    _ = (L * L ^ N) * T.M r ^ N := by rw [Real.mul_rpow hLp.le hMr]; ring

theorem n08_material_envelope_power_comparison {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 < C)
    (A : ℝ) :
    ∃ K N : ℝ, 0 < K ∧ 0 ≤ N ∧ ∀ r s,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
      T.H r ^ a ≤ C * T.H s ^ b → T.M s ^ A ≤ K * T.M r ^ N := by
  obtain ⟨L, N, hL, hN, hbound⟩ := n08_material_envelope_comparison hT ha hb hC
  let p : ℝ := max A 0
  have hp : 0 ≤ p := le_max_right _ _
  refine ⟨L ^ p, N * p, Real.rpow_pos_of_pos hL _, mul_nonneg hN.le hp,
    fun r s hr hs hc => ?_⟩
  have hMr : 0 ≤ T.M r := zero_le_one.trans (hT.2.1 r hr).2.2.2
  have hMs : 1 ≤ T.M s := (hT.2.1 s hs).2.2.2
  calc
    T.M s ^ A ≤ T.M s ^ p := Real.rpow_le_rpow_of_exponent_le hMs (le_max_left _ _)
    _ ≤ (L * T.M r ^ N) ^ p :=
      Real.rpow_le_rpow (zero_le_one.trans hMs) (hbound r s hr hs hc) hp
    _ = L ^ p * T.M r ^ (N * p) := by
      rw [Real.mul_rpow hL.le (Real.rpow_nonneg hMr _), ← Real.rpow_mul hMr]

end ContinuousFlexibility.Statements
