module

public import ContinuousFlexibility.Radial.MorseRetainedRadiusModelBounds
public import ContinuousFlexibility.Radial.MorseRealizationBasic

/-!
# Model integrals of an arbitrary realized Morse chain

The estimates refer to the actual radius charts carried by `MorseChainData`.
Their constants are independent of the height choices in a realized family.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def morseRealizedMassModel (T : MorseChainData) (side : Bool) (n : ℕ) : ℝ :=
  ∫ x in T.leftX side n..morseChainRightTurn T n,
    (deriv (T.radius side n) x) ^ 2 * (T.radius side n x) ^ 6

def morseRealizedResistanceModel (T : MorseChainData) (side : Bool) (n : ℕ) : ℝ :=
  ∫ x in T.leftX side n..morseChainRightTurn T n, ((T.radius side n x) ^ 8)⁻¹

def morseRealizedCapMassModel (T : MorseChainData) (side : Bool) (n : ℕ) : ℝ :=
  ∫ x in morseChainRightTurn T n..T.rightX side n,
    (deriv (T.radius side n) x) ^ 2 * (T.radius side n x) ^ 6

def morseRealizedCapResistanceModel (T : MorseChainData) (side : Bool) (n : ℕ) : ℝ :=
  ∫ x in morseChainRightTurn T n..T.rightX side n, ((T.radius side n x) ^ 8)⁻¹

/-- Uniform model estimates, before multiplication by the height amplitude. -/
structure MorseRealizedCellEstimates (T : MorseChainData) (K : ℝ) : Prop where
  one_le : 1 ≤ K
  mass_lower : ∀ side n, T.index ≤ n →
    morseChainA T n ^ 2 / K ≤ morseRealizedMassModel T side n
  mass_upper : ∀ side n, T.index ≤ n →
    morseRealizedMassModel T side n ≤ K * morseChainA T n ^ 2
  resistance_upper : ∀ side n, T.index ≤ n →
    morseRealizedResistanceModel T side n ≤
      K * log (morseChainA T n / morseChainB T n)
  cap_mass_upper : ∀ side n, T.index ≤ n →
    morseRealizedCapMassModel T side n ≤ K * morseChainA T n ^ 6
  cap_resistance_lower : ∀ side n, T.index ≤ n →
    (morseChainA T n ^ 4)⁻¹ / K ≤ morseRealizedCapResistanceModel T side n
  cap_resistance_upper : ∀ side n, T.index ≤ n →
    morseRealizedCapResistanceModel T side n ≤ K * (morseChainA T n ^ 4)⁻¹
  left_speed_upper : ∀ side n, T.index ≤ n →
    deriv (T.radius side n) (T.leftX side n) ≤ K * morseChainA T n
  right_speed_lower : ∀ side n, T.index ≤ n →
    morseChainA T n ^ 5 / K ≤ deriv (T.radius side n) (T.rightX side n)

theorem MorseRealizedCellEstimates.pos {T : MorseChainData} {K : ℝ}
    (h : MorseRealizedCellEstimates T K) : 0 < K :=
  zero_lt_one.trans_le h.one_le

private def RealizedCellAt (T : MorseChainData) (side : Bool) (n : ℕ) (K : ℝ) : Prop :=
  morseChainA T n ^ 2 / K ≤ morseRealizedMassModel T side n ∧
  morseRealizedMassModel T side n ≤ K * morseChainA T n ^ 2 ∧
  morseRealizedResistanceModel T side n ≤ K * log (morseChainA T n / morseChainB T n) ∧
  morseRealizedCapMassModel T side n ≤ K * morseChainA T n ^ 6 ∧
  (morseChainA T n ^ 4)⁻¹ / K ≤ morseRealizedCapResistanceModel T side n ∧
  morseRealizedCapResistanceModel T side n ≤ K * (morseChainA T n ^ 4)⁻¹ ∧
  deriv (T.radius side n) (T.leftX side n) ≤ K * morseChainA T n ∧
  morseChainA T n ^ 5 / K ≤ deriv (T.radius side n) (T.rightX side n)

private theorem realizedCellAt_mono {T : MorseChainData} {side : Bool} {n : ℕ} {K L : ℝ}
    (hA : 0 < morseChainA T n) (hlog : 0 ≤ log (morseChainA T n / morseChainB T n))
    (hK : 0 < K) (hKL : K ≤ L) (h : RealizedCellAt T side n K) :
    RealizedCellAt T side n L := by
  rcases h with ⟨hmlo, hmhi, hr, hc, hclo, hchi, hlv, hrv⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_left (sq_nonneg _) hK hKL).trans hmlo
  · exact hmhi.trans (mul_le_mul_of_nonneg_right hKL (sq_nonneg _))
  · exact hr.trans (mul_le_mul_of_nonneg_right hKL hlog)
  · exact hc.trans (mul_le_mul_of_nonneg_right hKL (pow_nonneg hA.le _))
  · exact (div_le_div_of_nonneg_left (inv_nonneg.mpr (pow_nonneg hA.le _)) hK hKL).trans hclo
  · exact hchi.trans (mul_le_mul_of_nonneg_right hKL (inv_nonneg.mpr (pow_nonneg hA.le _)))
  · exact hlv.trans (mul_le_mul_of_nonneg_right hKL hA.le)
  · exact (div_le_div_of_nonneg_left (pow_nonneg hA.le _) hK hKL).trans hrv

private theorem realizedCell_positive_data {T : MorseChainData} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T (fun _ => 1) D C) (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    0 < morseChainA T n ∧ 0 < log (morseChainA T n / morseChainB T n) ∧
    0 < morseRealizedMassModel T side n ∧ 0 < morseRealizedCapResistanceModel T side n ∧
    0 < deriv (T.radius side n) (T.rightX side n) := by
  obtain ⟨hB, hAB, _, hab, hbe, _, _⟩ := h.retained_data side n hn
  have hA : 0 < morseChainA T n := (mul_pos (by norm_num) hB).trans hAB
  have hlog : 0 < log (morseChainA T n / morseChainB T n) := by
    apply log_pos
    apply (one_lt_div hB).mpr
    linarith only [hAB, hB]
  have hae : T.leftX side n < T.rightX side n := hab.trans hbe
  have hr := h.radius_smooth side n hn
  have hv := (contDiff_infty_iff_deriv.mp hr).2
  have hMc : Continuous (fun x => (deriv (T.radius side n) x) ^ 2 * (T.radius side n x) ^ 6) :=
    (hv.continuous.pow 2).mul (hr.continuous.pow 6)
  have hRc : ContinuousOn (fun x => ((T.radius side n x) ^ 8)⁻¹)
      (Icc (morseChainRightTurn T n) (T.rightX side n)) :=
    (hr.continuous.continuousOn.pow 8).inv₀ (fun x hx =>
      pow_ne_zero 8 (h.radius_positive side n hn x ⟨hab.le.trans hx.1, hx.2⟩).ne')
  refine ⟨hA, hlog, ?_, ?_, h.derivative_positive side n hn _ (right_mem_Icc.mpr hae.le)⟩
  · apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hMc.intervalIntegrable _ _) _ hab
    intro x hx
    have hx' : x ∈ Icc (T.leftX side n) (T.rightX side n) :=
      ⟨hx.1.le, hx.2.le.trans hbe.le⟩
    exact mul_pos (pow_pos (h.derivative_positive side n hn x hx') 2)
      (pow_pos (h.radius_positive side n hn x hx') 6)
  · apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hRc.intervalIntegrable_of_Icc hbe.le) _ hbe
    intro x hx
    exact inv_pos.mpr (pow_pos (h.radius_positive side n hn x
      ⟨hab.le.trans hx.1.le, hx.2.le⟩) 8)

private theorem exists_realizedCellAt {T : MorseChainData} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T (fun _ => 1) D C) (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    ∃ K : ℝ, 1 ≤ K ∧ RealizedCellAt T side n K := by
  classical
  obtain ⟨hA, hlog, hM, hRC, hV⟩ := realizedCell_positive_data h side n hn
  let A := morseChainA T n
  let M := morseRealizedMassModel T side n
  let R := morseRealizedResistanceModel T side n
  let MC := morseRealizedCapMassModel T side n
  let RC := morseRealizedCapResistanceModel T side n
  let L := log (A / morseChainB T n)
  let vl := deriv (T.radius side n) (T.leftX side n)
  let vr := deriv (T.radius side n) (T.rightX side n)
  let S : Finset ℝ := {1, A ^ 2 / M, M / A ^ 2, R / L, MC / A ^ 6,
    (A ^ 4)⁻¹ / RC, RC / (A ^ 4)⁻¹, vl / A, A ^ 5 / vr}
  obtain ⟨K, hK⟩ := S.bddAbove
  have hK1 : 1 ≤ K := hK (by simp [S])
  have hKp : 0 < K := zero_lt_one.trans_le hK1
  have hmem (x : ℝ) (hx : x ∈ S) : x ≤ K := hK hx
  refine ⟨K, hK1, ?_⟩
  change A ^ 2 / K ≤ M ∧ M ≤ K * A ^ 2 ∧ R ≤ K * L ∧ MC ≤ K * A ^ 6 ∧
    (A ^ 4)⁻¹ / K ≤ RC ∧ RC ≤ K * (A ^ 4)⁻¹ ∧ vl ≤ K * A ∧ A ^ 5 / K ≤ vr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hKp).mpr
    simpa only [mul_comm] using (div_le_iff₀ hM).mp (hmem _ (by simp [S, A, M, R, MC, RC, L, vl, vr]))
  · exact (div_le_iff₀ (pow_pos hA 2)).mp (hmem _ (by simp [S, A, M, R, MC, RC, L, vl, vr]))
  · exact (div_le_iff₀ hlog).mp (hmem _ (by simp [S, A, M, R, MC, RC, L, vl, vr]))
  · exact (div_le_iff₀ (pow_pos hA 6)).mp (hmem _ (by simp [S, A, M, R, MC, RC, L, vl, vr]))
  · apply (div_le_iff₀ hKp).mpr
    simpa only [mul_comm] using (div_le_iff₀ hRC).mp (hmem _ (by simp [S, A, M, R, MC, RC, L, vl, vr]))
  · exact (div_le_iff₀ (inv_pos.mpr (pow_pos hA 4))).mp (hmem _ (by simp [S, A, M, R, MC, RC, L, vl, vr]))
  · exact (div_le_iff₀ hA).mp (hmem _ (by simp [S, A, M, R, MC, RC, L, vl, vr]))
  · apply (div_le_iff₀ hKp).mpr
    simpa only [mul_comm] using (div_le_iff₀ hV).mp (hmem _ (by simp [S, A, M, R, MC, RC, L, vl, vr]))

private theorem realizedCell_tail_model {T : MorseChainData} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T (fun _ => 1) D C) (side : Bool) (n : ℕ)
    (hn : T.index ≤ n) (h100 : 100 ≤ n) :
    let A := morseChainA T n
    let B := morseChainB T n
    let s := T.radius side n (morseChainRightTurn T n)
    (s ^ 8 * (morseShortLeftCapLength / 1024 * A ^ 2) ≤ morseRealizedMassModel T side n ∧
      morseRealizedMassModel T side n ≤ s ^ 8 * (2688 * A ^ 2)) ∧
    morseRealizedResistanceModel T side n ≤ (s ^ 8)⁻¹ * (512 * log (A / B)) ∧
    morseRealizedCapMassModel T side n ≤ s ^ 8 * A ^ 6 ∧
    ((s ^ 8)⁻¹ * ((A ^ 4)⁻¹ / 25600) ≤ morseRealizedCapResistanceModel T side n ∧
      morseRealizedCapResistanceModel T side n ≤ (s ^ 8)⁻¹ * (3 * (A ^ 4)⁻¹)) ∧
    deriv (T.radius side n) (T.leftX side n) ≤ 7 * s * A ∧
    s / 100 * A ^ 5 ≤ deriv (T.radius side n) (T.rightX side n) := by
  let A := morseChainA T n
  let B := morseChainB T n
  let s := T.radius side n (morseChainRightTurn T n)
  obtain ⟨hB, hAB, hleft, hab, hbe, hright, hspeed⟩ := h.retained_data side n hn
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have ha : T.leftX side n = morseCellLeftCut := hleft
  have hb : morseChainRightTurn T n = morseRightTurn A B := rfl
  have he : T.rightX side n = morseRightCapEnd A B (1 / 100) := by
    simpa only [morseRightCapEnd, morseRightCapLength, hb] using hright
  have hd1 : 1 ≤ (T.d n : ℝ) :=
    (one_le_exp_iff.mpr (sq_nonneg (n : ℝ))).trans (h.1 n hn).1
  have hBA := morseChainB_A_bounds T n hd1
  have hA₀ : A ≤ 1 / 1000 := by
    apply morseChainA_le_of_sq_ge_log T n (h.d_eq n hn) (by norm_num)
    have hnR : (100 : ℝ) ≤ n := by exact_mod_cast h100
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hnR 2
    have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9 / (1 / 1000 : ℝ))
    norm_num at hsq hlog ⊢
    linarith only [hlog, hsq]
  have hs : 0 < s := h.radius_positive side n hn _ ⟨hab.le, hbe.le⟩
  have hsub (x : ℝ) (hx : x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100))) :
      x ∈ Icc (T.leftX side n) (T.rightX side n) := by rwa [ha, he]
  have hmodel := morseRetainedRadius_model_bounds hB hAB hA₀ hBA.1 hBA.2
    hs (h.radius_smooth side n hn) (show T.radius side n (morseRightTurn A B) = s from rfl)
    (show deriv (T.radius side n) (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 * s from hspeed)
    (fun x hx => h.equation side n hn x (hsub x hx))
    (fun x hx => h.radius_positive side n hn x (hsub x hx))
    (fun x hx => h.derivative_positive side n hn x (hsub x hx))
  simpa only [morseRealizedMassModel, morseRealizedResistanceModel,
    morseRealizedCapMassModel, morseRealizedCapResistanceModel, ha, hb, he, A, B, s] using hmodel

private theorem realized_div_le_of_lower {a c M K : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hK : 0 < K) (hInv : c⁻¹ ≤ K) (hLower : c * a ≤ M) : a / K ≤ M := by
  have hki : K⁻¹ ≤ c := (inv_anti₀ (inv_pos.mpr hc) hInv).trans_eq (inv_inv c)
  calc
    a / K = K⁻¹ * a := by rw [div_eq_mul_inv, mul_comm]
    _ ≤ c * a := mul_le_mul_of_nonneg_right hki ha
    _ ≤ M := hLower

private theorem exists_realizedCell_tail_bound {T : MorseChainData} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T (fun _ => 1) D C) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ side n, T.index ≤ n → 100 ≤ n → RealizedCellAt T side n K := by
  classical
  let a := D.a
  let b := D.b
  have ha : 0 < a := h.geometry.1
  have hb : 0 < b := ha.trans h.geometry.2.1
  let ml := a ^ 8 * (morseShortLeftCapLength / 1024)
  let mu := b ^ 8 * 2688
  let ri := (a ^ 8)⁻¹ * 512
  let cm := b ^ 8
  let cl := (b ^ 8)⁻¹ / 25600
  let cu := (a ^ 8)⁻¹ * 3
  let vl := 7 * b
  let vr := a / 100
  have hlen : 0 < morseShortLeftCapLength := morseShortLeftCapLength_pos
  have hml : 0 < ml := mul_pos (pow_pos ha 8)
    (div_pos hlen (by norm_num))
  have hcl : 0 < cl := div_pos (inv_pos.mpr (pow_pos hb 8)) (by norm_num)
  have hvr : 0 < vr := div_pos ha (by norm_num)
  let S : Finset ℝ := {1, ml⁻¹, mu, ri, cm, cl⁻¹, cu, vl, vr⁻¹}
  obtain ⟨K, hK⟩ := S.bddAbove
  have hK1 : 1 ≤ K := hK (by simp [S])
  have hKp : 0 < K := zero_lt_one.trans_le hK1
  have hmem (x : ℝ) (hx : x ∈ S) : x ≤ K := hK hx
  refine ⟨K, hK1, ?_⟩
  intro side n hn h100
  let A := morseChainA T n
  let s := T.radius side n (morseChainRightTurn T n)
  obtain ⟨hA, hlog, _, _, _⟩ := realizedCell_positive_data h side n hn
  obtain ⟨_, _, _, hab, hbe, _, _⟩ := h.retained_data side n hn
  have hsB := h.radius_mem_core side n hn _ ⟨hab.le, hbe.le⟩
  have hslo : a ≤ s := hsB.1.le
  have hshi : s ≤ b := hsB.2.le
  have hs : 0 < s := ha.trans_le hslo
  have hs8lo : a ^ 8 ≤ s ^ 8 := pow_le_pow_left₀ ha.le hslo 8
  have hs8hi : s ^ 8 ≤ b ^ 8 := pow_le_pow_left₀ hs.le hshi 8
  have hsiLo : (b ^ 8)⁻¹ ≤ (s ^ 8)⁻¹ := inv_anti₀ (pow_pos hs 8) hs8hi
  have hsiHi : (s ^ 8)⁻¹ ≤ (a ^ 8)⁻¹ := inv_anti₀ (pow_pos ha 8) hs8lo
  obtain ⟨hM, hR, hCM, hCR, hVL, hVR⟩ := realizedCell_tail_model h side n hn h100
  have hmlo : ml * A ^ 2 ≤ morseRealizedMassModel T side n := by
    calc
      _ = a ^ 8 * (morseShortLeftCapLength / 1024 * A ^ 2) := by dsimp only [ml]; ring
      _ ≤ s ^ 8 * (morseShortLeftCapLength / 1024 * A ^ 2) :=
        mul_le_mul_of_nonneg_right hs8lo (by positivity)
      _ ≤ _ := hM.1
  have hmhi : morseRealizedMassModel T side n ≤ mu * A ^ 2 := by
    calc
      _ ≤ s ^ 8 * (2688 * A ^ 2) := hM.2
      _ ≤ b ^ 8 * (2688 * A ^ 2) := mul_le_mul_of_nonneg_right hs8hi (by positivity)
      _ = _ := by dsimp only [mu]; ring
  have hrhi : morseRealizedResistanceModel T side n ≤ ri * log (A / morseChainB T n) := by
    calc
      _ ≤ (s ^ 8)⁻¹ * (512 * log (A / morseChainB T n)) := hR
      _ ≤ (a ^ 8)⁻¹ * (512 * log (A / morseChainB T n)) :=
        mul_le_mul_of_nonneg_right hsiHi (by positivity)
      _ = _ := by dsimp only [ri]; ring
  have hcmhi : morseRealizedCapMassModel T side n ≤ cm * A ^ 6 :=
    hCM.trans (mul_le_mul_of_nonneg_right hs8hi (pow_nonneg hA.le 6))
  have hcrlo : cl * (A ^ 4)⁻¹ ≤ morseRealizedCapResistanceModel T side n := by
    calc
      _ = (b ^ 8)⁻¹ * ((A ^ 4)⁻¹ / 25600) := by dsimp only [cl]; ring
      _ ≤ (s ^ 8)⁻¹ * ((A ^ 4)⁻¹ / 25600) := mul_le_mul_of_nonneg_right hsiLo (by positivity)
      _ ≤ _ := hCR.1
  have hcrhi : morseRealizedCapResistanceModel T side n ≤ cu * (A ^ 4)⁻¹ := by
    calc
      _ ≤ (s ^ 8)⁻¹ * (3 * (A ^ 4)⁻¹) := hCR.2
      _ ≤ (a ^ 8)⁻¹ * (3 * (A ^ 4)⁻¹) := mul_le_mul_of_nonneg_right hsiHi (by positivity)
      _ = _ := by dsimp only [cu]; ring
  have hvlhi : deriv (T.radius side n) (T.leftX side n) ≤ vl * A :=
    hVL.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hshi (by norm_num)) hA.le)
  have hvrlo : vr * A ^ 5 ≤ deriv (T.radius side n) (T.rightX side n) :=
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hslo (by norm_num))
      (pow_nonneg hA.le 5)).trans hVR
  refine ⟨realized_div_le_of_lower (sq_nonneg A) hml hKp (hmem _ (by simp [S])) hmlo,
    hmhi.trans (mul_le_mul_of_nonneg_right (hmem _ (by simp [S])) (sq_nonneg A)),
    hrhi.trans (mul_le_mul_of_nonneg_right (hmem _ (by simp [S])) hlog.le),
    hcmhi.trans (mul_le_mul_of_nonneg_right (hmem _ (by simp [S])) (pow_nonneg hA.le 6)),
    realized_div_le_of_lower (inv_nonneg.mpr (pow_nonneg hA.le 4)) hcl hKp
      (hmem _ (by simp [S])) hcrlo,
    hcrhi.trans (mul_le_mul_of_nonneg_right (hmem _ (by simp [S])) (inv_nonneg.mpr (pow_nonneg hA.le 4))),
    hvlhi.trans (mul_le_mul_of_nonneg_right (hmem _ (by simp [S])) hA.le),
    realized_div_le_of_lower (pow_nonneg hA.le 5) hvr hKp (hmem _ (by simp [S])) hvrlo⟩

/-- The actual radius charts of one realization have uniform model estimates.
The certificate depends only on the fixed chain, so it applies to every
height choice realized on these same charts. -/
theorem exists_morseRealizedCellEstimates {T : MorseChainData} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T (fun _ => 1) D C) :
    ∃ K : ℝ, MorseRealizedCellEstimates T K := by
  classical
  obtain ⟨Kt, hKt, htail⟩ := exists_realizedCell_tail_bound h
  have hhead (side : Bool) (n : ℕ) :
      ∃ K : ℝ, 1 ≤ K ∧ (T.index ≤ n → RealizedCellAt T side n K) := by
    by_cases hn : T.index ≤ n
    · obtain ⟨K, hK, hb⟩ := exists_realizedCellAt h side n hn
      exact ⟨K, hK, fun _ => hb⟩
    · exact ⟨1, le_rfl, fun h' => (hn h').elim⟩
  choose k hk1 hk using hhead
  obtain ⟨Kh, hKh⟩ := (Set.finite_range (fun p : Bool × Fin 100 => k p.1 p.2)).bddAbove
  let K := max Kt (max 1 Kh)
  have hK1 : 1 ≤ K := (le_max_left 1 Kh).trans (le_max_right Kt _)
  have hAll (side : Bool) (n : ℕ) (hn : T.index ≤ n) : RealizedCellAt T side n K := by
    obtain ⟨hA, hlog, _, _, _⟩ := realizedCell_positive_data h side n hn
    by_cases h100 : 100 ≤ n
    · exact realizedCellAt_mono hA hlog.le (zero_lt_one.trans_le hKt)
        (le_max_left _ _) (htail side n hn h100)
    · have hn100 : n < 100 := lt_of_not_ge h100
      have hkKh : k side n ≤ Kh := hKh ⟨(side, ⟨n, hn100⟩), rfl⟩
      exact realizedCellAt_mono hA hlog.le (zero_lt_one.trans_le (hk1 side n))
        (hkKh.trans ((le_max_right 1 Kh).trans (le_max_right Kt _))) (hk side n hn)
  refine ⟨K, hK1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun side n hn => (hAll side n hn).1
  · exact fun side n hn => (hAll side n hn).2.1
  · exact fun side n hn => (hAll side n hn).2.2.1
  · exact fun side n hn => (hAll side n hn).2.2.2.1
  · exact fun side n hn => (hAll side n hn).2.2.2.2.1
  · exact fun side n hn => (hAll side n hn).2.2.2.2.2.1
  · exact fun side n hn => (hAll side n hn).2.2.2.2.2.2.1
  · exact fun side n hn => (hAll side n hn).2.2.2.2.2.2.2

end ContinuousFlexibility.Radial
