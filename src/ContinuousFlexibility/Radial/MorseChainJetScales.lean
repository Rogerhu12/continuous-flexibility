module

public import ContinuousFlexibility.Radial.MorseJoinPhysicalJets
public import ContinuousFlexibility.Radial.MorseJoinHeightContrast

/-!
# Index-dependent physical jets in the Morse chain

The adjacent-index comparison preserves the principal height exponent.
The actual connector widths and logarithmic height gap determine a
common scale for all the physical derivative estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem morseChain_adjacent_sq_le {n m : ℕ} (hn : 1 ≤ n)
    (hadj : m = n + 1 ∨ n = m + 1) : (m : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
  have hm : m ≤ n + 1 := by rcases hadj with h | h <;> omega
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (m : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hm
  calc
    _ ≤ (2 * (n : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith only [hn₁, hmn]) 2
    _ = _ := by ring

private theorem morseChain_adjacent_rpow_diff_le {n m : ℕ} (hn : 1 ≤ n)
    (hadj : m = n + 1 ∨ n = m + 1) :
    |(m : ℝ) ^ (5 / 2 : ℝ) - (n : ℝ) ^ (5 / 2 : ℝ)| ≤ 10 * (n : ℝ) ^ 2 := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsmall : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith only [hn₁]
  have hpow : ((n : ℝ) + 1) ^ (3 / 2 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := calc
    _ ≤ ((n : ℝ) + 1) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [hn₁]) (by norm_num)
    _ = ((n : ℝ) + 1) ^ 2 := Real.rpow_two _
    _ ≤ (2 * (n : ℝ)) ^ 2 := pow_le_pow_left₀ (by linarith only [hn₁]) hsmall 2
    _ = _ := by ring
  have hstep (x : ℝ) (hx : 0 ≤ x) (hxn : x ≤ (n : ℝ)) :
      |(x + 1) ^ (5 / 2 : ℝ) - x ^ (5 / 2 : ℝ)| ≤ 10 * (n : ℝ) ^ 2 := by
    have h := morseJoin_rpow_increment hx
    have hcmp : (x + 1) ^ (3 / 2 : ℝ) ≤ 4 * (n : ℝ) ^ 2 :=
      (Real.rpow_le_rpow (by linarith only [hx]) (add_le_add hxn (le_refl (1 : ℝ)))
        (by norm_num : (0 : ℝ) ≤ 3 / 2)).trans hpow
    rw [abs_of_nonneg h.1]
    exact h.2.trans (by linarith only [hcmp])
  rcases hadj with h | h
  · subst m
    simpa only [Nat.cast_add, Nat.cast_one] using hstep (n : ℝ) (Nat.cast_nonneg n) le_rfl
  · have hc : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast h
    have hh := hstep (m : ℝ) (Nat.cast_nonneg m) (by linarith only [hc])
    rw [← hc] at hh
    exact (abs_sub_comm _ _).trans_le hh

/-- Adjacent labels may be interchanged in either of the two exponential
jet bounds. The same comparison covers outward and inward labels. -/
theorem morseChain_exp_jet_adjacent {n m : ℕ} (hn : 1 ≤ n)
    (hadj : m = n + 1 ∨ n = m + 1) {ε : ℝ} (hε : |ε| ≤ 1) (B : ℝ) :
    exp (ε * (m : ℝ) ^ (5 / 2 : ℝ) + B * (m : ℝ) ^ 2) ≤
      exp (ε * (n : ℝ) ^ (5 / 2 : ℝ) + (10 + 4 * |B|) * (n : ℝ) ^ 2) := by
  have hΔ := morseChain_adjacent_rpow_diff_le hn hadj
  have hsq := morseChain_adjacent_sq_le hn hadj
  have hB := mul_le_mul (le_abs_self B) hsq (sq_nonneg (m : ℝ)) (abs_nonneg B)
  have hεΔ : ε * ((m : ℝ) ^ (5 / 2 : ℝ) - (n : ℝ) ^ (5 / 2 : ℝ)) ≤ 10 * (n : ℝ) ^ 2 := calc
    _ ≤ |ε * ((m : ℝ) ^ (5 / 2 : ℝ) - (n : ℝ) ^ (5 / 2 : ℝ))| := le_abs_self _
    _ = |ε| * |(m : ℝ) ^ (5 / 2 : ℝ) - (n : ℝ) ^ (5 / 2 : ℝ)| := abs_mul _ _
    _ ≤ 1 * (10 * (n : ℝ) ^ 2) := mul_le_mul hε hΔ (abs_nonneg _) zero_le_one
    _ = _ := one_mul _
  exact exp_le_exp.mpr (by nlinarith only [hB, hεΔ])

theorem morseChain_height_band_adjacent {n m : ℕ} (hn : 1 ≤ n)
    (hadj : m = n + 1 ∨ n = m + 1) {B w : ℝ} (hB : 0 ≤ B)
    (h : exp (-(m : ℝ) ^ (5 / 2 : ℝ) - B * (m : ℝ) ^ 2) ≤ w ∧
      w ≤ exp (-(m : ℝ) ^ (5 / 2 : ℝ) + B * (m : ℝ) ^ 2)) :
    exp (-(n : ℝ) ^ (5 / 2 : ℝ) - (10 + 4 * B) * (n : ℝ) ^ 2) ≤ w ∧
      w ≤ exp (-(n : ℝ) ^ (5 / 2 : ℝ) + (10 + 4 * B) * (n : ℝ) ^ 2) := by
  have hs := morseChain_adjacent_sq_le hn hadj
  have hb := mul_le_mul_of_nonneg_left hs hB
  have hd := (abs_le.mp (morseChain_adjacent_rpow_diff_le hn hadj)).2
  refine ⟨(exp_le_exp.mpr (by nlinarith only [hb, hd])).trans h.1, ?_⟩
  exact h.2.trans (by simpa only [neg_one_mul, abs_of_nonneg hB] using
    morseChain_exp_jet_adjacent hn hadj (by norm_num : |(-1 : ℝ)| ≤ 1) B)

theorem morseChainA_inv_exp_le (T : Statements.MorseChainData) (n : ℕ)
    (hd : T.d n = morseChainInteger n) :
    (Statements.morseChainA T n)⁻¹ ≤ 3 * exp ((n : ℝ) ^ 2) := by
  have hlow := (morseChainA_exp_bounds T n hd).1
  have hp : 0 < exp (-(n : ℝ) ^ 2) / 3 := div_pos (exp_pos _) (by norm_num)
  calc
    _ ≤ (exp (-(n : ℝ) ^ 2) / 3)⁻¹ := (inv_le_inv₀ (hp.trans_le hlow) hp).mpr hlow
    _ = _ := by rw [inv_div, div_eq_mul_inv, ← exp_neg, neg_neg]

/-- A common fixed coefficient times the largest inverse-width exponential. -/
def morseChainJoinJetScale (c aLo sLo : ℝ) (n : ℕ) : ℝ :=
  (7 + sLo⁻¹ + 4 * (c * aLo)⁻¹ * 3 ^ 12) * exp (48 * (n : ℝ) ^ 2)

theorem morseChainJoinJetScale_bounds (T : Statements.MorseChainData)
    {n m : ℕ} (hn : 1 ≤ n) (hadj : m = n + 1 ∨ n = m + 1)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m)
    {c aLo sLo a sL sR : ℝ} (hc : 0 < c) (haLo : 0 < aLo) (hsLo : 0 < sLo)
    (ha : aLo ≤ a) (hsL : sLo ≤ sL) (hsR : sLo ≤ sR) :
    let ell := c * a * (min (Statements.morseChainA T n) (Statements.morseChainA T m)) ^ 12
    let D := morseChainJoinJetScale c aLo sLo n
    0 < ell ∧ 1 ≤ D ∧ sL⁻¹ ≤ D ∧ sR⁻¹ ≤ D ∧
      (Statements.morseChainA T n)⁻¹ ≤ D ∧ (Statements.morseChainA T m)⁻¹ ≤ D ∧
      (ell / 4)⁻¹ ≤ D ∧ ell⁻¹ ≤ D ∧ 6 * (n : ℝ) ^ 2 ≤ D := by
  dsimp only
  let A := Statements.morseChainA T n
  let B := Statements.morseChainA T m
  let M := min A B
  let ell := c * a * M ^ 12
  let E := exp (48 * (n : ℝ) ^ 2)
  let K : ℝ := 7 + sLo⁻¹ + 4 * (c * aLo)⁻¹ * 3 ^ 12
  have hA : 0 < A := (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
    (morseChainA_exp_bounds T n hdn).1
  have hB : 0 < B := (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
    (morseChainA_exp_bounds T m hdm).1
  have hM : 0 < M := lt_min hA hB
  have hca : 0 < c * a := mul_pos hc (haLo.trans_le ha)
  have hcLo : 0 < c * aLo := mul_pos hc haLo
  have hell : 0 < ell := mul_pos hca (pow_pos hM _)
  have hAi : A⁻¹ ≤ 3 * exp (4 * (n : ℝ) ^ 2) :=
    (morseChainA_inv_exp_le T n hdn).trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by nlinarith only [sq_nonneg (n : ℝ)])) (by norm_num))
  have hBi : B⁻¹ ≤ 3 * exp (4 * (n : ℝ) ^ 2) :=
    (morseChainA_inv_exp_le T m hdm).trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (morseChain_adjacent_sq_le hn hadj)) (by norm_num))
  have hMi : M⁻¹ ≤ 3 * exp (4 * (n : ℝ) ^ 2) := by
    rcases le_total A B with h | h
    · simpa only [M, min_eq_left h] using hAi
    · simpa only [M, min_eq_right h] using hBi
  have hM12 : M⁻¹ ^ 12 ≤ (3 : ℝ) ^ 12 * E := calc
    _ ≤ (3 * exp (4 * (n : ℝ) ^ 2)) ^ 12 := pow_le_pow_left₀ (inv_nonneg.mpr hM.le) hMi _
    _ = _ := by
      rw [mul_pow, ← exp_nat_mul, show ((12 : ℕ) : ℝ) * (4 * (n : ℝ) ^ 2) =
        48 * (n : ℝ) ^ 2 by norm_num only [Nat.cast_ofNat]; ring]
  have hellInv : ell⁻¹ ≤ ((c * aLo)⁻¹ * 3 ^ 12) * E := calc
    _ = (c * a)⁻¹ * M⁻¹ ^ 12 := by
      dsimp only [ell]
      rw [mul_inv_rev, inv_pow, mul_comm]
    _ ≤ (c * aLo)⁻¹ * (3 ^ 12 * E) :=
      mul_le_mul ((inv_le_inv₀ hca hcLo).mpr (mul_le_mul_of_nonneg_left ha hc.le))
        hM12 (pow_nonneg (inv_nonneg.mpr hM.le) _) (inv_nonneg.mpr hcLo.le)
    _ = _ := by ring
  have hE : 1 ≤ E := one_le_exp_iff.mpr (mul_nonneg (by norm_num) (sq_nonneg _))
  have hE₀ : 0 ≤ E := zero_le_one.trans hE
  have hS₀ : 0 ≤ sLo⁻¹ := inv_nonneg.mpr hsLo.le
  have hC₀ : 0 ≤ (c * aLo)⁻¹ * (3 : ℝ) ^ 12 := by positivity
  have h7 : (7 : ℝ) ≤ K := by dsimp only [K]; nlinarith only [hS₀, hC₀]
  have hKS : sLo⁻¹ ≤ K := by dsimp only [K]; nlinarith only [hC₀]
  have hKC : 4 * (c * aLo)⁻¹ * 3 ^ 12 ≤ K := by dsimp only [K]; linarith only [hS₀]
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 7).trans h7
  have hK1 : K ≤ K * E := le_mul_of_one_le_right hK hE
  have hAE : 3 * exp (4 * (n : ℝ) ^ 2) ≤ K * E := mul_le_mul
    ((by norm_num : (3 : ℝ) ≤ 7).trans h7)
    (exp_le_exp.mpr (by nlinarith only [sq_nonneg (n : ℝ)])) (exp_pos _).le hK
  have h4 : (ell / 4)⁻¹ ≤ K * E := calc
    _ = 4 * ell⁻¹ := by rw [inv_div, div_eq_mul_inv]
    _ ≤ 4 * (((c * aLo)⁻¹ * 3 ^ 12) * E) := mul_le_mul_of_nonneg_left hellInv (by norm_num)
    _ = (4 * (c * aLo)⁻¹ * 3 ^ 12) * E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hKC hE₀
  have hGap : 6 * (n : ℝ) ^ 2 ≤ K * E := calc
    _ ≤ 48 * (n : ℝ) ^ 2 := by nlinarith only [sq_nonneg (n : ℝ)]
    _ ≤ E := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    _ ≤ _ := le_mul_of_one_le_left hE₀ ((by norm_num : (1 : ℝ) ≤ 7).trans h7)
  change 0 < ell ∧ 1 ≤ K * E ∧ sL⁻¹ ≤ K * E ∧ sR⁻¹ ≤ K * E ∧ A⁻¹ ≤ K * E ∧
    B⁻¹ ≤ K * E ∧ (ell / 4)⁻¹ ≤ K * E ∧ ell⁻¹ ≤ K * E ∧ _
  exact ⟨hell, ((by norm_num : (1 : ℝ) ≤ 7).trans h7).trans hK1,
    ((inv_le_inv₀ (hsLo.trans_le hsL) hsLo).mpr hsL).trans (hKS.trans hK1),
    ((inv_le_inv₀ (hsLo.trans_le hsR) hsLo).mpr hsR).trans (hKS.trans hK1),
    hAi.trans hAE, hBi.trans hAE, h4,
    ((inv_le_inv₀ hell (div_pos hell (by norm_num))).mpr (by linarith only [hell])).trans h4, hGap⟩

private theorem morseChain_logabs_absorbs_constant {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc : 0 < c) (e : ℝ) :
    exp (e - |log c| * (n : ℝ) ^ 2) ≤ c * exp e ∧
      c * exp e ≤ exp (e + |log c| * (n : ℝ) ^ 2) := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₂ : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn₁
  have hlog := mul_le_mul_of_nonneg_left hn₂ (abs_nonneg (log c))
  rw [mul_one] at hlog
  have he : c * exp e = exp (log c + e) := by rw [exp_add, exp_log hc]
  rw [he]
  exact ⟨exp_le_exp.mpr (by linarith only [neg_abs_le (log c), hlog]),
    exp_le_exp.mpr (by linarith only [le_abs_self (log c), hlog])⟩

private theorem morseChainAmplitude_exp_band (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) {n : ℕ} (hn : 1 ≤ n) :
    exp (-(n : ℝ) ^ (5 / 2 : ℝ)) ≤ Statements.morseChainAmplitude T σ n ∧
      Statements.morseChainAmplitude T σ n ≤ exp (-(n : ℝ) ^ (5 / 2 : ℝ) + 2 * (n : ℝ) ^ 2) := by
  have hp := morseChainAmplitude_pos T σ hσ n
  have h := morseChainAmplitude_log_bounds T σ hσ n
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have h1 : ((n : ℝ) + 1) * log 2 ≤ ((n : ℝ) + 1) * 1 :=
    mul_le_mul_of_nonneg_left hlog (by linarith only [hn₁])
  have hn₂ : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    simpa only [pow_two, one_mul] using mul_le_mul_of_nonneg_right hn₁ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  refine ⟨(exp_le_exp.mpr h.1).trans_eq (exp_log hp), ?_⟩
  rw [← exp_log hp]
  apply exp_le_exp.mpr
  linarith only [h.2, h1, hn₁, hn₂]

theorem morseChain_model_height_exp_band {sLo sHi : ℝ} (hsLo : 0 < sLo) (hsHi : 0 < sHi) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (T : Statements.MorseChainData) (σ : ℕ → ℝ)
      (_hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) {n : ℕ}, 1 ≤ n → T.d n = morseChainInteger n →
      ∀ M : MorseJoinJetModel, M.A = Statements.morseChainA T n →
        M.amplitude = Statements.morseChainAmplitude T σ n →
        sLo ≤ M.scale → M.scale ≤ sHi → ∀ x ∈ M.image,
          exp (-(n : ℝ) ^ (5 / 2 : ℝ) - B * (n : ℝ) ^ 2) ≤ M.height x ∧
          M.height x ≤ exp (-(n : ℝ) ^ (5 / 2 : ℝ) + B * (n : ℝ) ^ 2) := by
  let c := sLo / (200 * (3 : ℝ) ^ 5)
  let C := 8 * sHi
  let B := 5 + |log c| + 2 + |log C|
  have hc : 0 < c := div_pos hsLo (by norm_num)
  have hC : 0 < C := mul_pos (by norm_num) hsHi
  refine ⟨B, by dsimp only [B]; positivity, ?_⟩
  intro T σ hσ n hn hdn M hMA hAmp hs₀ hs₁ x hx
  have hv (y : ℝ) (hy : y ∈ Ioo M.p M.q) : 0 < deriv M.radius y :=
    (div_pos (pow_pos M.hA 5) (by norm_num)).trans_le (M.hVelocity y hy)
  have hw := morseCellPhysicalHeight_value_bounds (lo := M.A ^ 5 / 200) (hi := 8)
    M.hpq.le M.hAmplitude M.hScale M.hSmooth hv
    (fun y hy => ⟨M.hVelocity y hy, (le_abs_self _).trans (M.hBound y (Ioo_subset_Icc_self hy)).2⟩)
    hx
  have hA : exp (-(n : ℝ) ^ 2) / 3 ≤ M.A := by
    rw [hMA]
    exact (morseChainA_exp_bounds T n hdn).1
  have hAmplitude := morseChainAmplitude_exp_band T σ hσ hn
  rw [← hAmp] at hAmplitude
  let p := (n : ℝ) ^ (5 / 2 : ℝ)
  let t := (n : ℝ) ^ 2
  have hscale : exp (-t) / 3 > 0 := div_pos (exp_pos _) (by norm_num)
  have hlo : c * exp (-p - 5 * t) ≤ M.height x := calc
    _ = exp (-p) * sLo * ((exp (-t) / 3) ^ 5 / 200) := by
      rw [div_pow, ← exp_nat_mul, show ((5 : ℕ) : ℝ) * -t = -(5 * t) by
          norm_num only [Nat.cast_ofNat]; ring,
        show -p - 5 * t = -p + -(5 * t) by ring, exp_add]
      dsimp only [c]
      ring
    _ ≤ M.amplitude * M.scale * (M.A ^ 5 / 200) := mul_le_mul
      (mul_le_mul hAmplitude.1 hs₀ hsLo.le M.hAmplitude.le)
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hscale.le hA 5) (by norm_num))
      (div_nonneg (pow_nonneg hscale.le 5) (by norm_num))
      (mul_nonneg M.hAmplitude.le M.hScale.le)
    _ ≤ _ := hw.1
  have hhi : M.height x ≤ C * exp (-p + 2 * t) := calc
    _ ≤ M.amplitude * M.scale * 8 := hw.2
    _ ≤ exp (-p + 2 * t) * sHi * 8 :=
      mul_le_mul_of_nonneg_right (mul_le_mul hAmplitude.2 hs₁ M.hScale.le (exp_pos _).le) (by norm_num)
    _ = _ := by dsimp only [C]; ring
  have hB₁ : 5 + |log c| ≤ B := by dsimp only [B]; linarith only [abs_nonneg (log C)]
  have hB₂ : 2 + |log C| ≤ B := by dsimp only [B]; linarith only [abs_nonneg (log c)]
  change exp (-p - B * t) ≤ M.height x ∧ M.height x ≤ exp (-p + B * t)
  constructor
  · calc
      _ ≤ exp (-p - 5 * t - |log c| * t) := exp_le_exp.mpr (by
        nlinarith only [mul_le_mul_of_nonneg_right hB₁ (sq_nonneg (n : ℝ))])
      _ ≤ c * exp (-p - 5 * t) := (morseChain_logabs_absorbs_constant hn hc _).1
      _ ≤ _ := hlo
  · calc
      _ ≤ C * exp (-p + 2 * t) := hhi
      _ ≤ exp (-p + 2 * t + |log C| * t) := (morseChain_logabs_absorbs_constant hn hC _).2
      _ ≤ _ := exp_le_exp.mpr (by
        nlinarith only [mul_le_mul_of_nonneg_right hB₂ (sq_nonneg (n : ℝ))])

private theorem chainRadialJet_eq_iteratedDeriv (k : ℕ) (f : ℝ → ℝ) :
    Statements.radialJet k f = iteratedDeriv k f := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Statements.radialJet, ih, iteratedDeriv_succ]

theorem morseChain_exp_inv_jet_le_radialE (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    exp ((n : ℝ) ^ (5 / 2 : ℝ) + B * (n : ℝ) ^ 2) ≤ Statements.radialE n ^ (1 + B) := by
  have hl : 1 ≤ log (exp 1 + n) := calc
    1 = log (exp 1) := (log_exp 1).symm
    _ ≤ _ := log_le_log (exp_pos 1) (le_add_of_nonneg_right (Nat.cast_nonneg n))
  have hp : (n : ℝ) ^ (5 / 2 : ℝ) ≤ Statements.radialQ n :=
    le_mul_of_one_le_right (Real.rpow_nonneg (Nat.cast_nonneg n) _) hl
  have hsq := mul_le_mul_of_nonneg_left (radial_nat_sq_le_Q n) hB
  rw [Statements.radialE, ← exp_mul]
  exact exp_le_exp.mpr (by nlinarith only [hp, hsq])

/-- The common constant convention in the radial coefficient specification,
together with the two-sided pointwise height band and the sharper inverse
exponential bound used when changing the block index. -/
def MorseChainJetBounds (n k : ℕ) (C : ℝ) (w : ℝ → ℝ) (x : ℝ) : Prop :=
  exp (-(n : ℝ) ^ (5 / 2 : ℝ) - C * (n : ℝ) ^ 2) ≤ w x ∧
  w x ≤ exp (-(n : ℝ) ^ (5 / 2 : ℝ) + C * (n : ℝ) ^ 2) ∧
  |Statements.radialJet k w x| ≤ C * exp (-(n : ℝ) ^ (5 / 2 : ℝ) + C * (n : ℝ) ^ 2) ∧
  |Statements.radialJet k w⁻¹ x| ≤ C * exp ((n : ℝ) ^ (5 / 2 : ℝ) + C * (n : ℝ) ^ 2) ∧
  |Statements.radialJet k w⁻¹ x| ≤ C * Statements.radialE n ^ C

theorem MorseChainJetBounds.mono {n k : ℕ} {C C' : ℝ} {w : ℝ → ℝ} {x : ℝ}
    (h : MorseChainJetBounds n k C w x) (hC : 0 ≤ C) (hCC' : C ≤ C') :
    MorseChainJetBounds n k C' w x := by
  have h' := hC.trans hCC'
  have ht := mul_le_mul_of_nonneg_right hCC' (sq_nonneg (n : ℝ))
  have hexp (a : ℝ) : exp (a + C * (n : ℝ) ^ 2) ≤ exp (a + C' * (n : ℝ) ^ 2) :=
    exp_le_exp.mpr (add_le_add le_rfl ht)
  have hE : 1 ≤ Statements.radialE n :=
    one_le_exp_iff.mpr ((sq_nonneg (n : ℝ)).trans (radial_nat_sq_le_Q n))
  obtain ⟨hlo, hhi, hW, hI, hIE⟩ := h
  exact ⟨(exp_le_exp.mpr (by linarith only [ht])).trans hlo, hhi.trans (hexp _),
    hW.trans (mul_le_mul hCC' (hexp _) (exp_pos _).le h'),
    hI.trans (mul_le_mul hCC' (hexp _) (exp_pos _).le h'),
    hIE.trans (mul_le_mul hCC' (Real.rpow_le_rpow_of_exponent_le hE hCC')
      (Real.rpow_nonneg (zero_le_one.trans hE) _) h')⟩

private theorem morseChainJetBounds_of_exp {n k : ℕ} {B P C : ℝ} {w : ℝ → ℝ} {x : ℝ}
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hBC : 1 + B ≤ C) (hPC : P ≤ C)
    (hlo : exp (-(n : ℝ) ^ (5 / 2 : ℝ) - B * (n : ℝ) ^ 2) ≤ w x)
    (hhi : w x ≤ exp (-(n : ℝ) ^ (5 / 2 : ℝ) + B * (n : ℝ) ^ 2))
    (hW : |iteratedDeriv k w x| ≤ P * exp (-(n : ℝ) ^ (5 / 2 : ℝ) + B * (n : ℝ) ^ 2))
    (hInv : |iteratedDeriv k w⁻¹ x| ≤ P * exp ((n : ℝ) ^ (5 / 2 : ℝ) + B * (n : ℝ) ^ 2)) :
    MorseChainJetBounds n k C w x := by
  have hC : 0 ≤ C := hP.trans hPC
  have hB' : B ≤ C := by linarith only [hBC]
  have h := mul_le_mul_of_nonneg_right hB' (sq_nonneg (n : ℝ))
  have hexp (a : ℝ) : exp (a + B * (n : ℝ) ^ 2) ≤ exp (a + C * (n : ℝ) ^ 2) :=
    exp_le_exp.mpr (add_le_add le_rfl h)
  have he1 : 1 ≤ Statements.radialE n :=
    one_le_exp_iff.mpr ((sq_nonneg (n : ℝ)).trans (radial_nat_sq_le_Q n))
  unfold MorseChainJetBounds
  rw [chainRadialJet_eq_iteratedDeriv, chainRadialJet_eq_iteratedDeriv]
  refine ⟨(exp_le_exp.mpr (by linarith only [h])).trans hlo, hhi.trans (hexp _),
    hW.trans (mul_le_mul hPC (hexp _) (exp_pos _).le hC),
    hInv.trans (mul_le_mul hPC (hexp _) (exp_pos _).le hC), ?_⟩
  exact hInv.trans (mul_le_mul hPC ((morseChain_exp_inv_jet_le_radialE n hB).trans
    (Real.rpow_le_rpow_of_exponent_le he1 hBC)) (exp_pos _).le hC)

theorem MorseChainJetBounds.adjacent {n m k : ℕ} {C : ℝ} {w : ℝ → ℝ} {x : ℝ}
    (h : MorseChainJetBounds m k C w x) (hn : 1 ≤ n)
    (hadj : m = n + 1 ∨ n = m + 1) (hC : 0 ≤ C) :
    MorseChainJetBounds n k (11 + 4 * C) w x := by
  obtain ⟨hlo, hhi, hW, hI, _⟩ := h
  rw [chainRadialJet_eq_iteratedDeriv] at hW hI
  have hb := morseChain_height_band_adjacent hn hadj hC ⟨hlo, hhi⟩
  refine morseChainJetBounds_of_exp (B := 10 + 4 * C) (P := C) (by positivity) hC
    (by linarith) (by linarith only [hC]) hb.1 hb.2 ?_ ?_
  · exact hW.trans (mul_le_mul_of_nonneg_left
      (by simpa only [neg_one_mul, abs_of_nonneg hC] using
        morseChain_exp_jet_adjacent hn hadj (by norm_num : |(-1 : ℝ)| ≤ 1) C) hC)
  · exact hI.trans (mul_le_mul_of_nonneg_left
      (by simpa only [one_mul, abs_of_nonneg hC] using
        morseChain_exp_jet_adjacent hn hadj (by norm_num : |(1 : ℝ)| ≤ 1) C) hC)

private theorem morseChain_exp_bound_of_relative {n k j : ℕ} {D K G B C W e : ℝ}
    {f : ℝ → ℝ} {x : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hScale : D ≤ K * exp (G * (n : ℝ) ^ 2)) (hW : W ≤ exp (e + B * (n : ℝ) ^ 2))
    (h : |iteratedDeriv k f x| ≤ C * W * D ^ j) :
    |iteratedDeriv k f x| ≤ C * K ^ j *
      exp (e + (B + G * j) * (n : ℝ) ^ 2) := by
  have hDj := pow_le_pow_left₀ hD hScale j
  have hE : (K * exp (G * (n : ℝ) ^ 2)) ^ j =
      K ^ j * exp ((G * j) * (n : ℝ) ^ 2) := by
    rw [mul_pow, ← exp_nat_mul,
      show (j : ℝ) * (G * (n : ℝ) ^ 2) = (G * j) * (n : ℝ) ^ 2 by ring]
  calc
    _ ≤ C * exp (e + B * (n : ℝ) ^ 2) * D ^ j :=
      h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hC) (pow_nonneg hD _))
    _ ≤ C * exp (e + B * (n : ℝ) ^ 2) * ((K * exp (G * (n : ℝ) ^ 2)) ^ j) :=
      mul_le_mul_of_nonneg_left hDj (mul_nonneg hC (exp_pos _).le)
    _ = C * K ^ j * (exp (e + B * (n : ℝ) ^ 2) * exp ((G * j) * (n : ℝ) ^ 2)) := by
      rw [hE]
      ring
    _ = _ := by
      rw [← exp_add, show e + B * (n : ℝ) ^ 2 + (G * j) * (n : ℝ) ^ 2 =
        e + (B + G * j) * (n : ℝ) ^ 2 by ring]

private theorem morseChain_jetBounds_of_relative {n k j : ℕ} {D K G B C U : ℝ}
    {w : ℝ → ℝ} {x : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hScale : D ≤ K * exp (G * (n : ℝ) ^ 2))
    (hU₁ : 1 + (B + G * j) ≤ U) (hU₂ : C * K ^ j ≤ U)
    (hlo : exp (-(n : ℝ) ^ (5 / 2 : ℝ) - B * (n : ℝ) ^ 2) ≤ w x)
    (hhi : w x ≤ exp (-(n : ℝ) ^ (5 / 2 : ℝ) + B * (n : ℝ) ^ 2))
    (hW : |iteratedDeriv k w x| ≤ C * w x * D ^ j)
    (hInv : |iteratedDeriv k w⁻¹ x| ≤ C * (w x)⁻¹ * D ^ j) :
    MorseChainJetBounds n k U w x := by
  have hp : 0 < w x := (exp_pos _).trans_le hlo
  have hinv : (w x)⁻¹ ≤ exp ((n : ℝ) ^ (5 / 2 : ℝ) + B * (n : ℝ) ^ 2) := calc
    _ ≤ (exp (-(n : ℝ) ^ (5 / 2 : ℝ) - B * (n : ℝ) ^ 2))⁻¹ :=
      (inv_le_inv₀ hp (exp_pos _)).mpr hlo
    _ = _ := by rw [← exp_neg]; congr 1; ring
  have hb₀ : 0 ≤ B + G * j := add_nonneg hB (mul_nonneg hG (Nat.cast_nonneg j))
  have hb : B * (n : ℝ) ^ 2 ≤ (B + G * j) * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hG (Nat.cast_nonneg j))) (sq_nonneg _)
  exact morseChainJetBounds_of_exp hb₀ (mul_nonneg hC (pow_nonneg hK _)) hU₁ hU₂
    ((exp_le_exp.mpr (by linarith only [hb])).trans hlo)
    (hhi.trans (exp_le_exp.mpr (by linarith only [hb])))
    (morseChain_exp_bound_of_relative hC hD hScale hhi hW)
    (morseChain_exp_bound_of_relative hC hD hScale hinv hInv)

private theorem exists_morseChainModel_relativeJets (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : MorseJoinJetModel) {D : ℝ},
      1 ≤ D → M.scale⁻¹ ≤ D → M.A⁻¹ ≤ D → ∀ x ∈ M.image,
      |iteratedDeriv k M.height x| ≤ C * M.height x * D ^ (5 + 11 * k) ∧
      |iteratedDeriv k M.height⁻¹ x| ≤ C * (M.height x)⁻¹ * D ^ (5 + 11 * k) := by
  obtain ⟨C, hC, h⟩ := exists_morseCellPhysicalJet_bound k
  refine ⟨200 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro M D hD hScale hA x hx
  let W := M.amplitude * M.scale
  let w := M.height x
  have hWp : 0 < W := mul_pos M.hAmplitude M.hScale
  have hv (y : ℝ) (hy : y ∈ Ioo M.p M.q) : 0 < deriv M.radius y :=
    (div_pos (pow_pos M.hA 5) (by norm_num)).trans_le (M.hVelocity y hy)
  have hV : 0 < M.A ^ 5 / 200 := div_pos (pow_pos M.hA 5) (by norm_num)
  have hvlohi : W * (M.A ^ 5 / 200) ≤ w ∧ w ≤ W * 8 :=
    morseCellPhysicalHeight_value_bounds M.hpq.le M.hAmplitude M.hScale M.hSmooth hv
      (fun y hy => ⟨M.hVelocity y hy, (le_abs_self _).trans (M.hBound y (Ioo_subset_Icc_self hy)).2⟩) hx
  have hwp : 0 < w := (mul_pos hWp hV).trans_le hvlohi.1
  have hratio : W ≤ 200 * w * M.A⁻¹ ^ 5 := calc
    _ ≤ w / (M.A ^ 5 / 200) := (le_div_iff₀ hV).mpr hvlohi.1
    _ = _ := by rw [div_eq_mul_inv, inv_div, div_eq_mul_inv, inv_pow]; ring
  have hratioInv : W⁻¹ ≤ 200 * w⁻¹ := calc
    _ ≤ (w / 8)⁻¹ := (inv_le_inv₀ hWp (div_pos hwp (by norm_num))).mpr
      ((div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr hvlohi.2)
    _ = 8 * w⁻¹ := by rw [inv_div, div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hwp.le)
  have hs₀ : 0 ≤ M.scale⁻¹ := inv_nonneg.mpr M.hScale.le
  have hA₀ : 0 ≤ M.A⁻¹ := inv_nonneg.mpr M.hA.le
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hpow : M.scale⁻¹ ^ k * M.A⁻¹ ^ (5 + 10 * k) ≤ D ^ (5 + 11 * k) := calc
    _ ≤ D ^ k * D ^ (5 + 10 * k) := mul_le_mul (pow_le_pow_left₀ hs₀ hScale _)
      (pow_le_pow_left₀ hA₀ hA _) (pow_nonneg hA₀ _) (pow_nonneg hD₀ _)
    _ = _ := by rw [← pow_add, show k + (5 + 10 * k) = 5 + 11 * k by omega]
  have hraw := h M.hA M.hA₁ M.hB M.hBA M.hpq M.hSmooth M.hExp M.hBound M.hEquation
    M.hVelocity M.hAmplitude M.hScale x hx
  constructor
  · calc
      _ ≤ C * W * (M.scale⁻¹ ^ k * M.A⁻¹ ^ (10 * k)) := hraw.1.trans_eq (mul_assoc _ _ _)
      _ ≤ C * (200 * w * M.A⁻¹ ^ 5) * (M.scale⁻¹ ^ k * M.A⁻¹ ^ (10 * k)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC)
          (mul_nonneg (pow_nonneg hs₀ _) (pow_nonneg hA₀ _))
      _ = 200 * C * w * (M.scale⁻¹ ^ k * M.A⁻¹ ^ (5 + 10 * k)) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg (by norm_num) hC) hwp.le)
  · calc
      _ ≤ C * W⁻¹ * (M.scale⁻¹ ^ k * M.A⁻¹ ^ (5 + 10 * k)) := hraw.2.trans_eq (mul_assoc _ _ _)
      _ ≤ C * (200 * w⁻¹) * (M.scale⁻¹ ^ k * M.A⁻¹ ^ (5 + 10 * k)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratioInv hC)
          (mul_nonneg (pow_nonneg hs₀ _) (pow_nonneg hA₀ _))
      _ = 200 * C * w⁻¹ * (M.scale⁻¹ ^ k * M.A⁻¹ ^ (5 + 10 * k)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (mul_nonneg (by norm_num) hC) (inv_nonneg.mpr hwp.le))

/-- The complete model-piece bounds, uniform over all admissible amplitude
choices and all radius scales in a fixed positive interval. -/
theorem exists_morseChainModel_jetBounds {sLo sHi : ℝ} (hsLo : 0 < sLo) (hsHi : 0 < sHi) (k : ℕ) :
    ∃ U : ℝ, 0 < U ∧ ∀ (T : Statements.MorseChainData) (σ : ℕ → ℝ)
      (_hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) {n : ℕ}, 1 ≤ n → T.d n = morseChainInteger n →
      ∀ M : MorseJoinJetModel, M.A = Statements.morseChainA T n →
        M.amplitude = Statements.morseChainAmplitude T σ n →
        sLo ≤ M.scale → M.scale ≤ sHi → ∀ x ∈ M.image, MorseChainJetBounds n k U M.height x := by
  obtain ⟨B, hB, hband⟩ := morseChain_model_height_exp_band hsLo hsHi
  obtain ⟨C, hC, hrel⟩ := exists_morseChainModel_relativeJets k
  let K : ℝ := 3 + sLo⁻¹
  let j := 5 + 11 * k
  have hsi : 0 ≤ sLo⁻¹ := inv_nonneg.mpr hsLo.le
  have hK : 0 ≤ K := add_nonneg (by norm_num) hsi
  let U := 1 + (B + (j : ℝ)) + C * K ^ j
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hP : 0 ≤ C * K ^ j := mul_nonneg hC (pow_nonneg hK _)
  refine ⟨U, by dsimp only [U]; linarith only [hB, hj, hP], ?_⟩
  intro T σ hσ n hn hd M hMA hAmp hs₀ hs₁ x hx
  let E := exp ((n : ℝ) ^ 2)
  let D := K * E
  have hE : 1 ≤ E := one_le_exp_iff.mpr (sq_nonneg _)
  have hK' : K ≤ D := le_mul_of_one_le_right hK hE
  have hD : 1 ≤ D := (show 1 ≤ K by dsimp only [K]; linarith only [hsi]).trans hK'
  have hA : M.A⁻¹ ≤ D := by
    rw [hMA]
    exact (morseChainA_inv_exp_le T n hd).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hsi) (exp_pos _).le)
  have hS : M.scale⁻¹ ≤ D := ((inv_le_inv₀ M.hScale hsLo).mpr hs₀).trans
    ((le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3)).trans hK')
  obtain ⟨hlo, hhi⟩ := hband T σ hσ hn hd M hMA hAmp hs₀ hs₁ x hx
  obtain ⟨hw, hi⟩ := hrel M hD hS hA x hx
  exact morseChain_jetBounds_of_relative (G := 1) hC (zero_le_one.trans hD) hK zero_le_one hB
    (by rw [one_mul])
    (by dsimp only [U]; linarith only [hP]) (by dsimp only [U]; linarith only [hB, hj])
    hlo hhi hw hi

private theorem morseChainJoin_logGap_bounds (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) {n m : ℕ} (hn : 100 ≤ n)
    (hNn : T.index ≤ n) (hNm : T.index ≤ m) (hadj : m = n + 1 ∨ n = m + 1)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m)
    (L R : MorseJoinJetModel) (hAn : L.A = Statements.morseChainA T n)
    (hAm : R.A = Statements.morseChainA T m)
    (hAmpL : L.amplitude = Statements.morseChainAmplitude T σ n)
    (hAmpR : R.amplitude = Statements.morseChainAmplitude T σ m)
    {c xL xR : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (hxL : xL ∈ Ioo L.p L.q) (hxR : xR ∈ Ioo R.p R.q)
    (hrL : 1 / 2 ≤ L.radius xL ∧ L.radius xL ≤ 2)
    (hrR : 1 / 2 ≤ R.radius xR ∧ R.radius xR ≤ 2)
    (hvL : (1 / 100 : ℝ) * L.A ^ 5 ≤ deriv L.radius xL ∧
      deriv L.radius xL ≤ (3 / 100 : ℝ) * L.A ^ 5)
    (hvR : R.A / 4 ≤ deriv R.radius xR ∧ deriv R.radius xR ≤ 7 * R.A)
    {FL FR : ℝ → ℝ} :
    let a := L.scale * L.radius xL
    let b := R.scale * R.radius xR
    b - a = c * a * (min L.A R.A) ^ 12 →
    FL =ᶠ[𝓝 a] L.logProfile → FR =ᶠ[𝓝 b] R.logProfile →
    2 * (n : ℝ) ^ 2 ≤ FR b - FL a ∧ FR b - FL a ≤ 6 * (n : ℝ) ^ 2 := by
  dsimp only
  intro hPlace hLg hRg
  let ε := c * (min L.A R.A) ^ 12
  have hMin₀ : 0 ≤ min L.A R.A := le_min L.hA.le R.hA.le
  have hMin₁ : min L.A R.A ≤ 1 := (min_le_left _ _).trans L.hA₁
  have hε : 0 ≤ ε ∧ ε ≤ 1 := ⟨mul_nonneg hc.le (pow_nonneg hMin₀ _), by
    calc
      ε ≤ (1 : ℝ) * 1 ^ 12 := mul_le_mul hc₁ (pow_le_pow_left₀ hMin₀ hMin₁ 12)
        (pow_nonneg hMin₀ _) zero_le_one
      _ = _ := by norm_num⟩
  have hmatch : R.scale * R.radius xR = L.scale * L.radius xL * (1 + ε) := by
    calc
      _ = L.scale * L.radius xL + (R.scale * R.radius xR - L.scale * L.radius xL) := by ring
      _ = _ := by rw [hPlace]; dsimp only [ε]; ring
  have hRatio := morseJoin_scaleRatio_log_bound L.hScale R.hScale hrL hrR hε hmatch
  have hContrast := morseJoin_height_log_contrast (vn := deriv L.radius xL) (vm := deriv R.radius xR)
    T σ hσ (by omega : 1 ≤ n)
    hNn hNm hadj hdn hdm L.hScale R.hScale hRatio
    (by simpa only [hAn] using hvL) (by simpa only [hAm] using hvR)
  have hL (t : ℝ) (ht : t ∈ Ioo L.p L.q) : 0 < deriv L.radius t :=
    (div_pos (pow_pos L.hA 5) (by norm_num)).trans_le (L.hVelocity t ht)
  have hR (t : ℝ) (ht : t ∈ Ioo R.p R.q) : 0 < deriv R.radius t :=
    (div_pos (pow_pos R.hA 5) (by norm_num)).trans_le (R.hVelocity t ht)
  rw [hLg.eq_of_nhds, hRg.eq_of_nhds]
  unfold MorseJoinJetModel.logProfile
  rw [morseCollarLogProfile_at_model R.hScale R.hSmooth hR hxR,
    morseCollarLogProfile_at_model L.hScale L.hSmooth hL hxL, hAmpL, hAmpR,
    ← log_div hContrast.2.1.ne' hContrast.1.ne']
  exact hContrast.2.2.2 hn

/-- The fixed-order bounds for the actual adjacent Morse connector. Its
widths are one fourth of the true join length and its gap is the actual
endpoint height contrast. The chosen smooth extensions keep the two
model germs on the closed support collars. -/
theorem exists_morseChainJoin_jetBounds {c aLo sLo sHi : ℝ}
    (hc : 0 < c) (hc₁ : c ≤ 1) (haLo : 0 < aLo) (hsLo : 0 < sLo) (hsHi : 0 < sHi) (k : ℕ) :
    ∃ U : ℝ, 0 < U ∧ ∀ (T : Statements.MorseChainData) (σ : ℕ → ℝ)
      (_hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) {n m : ℕ}, 100 ≤ n →
      T.index ≤ n → T.index ≤ m → (m = n + 1 ∨ n = m + 1) →
      T.d n = morseChainInteger n → T.d m = morseChainInteger m →
      ∀ (L R : MorseJoinJetModel), L.A = Statements.morseChainA T n →
        R.A = Statements.morseChainA T m →
        L.amplitude = Statements.morseChainAmplitude T σ n →
        R.amplitude = Statements.morseChainAmplitude T σ m →
        sLo ≤ L.scale → L.scale ≤ sHi → sLo ≤ R.scale → R.scale ≤ sHi →
        ∀ {xL xR : ℝ}, xL ∈ Ioo L.p L.q → xR ∈ Ioo R.p R.q →
        (1 / 2 ≤ L.radius xL ∧ L.radius xL ≤ 2) →
        (1 / 2 ≤ R.radius xR ∧ R.radius xR ≤ 2) →
        ((1 / 100 : ℝ) * L.A ^ 5 ≤ deriv L.radius xL ∧
          deriv L.radius xL ≤ (3 / 100 : ℝ) * L.A ^ 5) →
        (R.A / 4 ≤ deriv R.radius xR ∧ deriv R.radius xR ≤ 7 * R.A) →
        let a := L.scale * L.radius xL
        let b := R.scale * R.radius xR
        let ell := c * a * (min L.A R.A) ^ 12
        let h := ell / 4
        aLo ≤ a → b - a = ell →
        ∀ (FL FR : ℝ → ℝ), ContDiff ℝ ∞ FL → ContDiff ℝ ∞ FR →
          Icc a (a + h) ⊆ L.image → Icc (b - h) b ⊆ R.image →
          (∀ x ∈ Icc a (a + h), FL =ᶠ[𝓝 x] L.logProfile) →
          (∀ x ∈ Icc (b - h) b, FR =ᶠ[𝓝 x] R.logProfile) →
          (∀ x ∈ Icc a (a + h), 2 / a ≤ deriv FL x) →
          (∀ x ∈ Icc (b - h) b, 2 / a ≤ deriv FR x) →
          MorseJoinBudget a b h h (2 / a) FL FR →
          ∀ x ∈ Icc a b, MorseChainJetBounds n k U (morseJoinProfile a b h h FL FR) x := by
  obtain ⟨B, hB, hband⟩ := morseChain_model_height_exp_band hsLo hsHi
  obtain ⟨C, hC, hrel⟩ := exists_morseJoin_modelPhysicalJet_bound k
  let K : ℝ := 7 + sLo⁻¹ + 4 * (c * aLo)⁻¹ * 3 ^ 12
  let j : ℕ := 16 * k
  let G : ℝ := 10 + 4 * B
  let U : ℝ := 1 + (G + 48 * (j : ℝ)) + C * K ^ j
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; linarith only [hB]
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hP : 0 ≤ C * K ^ j := mul_nonneg hC (pow_nonneg hK _)
  refine ⟨U, by dsimp only [U]; linarith only [hG, hj, hP], ?_⟩
  intro T σ hσ n m hn hNn hNm hadj hdn hdm L R hAn hAm hAmpL hAmpR
    hsL₀ hsL₁ hsR₀ hsR₁ xL xR hxL hxR hrL hrR hvL hvR
  dsimp only
  intro ha hPlace FL FR hFL hFR hLsub hRsub hLg hRg hFloorL hFloorR hBudget x hx
  let a := L.scale * L.radius xL
  let b := R.scale * R.radius xR
  let ell := c * a * (min L.A R.A) ^ 12
  let h := ell / 4
  let D := morseChainJoinJetScale c aLo sLo n
  have hn₁ : 1 ≤ n := by omega
  have hm₁ : 1 ≤ m := by rcases hadj with ht | ht <;> omega
  have hs := morseChainJoinJetScale_bounds T hn₁ hadj hdn hdm hc haLo hsLo ha hsL₀ hsR₀
  rw [← hAn, ← hAm] at hs
  obtain ⟨hell, hD, hSL, hSR, hAL, hAR, hWidth, hSpan, hGapD⟩ := hs
  have hh : 0 < h := div_pos hell (by norm_num)
  have hab : a < b := sub_pos.mp (show 0 < b - a from hPlace.symm ▸ hell)
  have hLa : a ∈ Icc a (a + h) := ⟨le_rfl, le_add_of_nonneg_right hh.le⟩
  have hRb : b ∈ Icc (b - h) b := ⟨sub_le_self _ hh.le, le_rfl⟩
  have hGap := (morseChainJoin_logGap_bounds T σ hσ hn hNn hNm hadj hdn hdm
    L R hAn hAm hAmpL hAmpR hc hc₁ hxL hxR hrL hrR hvL hvR hPlace (hLg a hLa) (hRg b hRb)).2
  let J : MorseJoinJetData :=
    { a := a, b := b, hL := h, hR := h, D := D, m := 2 / a, FL := FL, FR := FR
      hab := hab, hWidthL := hh, hWidthR := hh
      hWidths := by change ell / 4 + ell / 4 ≤ (b - a) / 2; rw [hPlace]; linarith
      hD := hD, hInvL := hWidth, hInvR := hWidth
      hInvSpan := by rw [hPlace]; exact hSpan
      hGap := hGap.trans hGapD, hm := div_nonneg (by norm_num) (haLo.le.trans ha)
      hSmoothL := hFL, hSmoothR := hFR, hFloorL := hFloorL, hFloorR := hFloorR
      hBudget := hBudget }
  obtain ⟨hw, hi⟩ := hrel J L R hSL hAL hSR hAR hLsub hRsub hLg hRg x hx
  have hWL := hband T σ hσ hn₁ hdn L hAn hAmpL hsL₀ hsL₁ a (hLsub hLa)
  have hWR := hband T σ hσ hm₁ hdm R hAm hAmpR hsR₀ hsR₁ b (hRsub hRb)
  have hWR' := morseChain_height_band_adjacent hn₁ hadj hB hWR
  have hBetween := J.height_between_models L R hLsub hRsub hLg hRg x hx
  have hGB : B ≤ G := by dsimp only [G]; linarith only [hB]
  have hExpLo : exp (-(n : ℝ) ^ (5 / 2 : ℝ) - G * (n : ℝ) ^ 2) ≤ J.height x := calc
    _ ≤ exp (-(n : ℝ) ^ (5 / 2 : ℝ) - B * (n : ℝ) ^ 2) :=
      exp_le_exp.mpr (by linarith only [mul_le_mul_of_nonneg_right hGB (sq_nonneg (n : ℝ))])
    _ ≤ L.height a := hWL.1
    _ ≤ _ := hBetween.1
  change MorseChainJetBounds n k U J.height x
  exact morseChain_jetBounds_of_relative (G := 48) hC (zero_le_one.trans hD) hK (by norm_num) hG
    (le_refl (K * exp (48 * (n : ℝ) ^ 2)))
    (by dsimp only [U]; linarith only [hP]) (by dsimp only [U]; linarith only [hG, hj])
    hExpLo (hBetween.2.trans hWR'.2) hw hi

end ContinuousFlexibility.Radial
