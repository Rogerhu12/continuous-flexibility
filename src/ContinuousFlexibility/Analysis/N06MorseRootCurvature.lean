import ContinuousFlexibility.Radial.MorseModelReturn

/-!
# Quantitative curvature of the actual Morse turning roots

The two roots are treated by their common zero-set equation. The actual
integer choices give a uniform lower bound for the derivative of the Morse
coefficient. Differentiating the already proved physical profile identity
then identifies the ordinary second derivative of the same realized profile.

The final coefficient-power lower bound uses only a realized Morse chain,
its actual amplitude choices, and the original smooth physical profile. It
does not assume a canonical coordinate bound. The frozen `IsRadialReference`
predicate alone does not retain the Morse-realization premise used here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Both actual coefficient roots have a derivative bounded below by half
the smaller Morse parameter. -/
theorem n06_morseRho_root_deriv_lower {A B x : ℝ}
    (hB : 0 < B) (h8 : 8 * B ≤ A) (hx : morseRho A B x = 0) :
    B / 2 ≤ |deriv (morseRho A B) x| := by
  have hA : 0 < A := (mul_pos (by norm_num : (0 : ℝ) < 8) hB).trans_le h8
  have h4 : 4 * B < A := by linarith only [hB, h8]
  have hq : B / A ≤ 1 / 8 := (div_le_iff₀ hA).mpr (by linarith only [h8])
  have hs : (1 / 2 : ℝ) ≤ sqrt (1 - 4 * B / A) := by
    apply Real.le_sqrt_of_sq_le
    rw [show 4 * B / A = 4 * (B / A) by ring]
    nlinarith only [hq]
  have ht : B / A ≤ exp (-x) := by
    rcases (morseRho_zero_iff_turn hB h4 x).mp hx with rfl | rfl
    · rw [exp_neg_morseLeftTurn hB h4]
      exact hq.trans ((by norm_num : (1 / 8 : ℝ) ≤ 1 / 2).trans
        (morseRootT_bounds hB h4).2.2.1.le)
    · rw [exp_neg_morseRightTurn hB h4]
      exact (morseRightRootT_ratio_bounds hB h4).1
  have habs : |2 * exp (-x) - 1| = sqrt (1 - 4 * B / A) := by
    rcases (morseRho_zero_iff_turn hB h4 x).mp hx with rfl | rfl
    · rw [exp_neg_morseLeftTurn hB h4]
      have he : 2 * morseLeftRootT A B - 1 = sqrt (1 - 4 * B / A) := by
        unfold morseLeftRootT
        ring
      rw [he, abs_of_nonneg (sqrt_nonneg _)]
    · rw [exp_neg_morseRightTurn hB h4]
      have he : 2 * morseRightRootT A B - 1 = -sqrt (1 - 4 * B / A) := by
        unfold morseRightRootT
        ring
      rw [he, abs_neg, abs_of_nonneg (sqrt_nonneg _)]
  rw [(hasDerivAt_morseRho A B x).deriv, abs_mul, abs_mul,
    abs_of_pos hA, abs_of_pos (exp_pos _), habs]
  calc
    B / 2 = A * ((B / A) * (1 / 2)) := by field_simp [hA.ne']
    _ ≤ A * (exp (-x) * sqrt (1 - 4 * B / A)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul ht hs (by norm_num) (exp_pos _).le) hA.le

/-- The actual least-nonsquare parameters satisfy the stronger separation
needed for the common two-root estimate. -/
theorem n06_morseChain_eight_mul_B_le_A (T : MorseChainData) (n : ℕ)
    (hd : 2 ≤ (T.d n : ℝ)) : 8 * morseChainB T n ≤ morseChainA T n := by
  have hd1 : 1 ≤ (T.d n : ℝ) := (by norm_num : (1 : ℝ) ≤ 2).trans hd
  have hp : 0 < (T.d n : ℝ) := zero_lt_one.trans_le hd1
  have hi : 0 ≤ (T.d n : ℝ)⁻¹ := inv_nonneg.mpr hp.le
  have hhalf : (T.d n : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hd
  rw [morseChainB_inv_pow T n hp.le]
  calc
    8 * ((T.d n : ℝ)⁻¹) ^ 9 =
        (T.d n : ℝ)⁻¹ * (8 * ((T.d n : ℝ)⁻¹) ^ 8) := by ring
    _ ≤ (T.d n : ℝ)⁻¹ * (8 * (1 / 2 : ℝ) ^ 8) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hi hhalf 8) (by norm_num)) hi
    _ ≤ (T.d n : ℝ)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (by norm_num) hi
    _ = (T.d n : ℝ)⁻¹ := mul_one _
    _ ≤ morseChainA T n := (morseChainA_inv_bounds T n hd1).1

/-- Either root lies strictly inside the actual retained model interval. -/
theorem n06_morseRealization_root_mem_Ioo
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) {x : ℝ}
    (hx : morseRho (morseChainA T n) (morseChainB T n) x = 0) :
    x ∈ Ioo (T.leftX side n) (T.rightX side n) := by
  have hp := hreal.retained_data side n hn
  obtain ⟨hl, hlr, hr⟩ := morseRealization_turns_retained hreal side hn
  rcases (morseRho_zero_iff_turn hp.1 hp.2.1 x).mp hx with rfl | rfl
  · exact ⟨hl, hlr.trans hr⟩
  · exact ⟨hl.trans hlr, hr⟩

/-- Differentiating the literal identity for the same physical profile gives
its true root curvature. No pointwise derivative of an unrelated model is
substituted for `D.w`. -/
theorem n06_morseRealization_profile_second_deriv_at_root
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) {x : ℝ}
    (hx : morseRho (morseChainA T n) (morseChainB T n) x = 0) :
    deriv (deriv D.w) (T.radius side n x) =
      -morseChainAmplitude T σ n *
        deriv (morseRho (morseChainA T n) (morseChainB T n)) x * T.radius side n x /
          deriv (T.radius side n) x ^ 2 := by
  let R : ℝ → ℝ := T.radius side n
  let ρ : ℝ → ℝ := morseRho (morseChainA T n) (morseChainB T n)
  let lam : ℝ := morseChainAmplitude T σ n
  have hxi := n06_morseRealization_root_mem_Ioo hreal side hn hx
  have hxc : x ∈ Icc (T.leftX side n) (T.rightX side n) := ⟨hxi.1.le, hxi.2.le⟩
  have hw : ContDiff ℝ ∞ D.w := hreal.geometry.2.2.1.1
  have hwd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hR : ContDiff ℝ ∞ R := hreal.radius_smooth side n hn
  have hRd : ContDiff ℝ ∞ (deriv R) := (contDiff_infty_iff_deriv.mp hR).2
  have hρ : ContDiff ℝ ∞ ρ := contDiff_morseRho _ _
  have hρ0 : ρ x = 0 := hx
  have hR₂ : deriv (deriv R) x = 0 := by
    change deriv (deriv (T.radius side n)) x = 0
    rw [hreal.equation side n hn x hxc, hx, neg_zero, zero_mul]
  have hv : 0 < deriv R x := hreal.derivative_positive side n hn x hxc
  have hfg : (fun t => deriv D.w (R t) * deriv R t) =ᶠ[𝓝 x]
      (fun t => lam * (-ρ t * R t)) := by
    filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with t ht
    exact morseRealization_profile_deriv_scaled hreal side hn ⟨ht.1.le, ht.2.le⟩
  have hf : HasDerivAt (fun t => deriv D.w (R t) * deriv R t)
      ((deriv (deriv D.w) (R x) * deriv R x) * deriv R x +
        deriv D.w (R x) * deriv (deriv R) x) x :=
    (((hwd.differentiable (by simp) (R x)).hasDerivAt.comp x
      (hR.differentiable (by simp) x).hasDerivAt).mul
      (hRd.differentiable (by simp) x).hasDerivAt)
  have hg : HasDerivAt (fun t => lam * (-ρ t * R t))
      (lam * (-deriv ρ x * R x + -ρ x * deriv R x)) x :=
    (((hρ.differentiable (by simp) x).hasDerivAt.neg.mul
      (hR.differentiable (by simp) x).hasDerivAt).const_mul lam)
  have he := hf.deriv.symm.trans (hfg.deriv_eq.trans hg.deriv)
  simp only [hR₂, hρ0, neg_zero, zero_mul, mul_zero, add_zero] at he
  change deriv (deriv D.w) (R x) = -lam * deriv ρ x * R x / deriv R x ^ 2
  apply (eq_div_iff (pow_ne_zero 2 hv.ne')).mpr
  calc
    deriv (deriv D.w) (R x) * deriv R x ^ 2 =
        (deriv (deriv D.w) (R x) * deriv R x) * deriv R x := by ring
    _ = lam * (-deriv ρ x * R x) := he
    _ = -lam * deriv ρ x * R x := by ring

/-- The actual amplitude and smaller coefficient have a fixed inverse
polynomial lower bound in the prescribed reference coefficient. -/
theorem n06_morseChain_amplitude_cubic_lower
    (T : MorseChainData) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (n : ℕ) (hd : T.d n = morseChainInteger n) :
    ((3 : ℝ) ^ 9)⁻¹ * radialE n ^ (-12 : ℝ) ≤
      morseChainAmplitude T σ n ^ 3 * morseChainB T n := by
  have hE : 0 < radialE n := exp_pos _
  have hE0 : 0 ≤ (radialE n)⁻¹ := inv_nonneg.mpr hE.le
  have hlog : 1 ≤ log (exp 1 + (n : ℝ)) := calc
    1 = log (exp 1) := (log_exp 1).symm
    _ ≤ log (exp 1 + (n : ℝ)) :=
      log_le_log (exp_pos _) (le_add_of_nonneg_right (Nat.cast_nonneg n))
  have hp : (n : ℝ) ^ (5 / 2 : ℝ) ≤ radialQ n :=
    le_mul_of_one_le_right (Real.rpow_nonneg (Nat.cast_nonneg n) _) hlog
  have hlam : (radialE n)⁻¹ ≤ morseChainAmplitude T σ n := by
    calc
      (radialE n)⁻¹ = exp (-radialQ n) := (exp_neg _).symm
      _ ≤ exp (-(n : ℝ) ^ (5 / 2 : ℝ)) := exp_le_exp.mpr (neg_le_neg hp)
      _ ≤ morseChainAmplitude T σ n := (morseChainAmplitude_bounds T σ hσ n).1
  have hd2 : (2 : ℝ) ≤ T.d n := by
    rw [hd]
    exact_mod_cast morseChainInteger_ge_two n
  have hdp : 0 < (T.d n : ℝ) := (by norm_num : (0 : ℝ) < 2).trans_le hd2
  have hdU : (T.d n : ℝ) ≤ 3 * radialE n := by
    have hi : (T.d n : ℝ) < exp ((n : ℝ) ^ 2) + 2 := by
      rw [hd]
      exact morseChainInteger_lt n
    have he1 : 1 ≤ exp ((n : ℝ) ^ 2) := one_le_exp_iff.mpr (sq_nonneg _)
    have he : exp ((n : ℝ) ^ 2) ≤ radialE n :=
      exp_le_exp.mpr (radial_nat_sq_le_Q n)
    linarith only [hi, he1, he]
  have hdi : (3 * radialE n)⁻¹ ≤ (T.d n : ℝ)⁻¹ := inv_anti₀ hdp hdU
  have hB : ((3 : ℝ) ^ 9)⁻¹ * ((radialE n)⁻¹) ^ 9 ≤ morseChainB T n := by
    rw [morseChainB_inv_pow T n hdp.le]
    calc
      ((3 : ℝ) ^ 9)⁻¹ * ((radialE n)⁻¹) ^ 9 = ((3 * radialE n)⁻¹) ^ 9 := by
        rw [mul_inv_rev, mul_pow, inv_pow]
        ring
      _ ≤ ((T.d n : ℝ)⁻¹) ^ 9 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (mul_nonneg (by norm_num) hE.le)) hdi 9
  have hlam3 : ((radialE n)⁻¹) ^ 3 ≤ morseChainAmplitude T σ n ^ 3 :=
    pow_le_pow_left₀ hE0 hlam 3
  have hpow : radialE n ^ (-12 : ℝ) = ((radialE n)⁻¹) ^ 12 := by
    rw [show (-12 : ℝ) = -((12 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hE.le, Real.rpow_natCast, inv_pow]
  rw [hpow]
  calc
    ((3 : ℝ) ^ 9)⁻¹ * ((radialE n)⁻¹) ^ 12 =
        ((radialE n)⁻¹) ^ 3 * (((3 : ℝ) ^ 9)⁻¹ * ((radialE n)⁻¹) ^ 9) := by ring
    _ ≤ morseChainAmplitude T σ n ^ 3 * morseChainB T n :=
      mul_le_mul hlam3 hB (by positivity)
        (pow_nonneg (morseChainAmplitude_pos T σ hσ n).le 3)

/-- Uniform physical root curvature for both tails and both turning roots
of the same realized chain. The constant is selected before every model
index. No canonical primitive estimate is an input. -/
theorem n06_morseRealization_root_curvature_lower
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (side : Bool) (n : ℕ), T.index ≤ n → ∀ x : ℝ,
      morseRho (morseChainA T n) (morseChainB T n) x = 0 →
      c * radialE n ^ (-12 : ℝ) ≤
        |deriv (deriv D.w) (T.radius side n x)| := by
  have hw : ContDiff ℝ ∞ D.w := hreal.geometry.2.2.1.1
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hw.continuous.continuousOn : ContinuousOn D.w (Icc D.a D.b))
  let M : ℝ := max M₀ 1
  have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
  have ha : 0 < D.a := hreal.geometry.1
  let c : ℝ := (D.a / (2 * M ^ 2)) * ((3 : ℝ) ^ 9)⁻¹
  refine ⟨c, mul_pos (div_pos ha (mul_pos (by norm_num) (sq_pos_of_pos hM)))
    (inv_pos.mpr (by norm_num)), ?_⟩
  intro side n hn x hx
  let R : ℝ → ℝ := T.radius side n
  let lam : ℝ := morseChainAmplitude T σ n
  let ρ : ℝ → ℝ := morseRho (morseChainA T n) (morseChainB T n)
  have hxi := n06_morseRealization_root_mem_Ioo hreal side hn hx
  have hxc : x ∈ Icc (T.leftX side n) (T.rightX side n) := ⟨hxi.1.le, hxi.2.le⟩
  have hr := hreal.radius_mem_core side n hn x hxc
  have hrp : 0 < R x := ha.trans hr.1
  have hlam : 0 < lam := morseChainAmplitude_pos T σ hσ n
  have hv : 0 < deriv R x := hreal.derivative_positive side n hn x hxc
  have hd2 : (2 : ℝ) ≤ T.d n := by
    rw [hreal.d_eq n hn]
    exact_mod_cast morseChainInteger_ge_two n
  have hB : 0 < morseChainB T n := (hreal.retained_data side n hn).1
  have hρ : morseChainB T n / 2 ≤ |deriv ρ x| :=
    n06_morseRho_root_deriv_lower hB (n06_morseChain_eight_mul_B_le_A T n hd2) hx
  have hcurv : deriv (deriv D.w) (R x) * deriv R x ^ 2 =
      -lam * deriv ρ x * R x := by
    apply (eq_div_iff (pow_ne_zero 2 hv.ne')).mp
    exact n06_morseRealization_profile_second_deriv_at_root hreal side hn hx
  have hprofile : D.w (R x) = lam * deriv R x := hreal.profile_eq side n hn x hxc
  have hweighted : deriv (deriv D.w) (R x) * D.w (R x) ^ 2 =
      -lam ^ 3 * deriv ρ x * R x := by
    calc
      _ = lam ^ 2 * (deriv (deriv D.w) (R x) * deriv R x ^ 2) := by
        rw [hprofile]
        ring
      _ = lam ^ 2 * (-lam * deriv ρ x * R x) := by rw [hcurv]
      _ = -lam ^ 3 * deriv ρ x * R x := by ring
  have habs : |deriv (deriv D.w) (R x)| * D.w (R x) ^ 2 =
      lam ^ 3 * |deriv ρ x| * R x := by
    have he := congrArg abs hweighted
    simpa only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (D.w (R x))),
      abs_of_pos (pow_pos hlam 3), abs_of_pos hrp] using he
  have hwM : |D.w (R x)| ≤ M := by
    have hb : |D.w (R x)| ≤ M₀ := by
      simpa only [Real.norm_eq_abs] using hM₀ (R x) ⟨hr.1.le, hr.2.le⟩
    exact hb.trans (le_max_left _ _)
  have hwM2 : D.w (R x) ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (D.w (R x))) hwM 2
  have hmul : lam ^ 3 * (morseChainB T n / 2) * D.a ≤
      |deriv (deriv D.w) (R x)| * M ^ 2 := by
    calc
      _ ≤ lam ^ 3 * |deriv ρ x| * R x :=
        mul_le_mul (mul_le_mul_of_nonneg_left hρ (pow_nonneg hlam.le 3)) hr.1.le
          ha.le (mul_nonneg (pow_nonneg hlam.le 3) (abs_nonneg _))
      _ = |deriv (deriv D.w) (R x)| * D.w (R x) ^ 2 := habs.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hwM2 (abs_nonneg _)
  have hraw : (D.a / (2 * M ^ 2)) * (lam ^ 3 * morseChainB T n) ≤
      |deriv (deriv D.w) (R x)| := by
    have he : (D.a / (2 * M ^ 2)) * (lam ^ 3 * morseChainB T n) =
        (lam ^ 3 * (morseChainB T n / 2) * D.a) / M ^ 2 := by
      field_simp [hM.ne'] <;> ring
    rw [he]
    exact (div_le_iff₀ (sq_pos_of_pos hM)).mpr hmul
  calc
    c * radialE n ^ (-12 : ℝ) = (D.a / (2 * M ^ 2)) *
        (((3 : ℝ) ^ 9)⁻¹ * radialE n ^ (-12 : ℝ)) := by dsimp only [c]; ring
    _ ≤ (D.a / (2 * M ^ 2)) * (lam ^ 3 * morseChainB T n) :=
      mul_le_mul_of_nonneg_left
        (n06_morseChain_amplitude_cubic_lower T σ hσ n (hreal.d_eq n hn))
        (div_nonneg ha.le (mul_nonneg (by norm_num) (sq_nonneg _)))
    _ ≤ |deriv (deriv D.w) (T.radius side n x)| := hraw

end ContinuousFlexibility.Analysis
