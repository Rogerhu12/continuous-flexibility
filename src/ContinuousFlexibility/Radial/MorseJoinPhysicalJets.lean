module

public import ContinuousFlexibility.Radial.MorseCellPhysicalJets
public import ContinuousFlexibility.Radial.MorseJoinActualGerms

/-!
# Physical derivatives on the Morse connectors

The supported slopes are actual logarithmic slopes of the two model
profiles. Leibniz's formula bounds the derivatives of the prescribed slope
on the entire connector. The exponential and its reciprocal retain their
respective height factors.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem exists_joinJet_product_bound (k p q : ℕ) (U V : ℕ → ℝ)
    (hU : ∀ i, 0 ≤ U i) (hV : ∀ i, 0 ≤ V i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f g : ℝ → ℝ} {D W Z x : ℝ},
      1 ≤ D → 0 ≤ W → 0 ≤ Z →
      ContDiffAt ℝ k f x → ContDiffAt ℝ k g x →
      (∀ i ≤ k, |iteratedDeriv i f x| ≤ U i * W * D ^ (p + 16 * i)) →
      (∀ i ≤ k, |iteratedDeriv i g x| ≤ V i * Z * D ^ (q + 16 * i)) →
      |iteratedDeriv k (f * g) x| ≤ C * (W * Z) * D ^ (p + q + 16 * k) := by
  let c (i : Fin (k + 1)) : ℝ := (k.choose i.val : ℝ) * U i.val * V (k - i.val)
  have hc (i : Fin (k + 1)) : 0 ≤ c i :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hU _)) (hV _)
  refine ⟨∑ i, c i, Finset.sum_nonneg (fun i _ => hc i), ?_⟩
  intro f g D W Z x hD hW hZ hf hg hbF hbG
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  let term (i : ℕ) : ℝ :=
    (k.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (k - i) g x
  have hl : iteratedDeriv k (f * g) x = ∑ i : Fin (k + 1), term i.val := by
    rw [Fin.sum_univ_eq_sum_range term]
    exact iteratedDeriv_mul hf hg
  rw [hl, Finset.sum_mul, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  unfold term
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (k.choose i.val))]
  have hi : i.val ≤ k := Nat.le_of_lt_succ i.isLt
  have he : (p + 16 * i.val) + (q + 16 * (k - i.val)) = p + q + 16 * k := by omega
  calc
    _ ≤ (k.choose i.val : ℝ) * (U i.val * W * D ^ (p + 16 * i.val)) *
        (V (k - i.val) * Z * D ^ (q + 16 * (k - i.val))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hbF _ hi) (Nat.cast_nonneg _))
        (hbG _ (Nat.sub_le _ _)) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg (hU _) hW) (pow_nonneg hD₀ _)))
    _ = c i * (W * Z) * (D ^ (p + 16 * i.val) * D ^ (q + 16 * (k - i.val))) := by
      dsimp only [c]
      ring
    _ = _ := by rw [← pow_add, he]

/-- The actual enlarged Morse model and its two positive physical scales. -/
structure MorseJoinJetModel where
  A : ℝ
  B : ℝ
  p : ℝ
  q : ℝ
  amplitude : ℝ
  scale : ℝ
  radius : ℝ → ℝ
  hA : 0 < A
  hA₁ : A ≤ 1
  hB : 0 ≤ B
  hBA : B ≤ A
  hpq : p < q
  hAmplitude : 0 < amplitude
  hScale : 0 < scale
  hSmooth : ContDiff ℝ ∞ radius
  hExp : ∀ x ∈ Icc p q, exp (-x) ≤ 3
  hBound : ∀ x ∈ Icc p q, |radius x| ≤ 2 ∧ |deriv radius x| ≤ 8
  hEquation : ∀ x ∈ Icc p q, deriv (deriv radius) x = -morseRho A B x * radius x
  hVelocity : ∀ x ∈ Ioo p q, A ^ 5 / 200 ≤ deriv radius x

def MorseJoinJetModel.image (M : MorseJoinJetModel) : Set ℝ :=
  Ioo (M.scale * M.radius M.p) (M.scale * M.radius M.q)

def MorseJoinJetModel.height (M : MorseJoinJetModel) : ℝ → ℝ :=
  morseCellPhysicalHeight M.radius M.amplitude M.scale M.p M.q

def MorseJoinJetModel.logProfile (M : MorseJoinJetModel) : ℝ → ℝ :=
  morseCollarLogProfile M.radius M.amplitude M.scale M.p M.q

private theorem MorseJoinJetModel.height_smooth (M : MorseJoinJetModel) :
    ContDiffOn ℝ ∞ M.height M.image ∧
      (∀ x ∈ M.image, 0 < M.height x) ∧ ContDiffOn ℝ ∞ M.height⁻¹ M.image := by
  apply morseCellPhysicalHeight_smooth M.hpq.le M.hAmplitude M.hScale M.hSmooth
  intro x hx
  exact (div_pos (pow_pos M.hA 5) (by norm_num)).trans_le (M.hVelocity x hx)

private theorem MorseJoinJetModel.isOpen_image (M : MorseJoinJetModel) : IsOpen M.image :=
  isOpen_Ioo

private theorem MorseJoinJetModel.logSlope_germ (M : MorseJoinJetModel) {x : ℝ}
    (hx : x ∈ M.image) : deriv M.logProfile =ᶠ[𝓝 x] deriv M.height * M.height⁻¹ := by
  obtain ⟨hw, hp, _⟩ := M.height_smooth
  filter_upwards [M.isOpen_image.mem_nhds hx] with y hy
  have h := ((hw.contDiffAt (M.isOpen_image.mem_nhds hy)).differentiableAt (by simp)).hasDerivAt
  change deriv (fun z => log (M.height z)) y = deriv M.height y * (M.height y)⁻¹
  rw [(h.log (hp y hy).ne').deriv, div_eq_mul_inv]

/-- All positive-order model logarithmic jets are uniform in the amplitude.
The inverse physical scale and the inverse well parameter are both bounded by D. -/
theorem exists_morseJoinModel_logSlopeJet_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : MorseJoinJetModel) {D : ℝ}, 1 ≤ D →
      M.scale⁻¹ ≤ D → M.A⁻¹ ≤ D → ∀ x ∈ M.image,
      |iteratedDeriv k (deriv M.logProfile) x| ≤ C * D ^ (16 + 16 * k) := by
  choose K hK hb using exists_morseCellPhysicalJet_bound
  obtain ⟨C, hC, hproduct⟩ := exists_joinJet_product_bound k 11 5
    (fun i => K (i + 1)) K (fun i => hK (i + 1)) hK
  refine ⟨C, hC, ?_⟩
  intro M D hD hS hA x hx
  let W := M.amplitude * M.scale
  have hW : 0 < W := mul_pos M.hAmplitude M.hScale
  obtain ⟨hw, _, hwi⟩ := M.height_smooth
  have hderiv : ContDiffOn ℝ ∞ (deriv M.height) M.image :=
    ((contDiffOn_infty_iff_deriv_of_isOpen M.isOpen_image).mp hw).2
  have hpow (i j e : ℕ) (he : i + j ≤ e) : M.scale⁻¹ ^ i * M.A⁻¹ ^ j ≤ D ^ e := by
    calc
      _ ≤ D ^ i * D ^ j := mul_le_mul
        (pow_le_pow_left₀ (inv_nonneg.mpr M.hScale.le) hS i)
        (pow_le_pow_left₀ (inv_nonneg.mpr M.hA.le) hA j)
        (pow_nonneg (inv_nonneg.mpr M.hA.le) _) (pow_nonneg (zero_le_one.trans hD) _)
      _ = D ^ (i + j) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hD he
  have hleft (i : ℕ) (_ : i ≤ k) :
      |iteratedDeriv i (deriv M.height) x| ≤ K (i + 1) * W * D ^ (11 + 16 * i) := by
    rw [← iteratedDeriv_succ']
    have h := (hb (i + 1) M.hA M.hA₁ M.hB M.hBA M.hpq M.hSmooth
      M.hExp M.hBound M.hEquation M.hVelocity M.hAmplitude M.hScale x hx).1
    calc
      _ ≤ (K (i + 1) * W) * (M.scale⁻¹ ^ (i + 1) * M.A⁻¹ ^ (10 * (i + 1))) :=
        h.trans_eq (mul_assoc _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpow (i + 1) (10 * (i + 1)) (11 + 16 * i) (by omega))
        (mul_nonneg (hK _) hW.le)
  have hright (i : ℕ) (_ : i ≤ k) :
      |iteratedDeriv i M.height⁻¹ x| ≤ K i * W⁻¹ * D ^ (5 + 16 * i) := by
    have h := (hb i M.hA M.hA₁ M.hB M.hBA M.hpq M.hSmooth
      M.hExp M.hBound M.hEquation M.hVelocity M.hAmplitude M.hScale x hx).2
    calc
      _ ≤ (K i * W⁻¹) * (M.scale⁻¹ ^ i * M.A⁻¹ ^ (5 + 10 * i)) :=
        h.trans_eq (mul_assoc _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpow i (5 + 10 * i) (5 + 16 * i) (by omega))
        (mul_nonneg (hK _) (inv_nonneg.mpr hW.le))
  have h := hproduct hD hW.le (inv_nonneg.mpr hW.le)
    ((hderiv.contDiffAt (M.isOpen_image.mem_nhds hx)).of_le (by simp))
    ((hwi.contDiffAt (M.isOpen_image.mem_nhds hx)).of_le (by simp)) hleft hright
  rw [Filter.EventuallyEq.iteratedDeriv_eq k (M.logSlope_germ hx)]
  simpa only [mul_inv_cancel₀ hW.ne', mul_one] using h

private theorem exists_joinWeight_scaled_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b h D : ℝ}, 0 < h → 1 ≤ D → h⁻¹ ≤ D → ∀ x,
      |iteratedDeriv k (morseJoinLeftWeight a h) x| ≤ C * D ^ (16 * k) ∧
      |iteratedDeriv k (morseJoinRightWeight b h) x| ≤ C * D ^ (16 * k) := by
  obtain ⟨C, hC, hb⟩ := exists_morseJoinWeight_jet_bound k
  refine ⟨C * 2 ^ k, mul_nonneg hC (by positivity), ?_⟩
  intro a b h D hh hD hInv x
  have hm : C * (2 / h) ^ k ≤ C * 2 ^ k * D ^ (16 * k) := by
    rw [div_eq_mul_inv, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ (inv_nonneg.mpr hh.le) hInv k).trans
        (pow_le_pow_right₀ hD (by omega))) (mul_nonneg hC (by positivity))
  exact ⟨(hb a b h hh x).1.trans hm, (hb a b h hh x).2.trans hm⟩

private theorem morseJoinConstant_scaled_bound {a b hL hR D m : ℝ} {FL FR : ℝ → ℝ}
    (hab : a < b) (hhL : 0 < hL) (hhR : 0 < hR) (hw : hL + hR ≤ (b - a) / 2)
    (hD : 1 ≤ D) (hInv : (b - a)⁻¹ ≤ D) (hgap : FR b - FL a ≤ D) (hm : 0 ≤ m)
    (hFloorL : ∀ x ∈ Icc a (a + hL), m ≤ deriv FL x)
    (hFloorR : ∀ x ∈ Icc (b - hR) b, m ≤ deriv FR x)
    (hbudget : MorseJoinBudget a b hL hR m FL FR) :
    |morseJoinConstant a b hL hR FL FR| ≤ 2 * D ^ 16 := by
  have hsep : a + hL < b - hR := by linarith only [hab, hw]
  have hs := morseJoinDenominator_pos hhL hhR hsep
  have hδ : 0 < (b - a) / 2 := div_pos (sub_pos.mpr hab) (by norm_num)
  have hslo : (b - a) / 2 ≤ morseJoinDenominator a b hL hR := by
    linarith only [hw, (morseJoinDenominator_bounds hhL hhR hsep.le).1]
  have hq : (morseJoinDenominator a b hL hR)⁻¹ ≤ 2 * D := calc
    _ ≤ ((b - a) / 2)⁻¹ := (inv_le_inv₀ hs hδ).mpr hslo
    _ = 2 * (b - a)⁻¹ := by rw [inv_div, div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by norm_num)
  have hLi : 0 ≤ ∫ x in a..b, morseJoinLeftSlope a hL FL x := by
    apply intervalIntegral.integral_nonneg hab.le
    intro x hx
    by_cases h : x ≤ a + hL
    · exact mul_nonneg (smoothTransition.nonneg _) (hm.trans (hFloorL x ⟨hx.1, h⟩))
    · simp only [morseJoinLeftSlope, morseJoinLeftWeight_zero hhL (le_of_not_ge h), zero_mul, le_refl]
  have hRi : 0 ≤ ∫ x in a..b, morseJoinRightSlope b hR FR x := by
    apply intervalIntegral.integral_nonneg hab.le
    intro x hx
    by_cases h : b - hR ≤ x
    · exact mul_nonneg (smoothTransition.nonneg _) (hm.trans (hFloorR x ⟨h, hx.2⟩))
    · simp only [morseJoinRightSlope, morseJoinRightWeight_zero hhR (le_of_not_ge h), zero_mul, le_refl]
  rw [abs_of_nonneg (hm.trans (morseJoinConstant_ge hhL hhR hsep hbudget))]
  unfold morseJoinConstant
  rw [div_eq_mul_inv]
  calc
    _ ≤ D * (morseJoinDenominator a b hL hR)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith only [hLi, hRi, hgap]) (inv_nonneg.mpr hs.le)
    _ ≤ D * (2 * D) := mul_le_mul_of_nonneg_left hq (zero_le_one.trans hD)
    _ = 2 * D ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by norm_num)) (by norm_num)

private theorem abs_iteratedDeriv_joinOne_le (k : ℕ) {D : ℝ} (hD : 1 ≤ D) (x : ℝ) :
    |iteratedDeriv k (fun _ : ℝ => (1 : ℝ)) x| ≤ D ^ (16 * k) := by
  cases k with
  | zero => simp
  | succ k => simpa only [iteratedDeriv_const, ite_eq_right (Nat.succ_ne_zero k), abs_zero]
      using pow_nonneg (zero_le_one.trans hD) (16 * (k + 1))

/-- The data used in the actual connector formula. The scale D bounds the
inverse widths and the logarithmic height difference. -/
structure MorseJoinJetData where
  a : ℝ
  b : ℝ
  hL : ℝ
  hR : ℝ
  D : ℝ
  m : ℝ
  FL : ℝ → ℝ
  FR : ℝ → ℝ
  hab : a < b
  hWidthL : 0 < hL
  hWidthR : 0 < hR
  hWidths : hL + hR ≤ (b - a) / 2
  hD : 1 ≤ D
  hInvL : hL⁻¹ ≤ D
  hInvR : hR⁻¹ ≤ D
  hInvSpan : (b - a)⁻¹ ≤ D
  hGap : FR b - FL a ≤ D
  hm : 0 ≤ m
  hSmoothL : ContDiff ℝ ∞ FL
  hSmoothR : ContDiff ℝ ∞ FR
  hFloorL : ∀ x ∈ Icc a (a + hL), m ≤ deriv FL x
  hFloorR : ∀ x ∈ Icc (b - hR) b, m ≤ deriv FR x
  hBudget : MorseJoinBudget a b hL hR m FL FR

def MorseJoinJetData.logProfile (J : MorseJoinJetData) : ℝ → ℝ :=
  morseJoinLog J.a J.b J.hL J.hR J.FL J.FR

def MorseJoinJetData.height (J : MorseJoinJetData) : ℝ → ℝ :=
  morseJoinProfile J.a J.b J.hL J.hR J.FL J.FR

private theorem MorseJoinJetData.separated (J : MorseJoinJetData) : J.a + J.hL < J.b - J.hR := by
  linarith only [J.hab, J.hWidths]

private theorem MorseJoinJetData.log_smooth (J : MorseJoinJetData) : ContDiff ℝ ∞ J.logProfile :=
  contDiff_morseJoinLog J.hSmoothL J.hSmoothR

/-- The actual connector height lies between its two prescribed endpoint
heights, with the same globally smooth positive witness. -/
theorem MorseJoinJetData.height_between (J : MorseJoinJetData) :
    ContDiff ℝ ∞ J.height ∧ (∀ x, 0 < J.height x) ∧
    ∀ x ∈ Icc J.a J.b, exp (J.FL J.a) ≤ J.height x ∧ J.height x ≤ exp (J.FR J.b) := by
  obtain ⟨hw, hp, _, hmono, _⟩ := morseJoinProfile_positive_mono J.hWidthL J.hWidthR
    J.separated J.hSmoothL J.hSmoothR J.hm J.hFloorL J.hFloorR J.hBudget
  have hwa : J.height J.a = exp (J.FL J.a) := by
    change exp (morseJoinLog J.a J.b J.hL J.hR J.FL J.FR J.a) = _
    simp only [morseJoinLog, intervalIntegral.integral_same, add_zero]
  have hwb : J.height J.b = exp (J.FR J.b) := by
    change exp (morseJoinLog J.a J.b J.hL J.hR J.FL J.FR J.b) = _
    rw [morseJoinLog_right_value J.hWidthL J.hWidthR J.separated J.hSmoothL J.hSmoothR]
  refine ⟨hw, hp, fun x hx => ?_⟩
  rw [← hwa, ← hwb]
  exact ⟨hmono (left_mem_Icc.mpr J.hab.le) hx hx.1,
    hmono hx (right_mem_Icc.mpr J.hab.le) hx.2⟩

private theorem exists_morseJoinLog_succJet_bound (K : ℕ → ℝ) (hK : ∀ i, 0 ≤ K i) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : MorseJoinJetData),
      (∀ i, ∀ x ∈ Icc J.a (J.a + J.hL),
        |iteratedDeriv i (deriv J.FL) x| ≤ K i * J.D ^ (16 + 16 * i)) →
      (∀ i, ∀ x ∈ Icc (J.b - J.hR) J.b,
        |iteratedDeriv i (deriv J.FR) x| ≤ K i * J.D ^ (16 + 16 * i)) →
      ∀ x ∈ Icc J.a J.b,
        |iteratedDeriv (k + 1) J.logProfile x| ≤ C * J.D ^ (16 + 16 * k) := by
  choose U hU hb using exists_joinWeight_scaled_bound
  obtain ⟨C, hC, hmul⟩ := exists_joinJet_product_bound k 0 16 U K hU hK
  have hQ₀ : 0 ≤ 1 + U k + U k := add_nonneg (add_nonneg zero_le_one (hU k)) (hU k)
  refine ⟨C + C + 2 * (1 + U k + U k),
    add_nonneg (add_nonneg hC hC) (mul_nonneg (by norm_num) hQ₀), ?_⟩
  intro J hL hR x hx
  have hD₀ : 0 ≤ J.D := zero_le_one.trans J.hD
  let χL := morseJoinLeftWeight J.a J.hL
  let χR := morseJoinRightWeight J.b J.hR
  let Q := morseJoinRemainder J.a J.b J.hL J.hR
  let c := morseJoinConstant J.a J.b J.hL J.hR J.FL J.FR
  let gL := morseJoinLeftSlope J.a J.hL J.FL
  let gR := morseJoinRightSlope J.b J.hR J.FR
  have hsL : ContDiff ℝ ∞ χL := contDiff_morseJoinLeftWeight J.a J.hL
  have hsR : ContDiff ℝ ∞ χR := contDiff_morseJoinRightWeight J.b J.hR
  have hdL : ContDiff ℝ ∞ (deriv J.FL) := (contDiff_infty_iff_deriv.mp J.hSmoothL).2
  have hdR : ContDiff ℝ ∞ (deriv J.FR) := (contDiff_infty_iff_deriv.mp J.hSmoothR).2
  have hbL (i : ℕ) : |iteratedDeriv i χL x| ≤ U i * J.D ^ (16 * i) :=
    (hb i (a := J.a) (b := J.b) J.hWidthL J.hD J.hInvL x).1
  have hbR (i : ℕ) : |iteratedDeriv i χR x| ≤ U i * J.D ^ (16 * i) :=
    (hb i (a := J.a) (b := J.b) J.hWidthR J.hD J.hInvR x).2
  have hleft : |iteratedDeriv k gL x| ≤ C * J.D ^ (16 + 16 * k) := by
    by_cases hxL : x ≤ J.a + J.hL
    · have h := hmul (f := χL) (g := deriv J.FL) (x := x)
        J.hD (zero_le_one : (0 : ℝ) ≤ 1) (zero_le_one : (0 : ℝ) ≤ 1)
        (hsL.contDiffAt.of_le (by simp)) (hdL.contDiffAt.of_le (by simp))
        (fun i _ => by simpa only [mul_one, zero_add] using hbL i)
        (fun i _ => by simpa only [mul_one] using hL i x ⟨hx.1, hxL⟩)
      change |iteratedDeriv k (χL * deriv J.FL) x| ≤ _
      simpa only [one_mul, zero_add, mul_one] using h
    · have h0 : gL =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds (lt_of_not_ge hxL)] with y hy
        change morseJoinLeftWeight J.a J.hL y * deriv J.FL y = 0
        rw [morseJoinLeftWeight_zero J.hWidthL (le_of_lt hy), zero_mul]
      rw [Filter.EventuallyEq.iteratedDeriv_eq k h0]
      simpa only [iteratedDeriv_const, ite_self, abs_zero]
        using mul_nonneg hC (pow_nonneg hD₀ (16 + 16 * k))
  have hright : |iteratedDeriv k gR x| ≤ C * J.D ^ (16 + 16 * k) := by
    by_cases hxR : J.b - J.hR ≤ x
    · have h := hmul (f := χR) (g := deriv J.FR) (x := x)
        J.hD (zero_le_one : (0 : ℝ) ≤ 1) (zero_le_one : (0 : ℝ) ≤ 1)
        (hsR.contDiffAt.of_le (by simp)) (hdR.contDiffAt.of_le (by simp))
        (fun i _ => by simpa only [mul_one, zero_add] using hbR i)
        (fun i _ => by simpa only [mul_one] using hR i x ⟨hxR, hx.2⟩)
      change |iteratedDeriv k (χR * deriv J.FR) x| ≤ _
      simpa only [one_mul, zero_add, mul_one] using h
    · have h0 : gR =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [Iio_mem_nhds (lt_of_not_ge hxR)] with y hy
        change morseJoinRightWeight J.b J.hR y * deriv J.FR y = 0
        rw [morseJoinRightWeight_zero J.hWidthR (le_of_lt hy), zero_mul]
      rw [Filter.EventuallyEq.iteratedDeriv_eq k h0]
      simpa only [iteratedDeriv_const, ite_self, abs_zero]
        using mul_nonneg hC (pow_nonneg hD₀ (16 + 16 * k))
  have hc : |c| ≤ 2 * J.D ^ 16 := morseJoinConstant_scaled_bound J.hab J.hWidthL J.hWidthR
    J.hWidths J.hD J.hInvSpan J.hGap J.hm J.hFloorL J.hFloorR J.hBudget
  have hsOne : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  have hsQ : ContDiff ℝ ∞ Q := (hsOne.sub hsL).sub hsR
  have absSub (u v : ℝ) : |u - v| ≤ |u| + |v| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le u (-v)
  have hQ : |iteratedDeriv k Q x| ≤ (1 + U k + U k) * J.D ^ (16 * k) := by
    have h1 : ContDiffAt ℝ k (fun _ : ℝ => (1 : ℝ)) x := contDiffAt_const
    have h2 : ContDiffAt ℝ k χL x := hsL.contDiffAt.of_le (by simp)
    have h3 : ContDiffAt ℝ k χR x := hsR.contDiffAt.of_le (by simp)
    change |iteratedDeriv k (fun y => 1 - χL y - χR y) x| ≤ _
    rw [iteratedDeriv_fun_sub (h1.sub h2) h3, iteratedDeriv_fun_sub h1 h2]
    calc
      _ ≤ J.D ^ (16 * k) + U k * J.D ^ (16 * k) + U k * J.D ^ (16 * k) :=
        (absSub _ _).trans (add_le_add
          ((absSub _ _).trans (add_le_add (abs_iteratedDeriv_joinOne_le k J.hD x) (hbL k))) (hbR k))
      _ = _ := by ring
  have hmid : |iteratedDeriv k (fun y => c * Q y) x| ≤
      (2 * (1 + U k + U k)) * J.D ^ (16 + 16 * k) := by
    rw [iteratedDeriv_const_mul_field, abs_mul]
    calc
      _ ≤ (2 * J.D ^ 16) * ((1 + U k + U k) * J.D ^ (16 * k)) :=
        mul_le_mul hc hQ (abs_nonneg _) (mul_nonneg (by norm_num) (pow_nonneg hD₀ 16))
      _ = _ := by rw [pow_add]; ring
  have hl : ContDiffAt ℝ k gL x := (hsL.mul hdL).contDiffAt.of_le (by simp)
  have hr : ContDiffAt ℝ k gR x := (hsR.mul hdR).contDiffAt.of_le (by simp)
  have hm : ContDiffAt ℝ k (fun y => c * Q y) x :=
    (contDiff_const.mul hsQ).contDiffAt.of_le (by simp)
  change |iteratedDeriv (k + 1) (morseJoinLog J.a J.b J.hL J.hR J.FL J.FR) x| ≤ _
  rw [iteratedDeriv_morseJoinLog_succ J.hSmoothL J.hSmoothR k]
  change |iteratedDeriv k (fun y => gL y + gR y + c * Q y) x| ≤ _
  rw [iteratedDeriv_fun_add (hl.add hr) hm, iteratedDeriv_fun_add hl hr]
  calc
    _ ≤ |iteratedDeriv k gL x| + |iteratedDeriv k gR x| +
        |iteratedDeriv k (fun y => c * Q y) x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C * J.D ^ (16 + 16 * k) + C * J.D ^ (16 + 16 * k) +
        (2 * (1 + U k + U k)) * J.D ^ (16 + 16 * k) := add_le_add (add_le_add hleft hright) hmid
    _ = _ := by ring

private theorem exists_joinExpJet_bound (K : ℕ → ℝ) (hK : ∀ i, 0 ≤ K i) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : ℝ → ℝ} {D x : ℝ}, 1 ≤ D → ContDiff ℝ ∞ F →
      (∀ i, |iteratedDeriv (i + 1) F x| ≤ K i * D ^ (16 + 16 * i)) →
      |iteratedDeriv n (fun t => exp (F t)) x| ≤ C * exp (F x) * D ^ (16 * n) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro F D x _ _ _
      simp only [iteratedDeriv_zero, Nat.mul_zero, pow_zero, mul_one, one_mul,
        abs_of_pos (exp_pos (F x)), le_refl]
    | succ n =>
      have hprev (i : Fin (n + 1)) := ih i.val i.isLt
      choose A hA hb using hprev
      let U (i : ℕ) : ℝ := if hi : i ≤ n then A ⟨i, Nat.lt_succ_of_le hi⟩ else 0
      have hU (i : ℕ) : 0 ≤ U i := by
        by_cases hi : i ≤ n
        · simpa only [U, dite_eq_left hi] using hA ⟨i, Nat.lt_succ_of_le hi⟩
        · simp only [U, dite_eq_right hi, le_refl]
      obtain ⟨C, hC, hprod⟩ := exists_joinJet_product_bound n 0 16 U K hU hK
      refine ⟨C, hC, ?_⟩
      intro F D x hD hF hJet
      let E (t : ℝ) := exp (F t)
      have hE : ContDiff ℝ ∞ E := hF.exp
      have hdF : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
      have hE' : deriv E = E * deriv F :=
        funext fun t => (((hF.differentiable (by simp) t).hasDerivAt).exp).deriv
      have hLeft (i : ℕ) (hi : i ≤ n) :
          |iteratedDeriv i E x| ≤ U i * E x * D ^ (0 + 16 * i) := by
        simpa only [U, dite_eq_left hi, zero_add] using hb ⟨i, Nat.lt_succ_of_le hi⟩ hD hF hJet
      have hRight (i : ℕ) (_ : i ≤ n) :
          |iteratedDeriv i (deriv F) x| ≤ K i * 1 * D ^ (16 + 16 * i) := by
        simpa only [iteratedDeriv_succ', mul_one] using hJet i
      have h := hprod hD (exp_pos (F x)).le (zero_le_one : (0 : ℝ) ≤ 1)
        (hE.contDiffAt.of_le (by simp)) (hdF.contDiffAt.of_le (by simp)) hLeft hRight
      change |iteratedDeriv (n + 1) E x| ≤ C * E x * D ^ (16 * (n + 1))
      rw [iteratedDeriv_succ', hE', show 16 * (n + 1) = 16 + 16 * n by omega]
      simpa only [mul_one, zero_add] using h

/-- Fixed-order physical derivatives of the actual positive connector and
its reciprocal retain the corresponding height factor. The constants
depend only on the uniform collar-slope constants and the order. -/
theorem exists_morseJoinPhysicalJet_bound (K : ℕ → ℝ) (hK : ∀ i, 0 ≤ K i) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : MorseJoinJetData),
      (∀ i, ∀ x ∈ Icc J.a (J.a + J.hL),
        |iteratedDeriv i (deriv J.FL) x| ≤ K i * J.D ^ (16 + 16 * i)) →
      (∀ i, ∀ x ∈ Icc (J.b - J.hR) J.b,
        |iteratedDeriv i (deriv J.FR) x| ≤ K i * J.D ^ (16 + 16 * i)) →
      ∀ x ∈ Icc J.a J.b,
        |iteratedDeriv k J.height x| ≤ C * J.height x * J.D ^ (16 * k) ∧
        |iteratedDeriv k J.height⁻¹ x| ≤ C * (J.height x)⁻¹ * J.D ^ (16 * k) := by
  choose B hB hb using exists_morseJoinLog_succJet_bound K hK
  obtain ⟨C, hC, hExp⟩ := exists_joinExpJet_bound B hB k
  refine ⟨C, hC, ?_⟩
  intro J hL hR x hx
  have hlog (i : ℕ) := hb i J hL hR x hx
  have hneg (i : ℕ) :
      |iteratedDeriv (i + 1) (-J.logProfile) x| ≤ B i * J.D ^ (16 + 16 * i) := by
    simpa only [iteratedDeriv_neg, abs_neg] using hlog i
  have hInv : J.height⁻¹ = fun t => exp ((-J.logProfile) t) := by
    funext t
    exact (exp_neg (J.logProfile t)).symm
  refine ⟨hExp (F := J.logProfile) J.hD J.log_smooth hlog, ?_⟩
  change |iteratedDeriv k J.height⁻¹ x| ≤ C * (J.height⁻¹ x) * J.D ^ (16 * k)
  rw [hInv]
  exact hExp (F := -J.logProfile) J.hD J.log_smooth.neg hneg

/-- The actual model germs furnish the collar slope estimates. The chosen
extensions enter the conclusion through the original connector formula. -/
theorem exists_morseJoin_modelPhysicalJet_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : MorseJoinJetData) (L R : MorseJoinJetModel),
      L.scale⁻¹ ≤ J.D → L.A⁻¹ ≤ J.D → R.scale⁻¹ ≤ J.D → R.A⁻¹ ≤ J.D →
      Icc J.a (J.a + J.hL) ⊆ L.image → Icc (J.b - J.hR) J.b ⊆ R.image →
      (∀ x ∈ Icc J.a (J.a + J.hL), J.FL =ᶠ[𝓝 x] L.logProfile) →
      (∀ x ∈ Icc (J.b - J.hR) J.b, J.FR =ᶠ[𝓝 x] R.logProfile) →
      ∀ x ∈ Icc J.a J.b,
        |iteratedDeriv k J.height x| ≤ C * J.height x * J.D ^ (16 * k) ∧
        |iteratedDeriv k J.height⁻¹ x| ≤ C * (J.height x)⁻¹ * J.D ^ (16 * k) := by
  choose K hK hb using exists_morseJoinModel_logSlopeJet_bound
  obtain ⟨C, hC, hJoin⟩ := exists_morseJoinPhysicalJet_bound K hK k
  refine ⟨C, hC, ?_⟩
  intro J L R hSL hAL hSR hAR hLsub hRsub hLg hRg
  apply hJoin J
  · intro i x hx
    rw [Filter.EventuallyEq.iteratedDeriv_eq i (hLg x hx).deriv]
    exact hb i L J.hD hSL hAL x (hLsub hx)
  · intro i x hx
    rw [Filter.EventuallyEq.iteratedDeriv_eq i (hRg x hx).deriv]
    exact hb i R J.hD hSR hAR x (hRsub hx)

theorem MorseJoinJetData.height_between_models (J : MorseJoinJetData) (L R : MorseJoinJetModel)
    (hLsub : Icc J.a (J.a + J.hL) ⊆ L.image) (hRsub : Icc (J.b - J.hR) J.b ⊆ R.image)
    (hLg : ∀ x ∈ Icc J.a (J.a + J.hL), J.FL =ᶠ[𝓝 x] L.logProfile)
    (hRg : ∀ x ∈ Icc (J.b - J.hR) J.b, J.FR =ᶠ[𝓝 x] R.logProfile) :
    ∀ x ∈ Icc J.a J.b, L.height J.a ≤ J.height x ∧ J.height x ≤ R.height J.b := by
  have hLa : J.a ∈ Icc J.a (J.a + J.hL) := ⟨le_rfl, le_add_of_nonneg_right J.hWidthL.le⟩
  have hRb : J.b ∈ Icc (J.b - J.hR) J.b := ⟨sub_le_self _ J.hWidthR.le, le_rfl⟩
  have hL : exp (J.FL J.a) = L.height J.a := by
    rw [(hLg J.a hLa).eq_of_nhds]
    exact exp_log (L.height_smooth.2.1 _ (hLsub hLa))
  have hR : exp (J.FR J.b) = R.height J.b := by
    rw [(hRg J.b hRb).eq_of_nhds]
    exact exp_log (R.height_smooth.2.1 _ (hRsub hRb))
  intro x hx
  simpa only [hL, hR] using J.height_between.2.2 x hx

end ContinuousFlexibility.Radial
