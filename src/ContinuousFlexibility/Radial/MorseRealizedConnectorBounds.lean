import ContinuousFlexibility.Radial.MorseRealizationBasic
import ContinuousFlexibility.Radial.MorseRealizedCellBounds
import ContinuousFlexibility.Radial.MorseAdjacentScaleBounds

/-!
# Connector integrals of an arbitrary realized Morse chain

The profile on a connector is controlled by its endpoint heights and
the physical logarithmic slope. Both endpoint orientations use the
same estimates in increasing physical radius.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Positive physical logarithmic slope makes the profile monotone on
the closed connector, including its two matched endpoints. -/
theorem morseConnector_monotone_of_logSlope {w : ℝ → ℝ} {l r : ℝ}
    (hw : ContDiff ℝ ∞ w) (hl : 0 < l)
    (hwp : ∀ x ∈ Icc l r, 0 < w x)
    (hslope : ∀ x ∈ Ioo l r, 2 / x ≤ deriv w x / w x) :
    MonotoneOn w (Icc l r) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc l r) hw.continuous.continuousOn
    (hw.differentiable (by simp)).differentiableOn
  intro x hx
  have hx' : x ∈ Ioo l r := by simpa only [interior_Icc] using hx
  have hquot : 0 ≤ deriv w x / w x :=
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hl.trans hx'.1).le).trans (hslope x hx')
  simpa only [zero_mul] using (le_div_iff₀ (hwp x (Ioo_subset_Icc_self hx'))).mp hquot

/-- Monotonicity bounds connector mass by its arrival height and
connector resistance by the reciprocal of its departure height. -/
theorem morseConnector_mass_resistance_bounds {w : ℝ → ℝ} {α β l r : ℝ}
    (hα : 0 < α) (hαl : α ≤ l) (hlr : l ≤ r) (hrβ : r ≤ β)
    (hwc : Continuous w) (hwp : ∀ x ∈ Icc l r, 0 < w x)
    (hmono : MonotoneOn w (Icc l r)) :
    (∫ x in l..r, w x * x ^ 6) ≤ (r - l) * w r * β ^ 6 ∧
      (∫ x in l..r, (w x * x ^ 8)⁻¹) ≤ (r - l) / (w l * α ^ 8) := by
  have hlp : 0 < l := hα.trans_le hαl
  have hlMem : l ∈ Icc l r := left_mem_Icc.mpr hlr
  have hrMem : r ∈ Icc l r := right_mem_Icc.mpr hlr
  have hMass (x : ℝ) (hx : x ∈ Icc l r) : w x * x ^ 6 ≤ w r * β ^ 6 :=
    mul_le_mul (hmono hx hrMem hx.2)
      (pow_le_pow_left₀ (hlp.le.trans hx.1) (hx.2.trans hrβ) 6)
      (pow_nonneg (hlp.le.trans hx.1) 6) (hwp r hrMem).le
  have hRes (x : ℝ) (hx : x ∈ Icc l r) :
      (w x * x ^ 8)⁻¹ ≤ (w l * α ^ 8)⁻¹ := by
    have hprod : w l * α ^ 8 ≤ w x * x ^ 8 :=
      mul_le_mul (hmono hlMem hx hx.1)
        (pow_le_pow_left₀ hα.le (hαl.trans hx.1) 8)
        (pow_nonneg hα.le 8) (hwp x hx).le
    simpa only [one_div] using
      one_div_le_one_div_of_le (mul_pos (hwp l hlMem) (pow_pos hα 8)) hprod
  have hMi : IntervalIntegrable (fun x => w x * x ^ 6) volume l r :=
    (hwc.mul (continuous_id.pow 6)).intervalIntegrable _ _
  have hRi : IntervalIntegrable (fun x => (w x * x ^ 8)⁻¹) volume l r :=
    ((hwc.continuousOn.mul (continuous_id.continuousOn.pow 8)).inv₀
      (fun x hx => (mul_pos (hwp x hx) (pow_pos (hlp.trans_le hx.1) 8)).ne')).intervalIntegrable_of_Icc hlr
  have hM := intervalIntegral.integral_mono_on (μ := volume) hlr hMi
    (continuous_const.intervalIntegrable _ _) hMass
  have hR := intervalIntegral.integral_mono_on (μ := volume) hlr hRi
    (continuous_const.intervalIntegrable _ _) hRes
  rw [intervalIntegral.integral_const, smul_eq_mul] at hM hR
  exact ⟨by simpa only [mul_assoc] using hM, by simpa only [div_eq_mul_inv] using hR⟩

/-- The endpoint estimates and the two adjacent scale bounds are
enough for a connector of any smaller width. -/
theorem morseConnector_scaled_mass_resistance_bounds
    {w : ℝ → ℝ} {α β l r A B lam eta K S L H : ℝ}
    (hα : 0 < α) (hαl : α ≤ l) (hlr : l ≤ r) (hrβ : r ≤ β)
    (hwc : Continuous w) (hwp : ∀ x ∈ Icc l r, 0 < w x)
    (hmono : MonotoneOn w (Icc l r))
    (hA : 0 < A) (hlam : 0 < lam) (hK : 0 < K) (hL : 0 ≤ L)
    (hwidth : r - l ≤ L * H ^ 12)
    (harrival : w r ≤ eta * K * B)
    (hdeparture : lam * A ^ 5 / K ≤ w l)
    (hMscale : (eta / lam) * B * H ^ 12 / A ^ 6 ≤ S)
    (hRscale : H ^ 12 / A ≤ S) :
    (∫ x in l..r, w x * x ^ 6) ≤ (L * K * β ^ 6 * S) * lam * A ^ 6 ∧
      (∫ x in l..r, (w x * x ^ 8)⁻¹) ≤
        (L * K * S / α ^ 8) * lam⁻¹ * (A ^ 4)⁻¹ := by
  obtain ⟨hM, hR⟩ := morseConnector_mass_resistance_bounds hα hαl hlr hrβ hwc hwp hmono
  have hlMem : l ∈ Icc l r := left_mem_Icc.mpr hlr
  have hrMem : r ∈ Icc l r := right_mem_Icc.mpr hlr
  have hwidthNonneg : 0 ≤ L * H ^ 12 := by positivity
  have hMscale' : (eta / lam) * B * H ^ 12 ≤ S * A ^ 6 :=
    (div_le_iff₀ (pow_pos hA 6)).mp hMscale
  have hMcoef : 0 ≤ L * K * β ^ 6 * lam := by positivity
  have hdeparturePos : 0 < lam * A ^ 5 / K := div_pos (mul_pos hlam (pow_pos hA 5)) hK
  have hInv : (w l * α ^ 8)⁻¹ ≤ (lam * A ^ 5 / K * α ^ 8)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (mul_pos hdeparturePos (pow_pos hα 8))
      (mul_le_mul_of_nonneg_right hdeparture (pow_nonneg hα.le 8))
  have hRcoef : 0 ≤ L * K / α ^ 8 * lam⁻¹ * (A ^ 4)⁻¹ := by positivity
  constructor
  · calc
      _ ≤ (r - l) * w r * β ^ 6 := hM
      _ ≤ (L * H ^ 12) * (eta * K * B) * β ^ 6 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hwidth harrival (hwp r hrMem).le hwidthNonneg) (by positivity)
      _ = (L * K * β ^ 6 * lam) * ((eta / lam) * B * H ^ 12) := by
        field_simp [hlam.ne']
        ring
      _ ≤ (L * K * β ^ 6 * lam) * (S * A ^ 6) :=
        mul_le_mul_of_nonneg_left hMscale' hMcoef
      _ = _ := by ring
  · calc
      _ ≤ (r - l) * (w l * α ^ 8)⁻¹ := by simpa only [div_eq_mul_inv] using hR
      _ ≤ (L * H ^ 12) * (lam * A ^ 5 / K * α ^ 8)⁻¹ :=
        mul_le_mul hwidth hInv
          (inv_nonneg.mpr (mul_nonneg (hwp l hlMem).le (pow_nonneg hα.le 8))) hwidthNonneg
      _ = (L * K / α ^ 8 * lam⁻¹ * (A ^ 4)⁻¹) * (H ^ 12 / A) := by
        field_simp [hlam.ne', hK.ne', hA.ne', hα.ne']
        ring
      _ ≤ (L * K / α ^ 8 * lam⁻¹ * (A ^ 4)⁻¹) * S :=
        mul_le_mul_of_nonneg_left hRscale hRcoef
      _ = _ := by ring

/-- Departure and arrival refer to increasing physical radius on both
tails. The frozen width bound is controlled by the larger adjacent scale. -/
theorem morseRealizedJoin_endpoints {T : MorseChainData} {C : ℕ → ℝ}
    {σ : ℕ → ℝ} {D : ReferenceData} (h : MorseChainRealization T σ D C)
    (side : Bool) (k : ℕ) (hk : T.index ≤ k) :
    let n := if side then k else k + 1
    let m := if side then k + 1 else k
    T.index ≤ n ∧ T.index ≤ m ∧ (m = n + 1 ∨ n = m + 1) ∧
      T.joinLeft side k = T.radius side n (T.rightX side n) ∧
      T.joinRight side k = T.radius side m (T.leftX side m) ∧
      T.joinRight side k - T.joinLeft side k ≤
        C 0 * (max (morseChainA T n) (morseChainA T m)) ^ 12 := by
  have hj := h.join_data side k hk
  have hk' : T.index ≤ k + 1 := hk.trans (Nat.le_succ k)
  have hAk : 0 ≤ morseChainA T k := sq_nonneg _
  cases side
  · refine ⟨hk', hk, Or.inr rfl, hj.2.1, hj.2.2.1, ?_⟩
    exact hj.2.2.2.1.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hAk (le_max_right _ _) 12) (h.constants_pos 0).le)
  · refine ⟨hk, hk', Or.inl rfl, hj.2.1, hj.2.2.1, ?_⟩
    exact hj.2.2.2.1.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hAk (le_max_left _ _) 12) (h.constants_pos 0).le)

/-- Every actual join obeys the same two bounds. Its radius weights
are controlled using one baseline realization of the fixed charts. -/
theorem morseRealizedJoin_bounds {T : MorseChainData} {C : ℕ → ℝ}
    {D0 D : ReferenceData} {σ : ℕ → ℝ} {K S : ℝ}
    (h0 : MorseChainRealization T (fun _ => 1) D0 C)
    (hcell : MorseRealizedCellEstimates T K)
    (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) (h : MorseChainRealization T σ D C)
    (hscale : ∀ n m, T.index ≤ n → T.index ≤ m → (m = n + 1 ∨ n = m + 1) →
      (morseChainAmplitude T σ m / morseChainAmplitude T σ n) * morseChainA T m *
          (max (morseChainA T n) (morseChainA T m)) ^ 12 / morseChainA T n ^ 6 ≤ S ∧
        (max (morseChainA T n) (morseChainA T m)) ^ 12 / morseChainA T n ≤ S)
    (side : Bool) (k : ℕ) (hk : T.index ≤ k) :
    let n := if side then k else k + 1
    (∫ x in T.joinLeft side k..T.joinRight side k, D.w x * x ^ 6) ≤
        (C 0 * K * D0.b ^ 6 * S) * morseChainAmplitude T σ n * morseChainA T n ^ 6 ∧
      (∫ x in T.joinLeft side k..T.joinRight side k, (D.w x * x ^ 8)⁻¹) ≤
        (C 0 * K * S / D0.a ^ 8) * (morseChainAmplitude T σ n)⁻¹ *
          (morseChainA T n ^ 4)⁻¹ := by
  let n := if side then k else k + 1
  let m := if side then k + 1 else k
  obtain ⟨hn, hm, hadj, hjl, hjr, hwidth⟩ := morseRealizedJoin_endpoints h side k hk
  have horder (i : ℕ) (hi : T.index ≤ i) : T.leftX side i ≤ T.rightX side i :=
    ((h.retained_data side i hi).2.2.2.1.trans
      (h.retained_data side i hi).2.2.2.2.1).le
  have hnr : T.rightX side n ∈ Icc (T.leftX side n) (T.rightX side n) :=
    right_mem_Icc.mpr (horder n hn)
  have hml : T.leftX side m ∈ Icc (T.leftX side m) (T.rightX side m) :=
    left_mem_Icc.mpr (horder m hm)
  have hl0 : T.joinLeft side k ∈ radialCore D0 := by
    rw [hjl]
    exact h0.radius_mem_core side n hn _ hnr
  have hr0 : T.joinRight side k ∈ radialCore D0 := by
    rw [hjr]
    exact h0.radius_mem_core side m hm _ hml
  have hlD : T.joinLeft side k ∈ radialCore D := by
    rw [hjl]
    exact h.radius_mem_core side n hn _ hnr
  have hrD : T.joinRight side k ∈ radialCore D := by
    rw [hjr]
    exact h.radius_mem_core side m hm _ hml
  have hwp (x : ℝ) (hx : x ∈ Icc (T.joinLeft side k) (T.joinRight side k)) :
      0 < D.w x :=
    h.geometry.2.2.2.2.1 x ⟨hlD.1.trans_le hx.1, hx.2.trans_lt hrD.2⟩
  have hw : ContDiff ℝ ∞ D.w := h.geometry.2.2.1.1
  have hj := h.join_data side k hk
  have hmono := morseConnector_monotone_of_logSlope hw (h0.geometry.1.trans hl0.1)
    hwp hj.2.2.2.2
  have hAn : 0 < morseChainA T n :=
    (mul_pos (by norm_num : (0 : ℝ) < 4) (h.retained_data side n hn).1).trans
      (h.retained_data side n hn).2.1
  have hlam := morseChainAmplitude_pos T σ hσ n
  have heta := morseChainAmplitude_pos T σ hσ m
  have harrival : D.w (T.joinRight side k) ≤
      morseChainAmplitude T σ m * K * morseChainA T m := by
    rw [hjr, h.profile_eq side m hm _ hml]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hcell.left_speed_upper side m hm) heta.le
  have hdeparture : morseChainAmplitude T σ n * morseChainA T n ^ 5 / K ≤
      D.w (T.joinLeft side k) := by
    rw [hjl, h.profile_eq side n hn _ hnr]
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left (hcell.right_speed_lower side n hn) hlam.le
  have hs := hscale n m hn hm hadj
  exact morseConnector_scaled_mass_resistance_bounds h0.geometry.1 hl0.1.le hj.1.le hr0.2.le
    hw.continuous hwp hmono hAn hlam hcell.pos (h.constants_pos 0).le
    hwidth harrival hdeparture hs.1 hs.2

/-- The interval following a retained cap is an actual connector,
except for the first left cap, whose connector interval is empty. -/
theorem morseRealizedConnector_join_or_zero {T : MorseChainData} {C : ℕ → ℝ}
    {σ : ℕ → ℝ} {D : ReferenceData} (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    T.radius side n (T.rightX side n) = morseChainResistanceEnd T side n ∨
      ∃ k : ℕ, T.index ≤ k ∧
        T.radius side n (T.rightX side n) = T.joinLeft side k ∧
        morseChainResistanceEnd T side n = T.joinRight side k ∧
        (if side then k else k + 1) = n := by
  cases side
  · by_cases hi : T.index < n
    · right
      have hk : T.index ≤ n - 1 := by omega
      have hpred : n - 1 + 1 = n := by omega
      have he : T.joinLeft false (n - 1) =
          T.radius false (n - 1 + 1) (T.rightX false (n - 1 + 1)) :=
        (h.join_data false (n - 1) hk).2.1
      rw [hpred] at he
      refine ⟨n - 1, hk, he.symm, ?_, hpred⟩
      simp only [morseChainResistanceEnd, Bool.false_eq_true, ↓reduceIte, hi]
    · left
      simp only [morseChainResistanceEnd, Bool.false_eq_true, ↓reduceIte, hi]
  · exact Or.inr ⟨n, hn, (h.join_data true n hn).2.1.symm, rfl, rfl⟩

/-- One connector constant works for all admissible height choices
and for every realization with the same charts and original constants. -/
theorem exists_morseRealizedConnectorBounds {T : MorseChainData} {C : ℕ → ℝ}
    {D0 : ReferenceData} {K : ℝ}
    (h0 : MorseChainRealization T (fun _ => 1) D0 C)
    (hcell : MorseRealizedCellEstimates T K) :
    ∃ Kconn : ℝ, 1 ≤ Kconn ∧ ∀ σ (D : ReferenceData),
      (∀ i, 1 ≤ σ i ∧ σ i ≤ 2) → MorseChainRealization T σ D C →
      ∀ side n, T.index ≤ n →
        (∫ x in T.radius side n (T.rightX side n)..morseChainResistanceEnd T side n,
          D.w x * x ^ 6) ≤ Kconn * morseChainAmplitude T σ n * morseChainA T n ^ 6 ∧
        (∫ x in T.radius side n (T.rightX side n)..morseChainResistanceEnd T side n,
          (D.w x * x ^ 8)⁻¹) ≤
            Kconn * (morseChainAmplitude T σ n)⁻¹ * (morseChainA T n ^ 4)⁻¹ := by
  obtain ⟨S, hS, hscale⟩ := exists_morseAdjacentScaleBounds T h0.d_eq
  let M := C 0 * K * D0.b ^ 6 * S
  let R := C 0 * K * S / D0.a ^ 8
  let Kconn := max 1 (max M R)
  have hKconn : 1 ≤ Kconn := le_max_left _ _
  have hMconn : M ≤ Kconn := (le_max_left _ _).trans (le_max_right _ _)
  have hRconn : R ≤ Kconn := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Kconn, hKconn, ?_⟩
  intro σ D hσ h side n hn
  have hlam : 0 < morseChainAmplitude T σ n := morseChainAmplitude_pos T σ hσ n
  have hA : 0 ≤ morseChainA T n := sq_nonneg _
  rcases morseRealizedConnector_join_or_zero h side n hn with he | ⟨k, hk, hl, hr, hindex⟩
  · rw [he, intervalIntegral.integral_same, intervalIntegral.integral_same]
    exact ⟨mul_nonneg (mul_nonneg (zero_le_one.trans hKconn) hlam.le) (pow_nonneg hA 6),
      mul_nonneg (mul_nonneg (zero_le_one.trans hKconn) (inv_nonneg.mpr hlam.le))
        (inv_nonneg.mpr (pow_nonneg hA 4))⟩
  · have hj := morseRealizedJoin_bounds h0 hcell hσ h (hscale σ hσ) side k hk
    dsimp only at hj
    rw [hindex] at hj
    rw [hl, hr]
    constructor
    · exact hj.1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMconn hlam.le) (pow_nonneg hA 6))
    · exact hj.2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hRconn (inv_nonneg.mpr hlam.le))
        (inv_nonneg.mpr (pow_nonneg hA 4)))

end ContinuousFlexibility.Radial
