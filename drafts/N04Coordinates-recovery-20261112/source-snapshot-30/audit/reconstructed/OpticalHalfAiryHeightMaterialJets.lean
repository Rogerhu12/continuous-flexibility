import ContinuousFlexibility.Analysis.OpticalHalfAiryAverage
import ContinuousFlexibility.Analysis.PositivePowerPolynomialMaterialJets
import ContinuousFlexibility.Analysis.PointwiseProductPolynomialMaterialJets

/-!
# All-order height bounds on the same complete optical half

The square-root representative is only used through its genuine germs on
the closed half. Every integral jet samples the same half. The existing
polynomial power and product calculus is specialized at the zero state;
no derivative of the representative outside the half is estimated.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem opticalHalf_material_mono {a b W : ℝ}
    (hab : a ≤ b) (hb : 0 ≤ b) (hW : 1 ≤ W) :
    a * W ^ a ≤ b * W ^ b :=
  mul_le_mul hab (Real.rpow_le_rpow_of_exponent_le hW hab)
    (Real.rpow_nonneg (zero_le_one.trans hW) _) hb

private theorem opticalHalf_power_jets (a K : ℝ) (hK : 1 ≤ K)
    (A : ℕ → ℝ) (hA : ∀ n, 1 ≤ A n) :
    ∃ B : ℕ → ℝ, (∀ n, 1 ≤ B n) ∧
      ∀ W : ℝ, 1 ≤ W → ∀ g : ℝ → ℝ, ∀ x : ℝ,
        ContDiffAt ℝ ∞ g x → 0 < g x →
        g x ≤ K * W ^ K → (g x)⁻¹ ≤ K * W ^ K →
        (∀ n, |iteratedDeriv n g x| ≤ A n * W ^ (A n)) →
        ∀ n, |iteratedDeriv n (fun y => g y ^ a) x| ≤ B n * W ^ (B n) := by
  have hp : Monotone realGrading := fun _ _ _ => le_rfl
  obtain ⟨base, loss, hmaterial⟩ := positivePower_polynomial_material_bound
    (X := ℝ) hp coordinate_hasInterpolation_realGrading 0
  obtain ⟨C, hC, hbound⟩ := hmaterial a K hK A hA
  refine ⟨(fun n => 1 + C n), (fun n => le_add_of_nonneg_right (hC n).le), ?_⟩
  intro W hW g x hg hx hvalue hinverse hj n
  have hz : realGrading base (0 : ℝ) ≤ 1 := by
    simpa only [map_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
  have hi (k : ℕ) (_hk : 1 ≤ k) : ‖iteratedFDeriv ℝ k g x‖ ≤
      A k * W ^ (A k) * (1 + realGrading (k + 0) (0 : ℝ)) := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      map_zero, add_zero, mul_one] using hj k
  have hb : |iteratedDeriv n (fun y => g y ^ a) x| ≤ C n * W ^ (C n) := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      map_zero, add_zero, mul_one] using
      hbound (0 : ℝ) hz W hW g x hg hx hvalue hinverse hi n
  exact hb.trans (opticalHalf_material_mono (le_add_of_nonneg_left zero_le_one)
    (add_nonneg zero_le_one (hC n).le) hW)

private theorem opticalHalf_product_jets (A : ℕ → ℝ) (hA : ∀ n, 1 ≤ A n) :
    ∃ B : ℕ → ℝ, (∀ n, 1 ≤ B n) ∧
      ∀ W : ℝ, 1 ≤ W → ∀ f g : ℝ → ℝ, ∀ x : ℝ,
        ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ g x →
        (∀ n, |iteratedDeriv n f x| ≤ A n * W ^ (A n)) →
        (∀ n, |iteratedDeriv n g x| ≤ A n * W ^ (A n)) →
        ∀ n, |iteratedDeriv n (fun y => f y * g y) x| ≤ B n * W ^ (B n) := by
  have hp : Monotone realGrading := fun _ _ _ => le_rfl
  obtain ⟨base, loss, hmaterial⟩ := pointwiseProduct_polynomial_material_bound
    (X := ℝ) hp coordinate_hasInterpolation_realGrading 0
  obtain ⟨C, hC, hbound⟩ := hmaterial A hA
  refine ⟨(fun n => 1 + C n), (fun n => le_add_of_nonneg_right (hC n).le), ?_⟩
  intro W hW f g x hf hg hfj hgj n
  have hz : realGrading base (0 : ℝ) ≤ 1 := by
    simpa only [map_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
  have hfj' (k : ℕ) : ‖iteratedFDeriv ℝ k f x‖ ≤
      A k * W ^ (A k) * (1 + realGrading (k + 0) (0 : ℝ)) := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      map_zero, add_zero, mul_one] using hfj k
  have hgj' (k : ℕ) : ‖iteratedFDeriv ℝ k g x‖ ≤
      A k * W ^ (A k) * (1 + realGrading (k + 0) (0 : ℝ)) := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      map_zero, add_zero, mul_one] using hgj k
  have hb : |iteratedDeriv n (fun y => f y * g y) x| ≤ C n * W ^ (C n) := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      map_zero, add_zero, mul_one] using
      hbound (0 : ℝ) hz W hW f g x hf hg hfj' hgj' n
  exact hb.trans (opticalHalf_material_mono (le_add_of_nonneg_left zero_le_one)
    (add_nonneg zero_le_one (hC n).le) hW)

/-- Every real power of the same Airy height has polynomial all-order
cost on the entire closed half. The given factor and physical profile
are the only quantitative inputs; the positive square-root extension
contributes no exterior jet or radius cost. -/
theorem opticalHalf_airyHeight_power_material_jets
    (a K : ℝ) (hK : 1 ≤ K) (A : ℕ → ℝ) (hA : ∀ n, 1 ≤ A n) :
    ∃ B : ℕ → ℝ, (∀ n, 1 ≤ B n) ∧
      ∀ E : ℝ, 1 ≤ E → ∀ g c w : ℝ → ℝ, ∀ d : ℝ,
        ContDiff ℝ ∞ g → ContDiff ℝ ∞ c →
        (∀ x ∈ Icc (0 : ℝ) d, c =ᶠ[𝓝 x] (fun y => Real.sqrt (g y))) →
        (∀ x ∈ Icc (0 : ℝ) d,
          0 < g x ∧ g x ≤ K * E ^ K ∧ (g x)⁻¹ ≤ K * E ^ K) →
        (∀ x ∈ Icc (0 : ℝ) d,
          ContDiffAt ℝ ∞ w x ∧ 0 < w x ∧
            w x ≤ K * E ^ K ∧ (w x)⁻¹ ≤ K * E ^ K) →
        (∀ n x, x ∈ Icc (0 : ℝ) d →
          |iteratedDeriv n g x| ≤ A n * E ^ (A n) ∧
          |iteratedDeriv n w x| ≤ A n * E ^ (A n)) →
        ∀ x ∈ Icc (0 : ℝ) d, ∀ n,
          |iteratedDeriv n (fun y => n06AiryRadialHeight c w y ^ a) x| ≤
            B n * E ^ (B n) := by
  obtain ⟨C, hC, hcBound⟩ := opticalHalf_power_jets (1 / 2) K hK A hA
  let AC : ℕ → ℝ := fun n => 1 + 2 * C n
  have hAC (n : ℕ) : 1 ≤ AC n :=
    le_add_of_nonneg_right (mul_nonneg (by norm_num) (zero_le_one.trans (hC n)))
  obtain ⟨D, hD, hpowBound⟩ := opticalHalf_power_jets (-1 / 3) K hK AC hAC
  let M₁ : ℕ → ℝ := fun n => max (C n) (D n)
  have hM₁ (n : ℕ) : 1 ≤ M₁ n := (hC n).trans (le_max_left _ _)
  obtain ⟨S, hS, hsBound⟩ := opticalHalf_product_jets M₁ hM₁
  let M₂ : ℕ → ℝ := fun n => max (A n) (S n)
  have hM₂ (n : ℕ) : 1 ≤ M₂ n := (hA n).trans (le_max_left _ _)
  obtain ⟨P, hP, hpBound⟩ := opticalHalf_product_jets M₂ hM₂
  let K₁ : ℝ := 1 + K ^ 3 + K * 3
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hK₁ : 1 ≤ K₁ := by
    dsimp only [K₁]
    nlinarith only [pow_nonneg hK0 3, mul_nonneg hK0 (by norm_num : (0 : ℝ) ≤ 3)]
  obtain ⟨B, hB, hheightBound⟩ := opticalHalf_power_jets (-a / 2) K₁ hK₁ P hP
  refine ⟨B, hB, ?_⟩
  intro E hE g c w d hg hc hcg hgb hwb hj
  let V : ℝ := K * E ^ K
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hV : 1 ≤ V := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ K * E ^ K := mul_le_mul hK (Real.one_le_rpow hE hK0) zero_le_one hK0
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hsmallPower {u : ℝ} (hu : 0 < u) (huV : u ≤ V) (huI : u⁻¹ ≤ V)
      (b : ℝ) (hb : |b| ≤ 1) : u ^ b ≤ V := by
    calc
      u ^ b ≤ V ^ |b| := positive_rpow_le_of_value_inverse_bounds hu huV huI b
      _ ≤ V ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hV hb
      _ = V := Real.rpow_one _
  have hcValues (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) :
      0 < c x ∧ c x ≤ V ∧ (c x)⁻¹ ≤ V := by
    have he := (hcg x hx).self_of_nhds
    have hb := hgb x hx
    refine ⟨by rw [he]; exact Real.sqrt_pos.mpr hb.1, ?_, ?_⟩
    · rw [he, Real.sqrt_eq_rpow]
      exact hsmallPower hb.1 hb.2.1 hb.2.2 (1 / 2) (by norm_num)
    · calc
        (c x)⁻¹ = g x ^ (-1 / 2 : ℝ) := by
          rw [he, Real.sqrt_eq_rpow, ← Real.rpow_neg hb.1.le]
          norm_num
        _ ≤ V := hsmallPower hb.1 hb.2.1 hb.2.2 (-1 / 2) (by norm_num)
  have hcJets (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) (n : ℕ) :
      |iteratedDeriv n c x| ≤ C n * E ^ (C n) := by
    have he : c =ᶠ[𝓝 x] (fun y => g y ^ (1 / 2 : ℝ)) :=
      (hcg x hx).trans (Eventually.of_forall (fun y => Real.sqrt_eq_rpow (g y)))
    rw [he.iteratedDeriv_eq n]
    exact hcBound E hE g x hg.contDiffAt (hgb x hx).1 (hgb x hx).2.1
      (hgb x hx).2.2 (fun k => (hj k x hx).1) n
  have hAverageValues (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) :
      0 < n06AiryAverage c x ∧ n06AiryAverage c x ≤ V ∧
        (n06AiryAverage c x)⁻¹ ≤ V := by
    have hcRange : ∀ y ∈ Icc (0 : ℝ) d, V⁻¹ ≤ c y ∧ c y ≤ V := by
      intro y hy
      refine ⟨?_, (hcValues y hy).2.1⟩
      have hh := inv_anti₀ (inv_pos.mpr (hcValues y hy).1) (hcValues y hy).2.2
      simpa only [inv_inv] using hh
    have hb := airyAverage_bounds_on_nonnegative_interval hc.continuous hx hcRange
    refine ⟨(inv_pos.mpr hVpos).trans_le hb.1, hb.2, ?_⟩
    have hh := inv_anti₀ (inv_pos.mpr hVpos) hb.1
    simpa only [inv_inv] using hh
  have hAverageJets (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) (n : ℕ) :
      |iteratedDeriv n (n06AiryAverage c) x| ≤ AC n * E ^ (AC n) := by
    have hb := airyAverage_jet_bound_on_nonnegative_interval hc n
      (mul_nonneg (zero_le_one.trans (hC n)) (Real.rpow_nonneg hE0 _)) hx
      (fun y hy => hcJets y hy n)
    have hCC : C n ≤ AC n := by
      dsimp only [AC]
      linarith only [hC n]
    calc
      _ ≤ 2 * (C n * E ^ (C n)) := hb
      _ = (2 * C n) * E ^ (C n) := by ring
      _ ≤ AC n * E ^ (AC n) := mul_le_mul
        (le_add_of_nonneg_left zero_le_one)
        (Real.rpow_le_rpow_of_exponent_le hE hCC)
        (Real.rpow_nonneg hE0 _) (zero_le_one.trans (hAC n))
  have hSlopeJets (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) (n : ℕ) :
      |iteratedDeriv n (n06AiryRadialSlope c) x| ≤ S n * E ^ (S n) := by
    have hv := hAverageValues x hx
    have hp : ContDiffAt ℝ ∞ (fun y => n06AiryAverage c y ^ (-1 / 3 : ℝ)) x :=
      (n06_contDiff_airyAverage hc).contDiffAt.rpow_const_of_ne hv.1.ne'
    apply hsBound E hE c (fun y => n06AiryAverage c y ^ (-1 / 3 : ℝ)) x
      hc.contDiffAt hp
    · intro k
      exact (hcJets x hx k).trans (opticalHalf_material_mono (le_max_left _ _)
        (zero_le_one.trans (hM₁ k)) hE)
    · intro k
      exact (hpowBound E hE (n06AiryAverage c) x (n06_contDiff_airyAverage hc).contDiffAt
        hv.1 hv.2.1 hv.2.2 (hAverageJets x hx) k).trans
        (opticalHalf_material_mono (le_max_right _ _) (zero_le_one.trans (hM₁ k)) hE)
  have hVcube : V ^ 3 ≤ K₁ * E ^ K₁ := by
    have hk : K ^ 3 ≤ K₁ := by
      dsimp only [K₁]
      nlinarith only [mul_nonneg hK0 (by norm_num : (0 : ℝ) ≤ 3)]
    have he : K * 3 ≤ K₁ := by
      dsimp only [K₁]
      linarith only [pow_nonneg hK0 3]
    calc
      V ^ 3 = K ^ 3 * E ^ (K * 3) := by
        dsimp only [V]
        rw [mul_pow, ← Real.rpow_mul_natCast hE0 K 3]
      _ ≤ K₁ * E ^ K₁ := mul_le_mul hk (Real.rpow_le_rpow_of_exponent_le hE he)
        (Real.rpow_nonneg hE0 _) (zero_le_one.trans hK₁)
  intro x hx n
  let F : ℝ → ℝ := fun y => w y * n06AiryRadialSlope c y
  have hv := hAverageValues x hx
  have hcV := hcValues x hx
  have hwV := hwb x hx
  have hs : ContDiffAt ℝ ∞ (n06AiryRadialSlope c) x :=
    hc.contDiffAt.mul ((n06_contDiff_airyAverage hc).contDiffAt.rpow_const_of_ne hv.1.ne')
  have hF : ContDiffAt ℝ ∞ F x := hwV.1.mul hs
  have hFpos : 0 < F x :=
    mul_pos hwV.2.1 (mul_pos hcV.1 (Real.rpow_pos_of_pos hv.1 _))
  have hAPow : n06AiryAverage c x ^ (-1 / 3 : ℝ) ≤ V :=
    hsmallPower hv.1 hv.2.1 hv.2.2 (-1 / 3) (by norm_num)
  have hFvalue : F x ≤ K₁ * E ^ K₁ := by
    apply le_trans _ hVcube
    calc
      F x ≤ V * (V * V) := mul_le_mul hwV.2.2.1
        (mul_le_mul hcV.2.1 hAPow (Real.rpow_nonneg hv.1.le _) hVpos.le)
        (mul_nonneg hcV.1.le (Real.rpow_nonneg hv.1.le _)) hVpos.le
      _ = V ^ 3 := by ring
  have hFinverse : (F x)⁻¹ ≤ K₁ * E ^ K₁ := by
    apply le_trans _ hVcube
    have hi : (n06AiryAverage c x ^ (-1 / 3 : ℝ))⁻¹ =
        n06AiryAverage c x ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_neg hv.1.le]
      norm_num
    change (w x * (c x * n06AiryAverage c x ^ (-1 / 3 : ℝ)))⁻¹ ≤ V ^ 3
    rw [mul_inv_rev, mul_inv_rev, hi]
    calc
      _ ≤ (V * V) * V := mul_le_mul
        (mul_le_mul (hsmallPower hv.1 hv.2.1 hv.2.2 (1 / 3) (by norm_num)) hcV.2.2
          (inv_nonneg.mpr hcV.1.le) hVpos.le)
        hwV.2.2.2 (inv_nonneg.mpr hwV.2.1.le) (mul_nonneg hVpos.le hVpos.le)
      _ = V ^ 3 := by ring
  have hFjets (k : ℕ) : |iteratedDeriv k F x| ≤ P k * E ^ (P k) := by
    apply hpBound E hE w (n06AiryRadialSlope c) x hwV.1 hs
    · intro j
      exact (hj j x hx).2.trans (opticalHalf_material_mono (le_max_left _ _)
        (zero_le_one.trans (hM₂ j)) hE)
    · intro j
      exact (hSlopeJets x hx j).trans (opticalHalf_material_mono (le_max_right _ _)
        (zero_le_one.trans (hM₂ j)) hE)
  have he : (fun y => n06AiryRadialHeight c w y ^ a) =ᶠ[𝓝 x]
      (fun y => F y ^ (-a / 2)) := by
    filter_upwards [hF.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hFpos)] with y hy
    change (F y ^ (-1 / 2 : ℝ)) ^ a = F y ^ (-a / 2)
    rw [← Real.rpow_mul (le_of_lt hy)]
    congr 1
    ring
  rw [he.iteratedDeriv_eq n]
  exact hheightBound E hE F x hF hFpos hFvalue hFinverse hFjets n

end ContinuousFlexibility.Analysis
