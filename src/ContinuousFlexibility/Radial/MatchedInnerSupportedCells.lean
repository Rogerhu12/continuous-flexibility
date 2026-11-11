import ContinuousFlexibility.Radial.MatchedSupportedColumnCells
import ContinuousFlexibility.Radial.MatchedInnerWeightTransport

/-!
# The actual inner cell kernel with finite-region weights

The original inner source map supplies the input restriction and the
original inner representative supplies the output support. Weights are
only compared where the actual localizer is nonzero in that region. In particular their
unchanged extension by one outside the finite chain causes no loss or
additional hypothesis. The frequency scalar gate is retained throughout.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory ContinuousFlexibility.Statements

theorem matchedInner_source_gate_idempotent {D : ReferenceData}
    (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
    (active : Bool) (F : RadialModePair D) :
    M.sourceInner (matchedModeScalarGate D active
      (M.sourceInner (matchedModeScalarGate D active F))) =
        M.sourceInner (matchedModeScalarGate D active F) := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(hM.2.2.2.1 (matchedModeScalarGate D active
      (M.sourceInner (matchedModeScalarGate D active F)))).2.2.1,
      (hM.2.2.2.1 (matchedModeScalarGate D active F)).2.2.1] with x hl hr
    rw [hl]
    change (if x ∈ Ioo M.innerLeft M.innerRight then
      (M.sourceInner (matchedModeScalarGate D active F)).1 x else 0) =
        (M.sourceInner (matchedModeScalarGate D active F)).1 x
    simp only [hr]
    split_ifs <;> rfl
  · rw [(hM.2.2.2.1 _).1]
    change (if active then (M.sourceInner (matchedModeScalarGate D active F)).2 else 0) =
      (M.sourceInner (matchedModeScalarGate D active F)).2
    simp only [(hM.2.2.2.1 (matchedModeScalarGate D active F)).1,
      matchedModeScalarGate_apply]
    cases active <;> rfl

/-- The actual inner inverse has the original finite inner support. -/
theorem matchedInnerInverse_supported {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M) (F : RadialModePair D) :
    ∀ᵐ x ∂radialHilbertMeasure D, x ∉ Ioo M.innerLeft M.innerRight →
      (M.innerInverse (M.sourceInner F)).1 x = 0 := by
  have hr := hM.2.2.2.2.1 F
  filter_upwards [hr.1, matching_ae_inner_or_outer hD M] with x hx hs hout
  rcases hs with hin | hext
  · exact False.elim (hout hin)
  · exact hx.trans (hr.2.2.2.2.2.2.1 x hext)

/-- The input weight is only paid after the true source restriction.
The scalar cell and ordinary field cells use the same actual map. -/
theorem matchedInner_sourceCell_weighted_norm_le {D : ReferenceData}
    (hP : RadialPartition D) (M : RadialMatchingData D)
    (hM : MatchingLocalRealizations D M)
    (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (weight : ℝ → ℝ)
    (hE : ∀ f, E f =ᵐ[radialHilbertMeasure D] fun x => weight x * f x)
    (active : Bool) (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hB₀ : 1 ≤ B 0)
    (hlocal : ∀ m, ∀ᵐ x ∂radialHilbertMeasure D,
      D.localizer m x ≠ 0 → x ∈ Ioo M.innerLeft M.innerRight → |weight x| ≤ B (m + 1))
    (m : ℕ) (F : RadialModePair D) :
    ‖E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
      (M.sourceInner (matchedModeScalarGate D active (matchedModeChannel D hP m F)))‖ ≤
      B m * ‖F‖ := by
  cases m with
  | zero =>
      rw [← matchedInner_sourceInner_weight_commute M hM E weight hE]
      apply (matchedInner_sourceInner_norm_le M hM _).trans
      change ‖(E 0, if active then F.2 else (0 : ℝ))‖ ≤ B 0 * ‖F‖
      rw [map_zero, Prod.norm_def, norm_zero]
      have hs : ‖(if active then F.2 else (0 : ℝ))‖ ≤ ‖F‖ := by
        cases active
        · simpa using norm_nonneg F
        · exact norm_snd_le F
      rw [max_eq_right (norm_nonneg _)]
      exact hs.trans ((by rw [one_mul] : ‖F‖ = 1 * ‖F‖).le.trans
        (mul_le_mul_of_nonneg_right hB₀ (norm_nonneg F)))
  | succ m =>
      have hg : matchedModeScalarGate D active (matchedModeChannel D hP (m + 1) F) =
          matchedModeChannel D hP (m + 1) F :=
        matchedModeScalarGate_eq_self D active _ (fun _ => rfl)
      rw [hg, ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply,
        Prod.norm_def, (hM.2.2.2.1 _).1]
      change max ‖E (M.sourceInner (matchedModeChannel D hP (m + 1) F)).1‖ ‖(0 : ℝ)‖ ≤
        B (m + 1) * ‖F‖
      rw [norm_zero, max_eq_left (norm_nonneg _)]
      have hf : ‖E (M.sourceInner (matchedModeChannel D hP (m + 1) F)).1‖ ≤
          B (m + 1) * ‖F.1‖ := by
        apply Lp.norm_le_mul_norm_of_ae_le_mul
        filter_upwards [hE (M.sourceInner (matchedModeChannel D hP (m + 1) F)).1,
          (hM.2.2.2.1 (matchedModeChannel D hP (m + 1) F)).2.2.1,
          matchedModeCellL2_ae D hP m F.1, hlocal m] with x he hs hc hb
        rw [he, hs]
        by_cases hi : x ∈ Ioo M.innerLeft M.innerRight
        · rw [if_pos hi]
          change ‖weight x * matchedModeCellL2 D hP m F.1 x‖ ≤ B (m + 1) * ‖F.1 x‖
          rw [hc]
          by_cases hχ : D.localizer m x = 0
          · rw [hχ, zero_mul, mul_zero, norm_zero]
            exact mul_nonneg (hB _) (norm_nonneg _)
          · have hcoef : |weight x * D.localizer m x| ≤ B (m + 1) := by
              rw [abs_mul]
              exact (mul_le_mul (hb hχ hi)
                (matchedRadialLocalizer_abs_le_one hP m x) (abs_nonneg _) (hB _)).trans_eq
                  (mul_one _)
            rw [← mul_assoc, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
        · rw [if_neg hi, mul_zero, norm_zero]
          exact mul_nonneg (hB _) (norm_nonneg _)
      exact hf.trans (mul_le_mul_of_nonneg_left (norm_fst_le F) (hB _))

section Kernel

variable {D : ReferenceData} (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)

local notation "T" => M.innerInverse ∘L matchingSourceInnerCLM D M hM ∘L
  matchedModeScalarGate D (decide (M.frequency = 2))

include hD

/-- Both weighted realizations of the same restricted inner inverse
give its true two-cell kernel. Weight comparisons only concern the
actual finite inner region. -/
theorem matchedInner_twoSign_supported_cell_envelope
    (level : ℕ → ℕ) (hlevel : level 0 = 0)
    (Wo Wi : Bool → ℝ → ℝ)
    (hWo : ∀ sign, Measurable (Wo sign)) (hWi : ∀ sign, Measurable (Wi sign))
    (ho : ∀ sign x, 0 < Wo sign x) (hi : ∀ sign x, 0 < Wi sign x)
    (Bo Co Bi Ci : Bool → ℝ)
    (hBo : ∀ sign x, |Wo sign x| ≤ Bo sign)
    (hCo : ∀ sign x, |(Wo sign x)⁻¹| ≤ Co sign)
    (hBi : ∀ sign x, |Wi sign x| ≤ Bi sign)
    (hCi : ∀ sign x, |(Wi sign x)⁻¹| ≤ Ci sign)
    {C R a : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hweighted : ∀ sign : Bool,
      ‖(matchedModeActualWeight D (Wo sign) (hWo sign) (ho sign)
          (Bo sign) (Co sign) (hBo sign) (hCo sign) : RadialModePair D →L[ℝ] RadialModePair D) ∘L
        T ∘L
        ((matchedModeActualWeight D (Wi sign) (hWi sign) (hi sign)
          (Bi sign) (Ci sign) (hBi sign) (hCi sign)).symm :
            RadialModePair D →L[ℝ] RadialModePair D)‖ ≤ C)
    (hlocal : ∀ sign m, ∀ᵐ x ∂radialHilbertMeasure D,
      D.localizer m x ≠ 0 → x ∈ Ioo M.innerLeft M.innerRight →
        |(Wo sign x)⁻¹| ≤ R * Real.exp (a * radialQ (level (m + 1)) -
          (if sign then radialS (level (m + 1)) else -radialS (level (m + 1)))) ∧
        |Wi sign x| ≤ R * Real.exp (a * radialQ (level (m + 1)) +
          (if sign then radialS (level (m + 1)) else -radialS (level (m + 1)))))
    (k m : ℕ) :
    ‖matchedModeChannel D hP k ∘L T ∘L matchedModeChannel D hP m‖ ≤
      C * R ^ 2 * Real.exp
        (a * (radialQ (level k) + radialQ (level m)) -
          |radialS (level k) - radialS (level m)|) := by
  have hR₀ : 0 ≤ R := zero_le_one.trans hR
  let height : Bool → ℕ → ℝ := fun sign j => if sign then radialS j else -radialS j
  let B : Bool → ℕ → ℝ := fun sign j =>
    R * Real.exp (a * radialQ (level j) + height sign (level j))
  have hB : ∀ sign j, 0 ≤ B sign j := fun _ _ => mul_nonneg hR₀ (Real.exp_pos _).le
  have hB₀ : ∀ sign, 1 ≤ B sign 0 := by
    intro sign
    simpa only [B, height, hlevel,
      show radialQ 0 = 0 by norm_num [radialQ],
      show radialS 0 = 0 by norm_num [radialS],
      neg_zero, ite_self, mul_zero, add_zero, Real.exp_zero, mul_one] using hR
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro F
  let Fcell := matchedModeChannel D hP m F
  let X := M.sourceInner (matchedModeScalarGate D (decide (M.frequency = 2)) Fcell)
  have hTX : T X = T Fcell := by
    simp only [ContinuousLinearMap.comp_apply, matchingSourceInnerCLM_apply]
    exact congrArg M.innerInverse
      (matchedInner_source_gate_idempotent M hM (decide (M.frequency = 2)) Fcell)
  have hsupp : ∀ᵐ x ∂radialHilbertMeasure D, x ∉ Ioo M.innerLeft M.innerRight →
      (T Fcell).1 x = 0 :=
    matchedInnerInverse_supported hD hM
      (matchedModeScalarGate D (decide (M.frequency = 2)) Fcell)
  have hcolumn : ∀ sign : Bool,
      ‖matchedModeActualWeight D (Wo sign) (hWo sign) (ho sign)
        (Bo sign) (Co sign) (hBo sign) (hCo sign) (T Fcell)‖ ≤
      (C * R * ‖F‖) * Real.exp (a * radialQ (level m) + height sign (level m)) := by
    intro sign
    let Ei := innerWeightEquiv (radialHilbertMeasure D)
      (Wi sign) (hWi sign) (hi sign) (Bi sign) (Ci sign) (hBi sign) (hCi sign)
    let Eo := matchedModeActualWeight D (Wo sign) (hWo sign) (ho sign)
      (Bo sign) (Co sign) (hBo sign) (hCo sign)
    let EiPair := Ei.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
    have hei : ∀ f, Ei f =ᵐ[radialHilbertMeasure D] fun x => Wi sign x * f x :=
      innerWeightEquiv_ae (radialHilbertMeasure D)
        (Wi sign) (hWi sign) (hi sign) (Bi sign) (Ci sign) (hBi sign) (hCi sign)
    have hin : ‖EiPair X‖ ≤ B sign m * ‖F‖ :=
      matchedInner_sourceCell_weighted_norm_le hP M hM Ei (Wi sign) hei
        (decide (M.frequency = 2)) (B sign) (hB sign) (hB₀ sign)
        (fun j => (hlocal sign j).mono fun _ hx hχ hi => (hx hχ hi).2) m F
    have hmid : ‖Eo (T X)‖ ≤ C * ‖EiPair X‖ := by
      have hh := ((Eo : RadialModePair D →L[ℝ] RadialModePair D) ∘L T ∘L
        (EiPair.symm : RadialModePair D →L[ℝ] RadialModePair D)).le_opNorm (EiPair X)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (hweighted sign) (norm_nonneg _))
    rw [hTX] at hmid
    exact (hmid.trans (mul_le_mul_of_nonneg_left hin hC)).trans_eq (by dsimp only [B]; ring)

  have hp := matchedMode_twoSign_supported_column_envelope D hP (T Fcell) (level m) level hlevel
    (Ioo M.innerLeft M.innerRight) hsupp Wo hWo ho Bo Co hBo hCo
    (mul_nonneg (mul_nonneg hC hR₀) (norm_nonneg F)) hR hcolumn
    (fun sign j => (hlocal sign j).mono fun _ hx hχ hi => (hx hχ hi).1) k
  change ‖matchedModeChannel D hP k (T Fcell)‖ ≤ _
  convert hp using 1 <;> ring

end Kernel

end ContinuousFlexibility.Radial
