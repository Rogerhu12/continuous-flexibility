import ContinuousFlexibility.Radial.MatchedModeWeightedCells
import ContinuousFlexibility.Radial.MatchingGraphRestrictions

/-!
# Cell decay from actual supported weighted columns

Finite-chain weights keep their original extension by one outside the
inner region. Only their values where an actual localizer is nonzero and the
original vector is supported enter the estimate. Null cut endpoints are
allowed. The scalar channel still has weight one and level zero.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory ContinuousFlexibility.Statements

/-- A single supported vector only pays an inverse weight on its own
support. This is a vector estimate, so no bound on irrelevant exterior
values of the finite-chain weight is required. -/
theorem matchedMode_supported_channel_norm_le
    (D : ReferenceData) (hP : RadialPartition D)
    (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (inverseWeight : ℝ → ℝ)
    (hE : ∀ f, E.symm f =ᵐ[radialHilbertMeasure D]
      fun x => inverseWeight x * f x)
    (P : RadialModePair D) (s : Set ℝ)
    (hsupp : ∀ᵐ x ∂radialHilbertMeasure D, x ∉ s → P.1 x = 0)
    (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (hA₀ : 1 ≤ A 0)
    (hlocal : ∀ m, ∀ᵐ x ∂radialHilbertMeasure D,
      D.localizer m x ≠ 0 → x ∈ s → |inverseWeight x| ≤ A (m + 1)) (k : ℕ) :
    ‖matchedModeChannel D hP k P‖ ≤
      A k * ‖E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) P‖ := by
  let EP := E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) P
  cases k with
  | zero =>
      change ‖matchedModeBorder D P‖ ≤ A 0 * ‖EP‖
      rw [matchedModeBorder_norm]
      have hs : ‖P.2‖ ≤ ‖EP‖ := norm_snd_le EP
      exact hs.trans
        ((by rw [one_mul] : ‖EP‖ = 1 * ‖EP‖).le.trans
          (mul_le_mul_of_nonneg_right hA₀ (norm_nonneg EP)))
  | succ m =>
      change ‖(matchedModeCellL2 D hP m P.1, (0 : ℝ))‖ ≤ A (m + 1) * ‖EP‖
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      have he : (P.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
          fun x => inverseWeight x * E P.1 x := by
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hE (E P.1)
      have hf : ‖matchedModeCellL2 D hP m P.1‖ ≤ A (m + 1) * ‖E P.1‖ := by
        apply Lp.norm_le_mul_norm_of_ae_le_mul
        filter_upwards [matchedModeCellL2_ae D hP m P.1, he, hsupp, hlocal m]
          with x hc heq hz hb
        by_cases hχ : D.localizer m x = 0
        · rw [hc, hχ, zero_mul, norm_zero]
          exact mul_nonneg (hA _) (norm_nonneg _)
        by_cases hxs : x ∈ s
        · have hcoef : |D.localizer m x * inverseWeight x| ≤ A (m + 1) := by
            rw [abs_mul]
            exact (mul_le_mul (matchedRadialLocalizer_abs_le_one hP m x)
              (hb hχ hxs) (abs_nonneg _) zero_le_one).trans_eq
                (one_mul _)
          rw [hc, heq, ← mul_assoc, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
        · rw [hc, hz hxs, mul_zero, norm_zero]
          exact mul_nonneg (hA _) (norm_nonneg _)
      have hefield : ‖E P.1‖ ≤ ‖EP‖ := norm_fst_le EP
      exact hf.trans (mul_le_mul_of_nonneg_left hefield (hA _))

/-- Two signs retain the full height-distance decay using only the
actual support intersection. Both signs act on the same original vector. -/
theorem matchedMode_twoSign_supported_column_envelope
    (D : ReferenceData) (hP : RadialPartition D) (P : RadialModePair D) (n : ℕ)
    (level : ℕ → ℕ) (hlevel : level 0 = 0)
    (support : Set ℝ)
    (hsupp : ∀ᵐ x ∂radialHilbertMeasure D, x ∉ support → P.1 x = 0)
    (W : Bool → ℝ → ℝ) (hW : ∀ sign, Measurable (W sign))
    (hw : ∀ sign x, 0 < W sign x)
    (B V : Bool → ℝ)
    (hB : ∀ sign x, |W sign x| ≤ B sign)
    (hV : ∀ sign x, |(W sign x)⁻¹| ≤ V sign)
    {C R a : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hweighted : ∀ sign : Bool,
      ‖matchedModeActualWeight D (W sign) (hW sign) (hw sign)
        (B sign) (V sign) (hB sign) (hV sign) P‖ ≤
          C * Real.exp (a * radialQ n + (if sign then radialS n else -radialS n)))
    (hlocal : ∀ sign m, ∀ᵐ x ∂radialHilbertMeasure D,
      D.localizer m x ≠ 0 → x ∈ support →
        |(W sign x)⁻¹| ≤ R * Real.exp
          (a * radialQ (level (m + 1)) -
            (if sign then radialS (level (m + 1)) else -radialS (level (m + 1)))))
    (k : ℕ) :
    ‖matchedModeChannel D hP k P‖ ≤ C * R * Real.exp
      (a * (radialQ (level k) + radialQ n) -
        |radialS (level k) - radialS n|) := by
  let height : Bool → ℕ → ℝ := fun sign j => if sign then radialS j else -radialS j
  let A : Bool → ℕ → ℝ := fun sign j =>
    R * Real.exp (a * radialQ (level j) - height sign (level j))
  have hR₀ : 0 ≤ R := zero_le_one.trans hR
  have hA : ∀ sign j, 0 ≤ A sign j :=
    fun sign j => mul_nonneg hR₀ (Real.exp_pos _).le
  have hq₀ : radialQ 0 = 0 := by norm_num [radialQ]
  have hs₀ : radialS 0 = 0 := by norm_num [radialS]
  have hA₀ : ∀ sign, 1 ≤ A sign 0 := by
    intro sign
    simpa only [A, height, hlevel, hq₀, hs₀, neg_zero,
      ite_self, mul_zero, sub_zero, Real.exp_zero, mul_one] using hR
  have hsign (sign : Bool) :
      ‖matchedModeChannel D hP k P‖ ≤ C * R * Real.exp
        (a * (radialQ (level k) + radialQ n) -
          height sign (level k) + height sign n) := by
    let E := innerWeightEquiv (radialHilbertMeasure D)
      (W sign) (hW sign) (hw sign) (B sign) (V sign) (hB sign) (hV sign)
    have he : ∀ f, E.symm f =ᵐ[radialHilbertMeasure D]
        fun x => (W sign x)⁻¹ * f x :=
      innerWeightEquiv_symm_ae (radialHilbertMeasure D)
        (W sign) (hW sign) (hw sign) (B sign) (V sign) (hB sign) (hV sign)
    have hc := matchedMode_supported_channel_norm_le D hP E (fun x => (W sign x)⁻¹)
      he P support hsupp (A sign) (hA sign) (hA₀ sign)
      (fun m => hlocal sign m) k
    have hp : ‖E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) P‖ ≤
        C * Real.exp (a * radialQ n + height sign n) := hweighted sign
    calc
      _ ≤ A sign k * (C * Real.exp (a * radialQ n + height sign n)) :=
        hc.trans (mul_le_mul_of_nonneg_left hp (hA sign k))
      _ = _ := by
        dsimp only [A]
        rw [show a * (radialQ (level k) + radialQ n) -
            height sign (level k) + height sign n =
          (a * radialQ (level k) - height sign (level k)) +
            (a * radialQ n + height sign n) by ring]
        simp only [Real.exp_add]
        ring
  by_cases hkn : radialS n ≤ radialS (level k)
  · calc
      _ ≤ _ := hsign true
      _ = _ := by
        change C * R * Real.exp (a * (radialQ (level k) + radialQ n) -
          radialS (level k) + radialS n) = C * R * Real.exp
            (a * (radialQ (level k) + radialQ n) - |radialS (level k) - radialS n|)
        rw [abs_of_nonneg (sub_nonneg.mpr hkn)]
        congr 2
        ring
  · calc
      _ ≤ _ := hsign false
      _ = _ := by
        change C * R * Real.exp (a * (radialQ (level k) + radialQ n) -
          (-radialS (level k)) + (-radialS n)) = C * R * Real.exp
            (a * (radialQ (level k) + radialQ n) - |radialS (level k) - radialS n|)
        rw [abs_of_nonpos (sub_nonpos.mpr (lt_of_not_ge hkn).le)]
        congr 2
        ring

/-- The support needed above is a consequence of the original frozen
matching realization, not an additional hypothesis on its inner column. -/
theorem matchedInnerPoisson_supported {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M) (i : Fin 2) :
    ∀ᵐ x ∂radialHilbertMeasure D,
      x ∉ Ioo M.innerLeft M.innerRight → (M.innerPoisson i).1 x = 0 := by
  have hs := (hM.2.2.2.1 (M.innerPoisson i)).2.2.1
  rw [matching_sourceInner_innerPoisson hD hM i] at hs
  filter_upwards [hs] with x hx hout
  simpa only [if_neg hout] using hx

end ContinuousFlexibility.Radial
