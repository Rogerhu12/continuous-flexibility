import ContinuousFlexibility.Radial.OuterMorseLocalizedDensity

/-!
# The manuscript bounds for one actual outer inverse

The same core factor is used in all four estimates:
`exp (Cbound * n² + Co * τ)`. The weighted global operator and every
weighted localization are the operators already carried by the actual
Green data. Each ordinary localized operator has the same negative
localized kernel; no global unweighted bound is asserted.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

def morseOuterCoreFactor (M : MorseChainData) (n j : ℕ) (Cbound Co : ℝ) : ℝ :=
  exp (Cbound * (n : ℝ) ^ 2 + Co * ((j : ℝ) * sqrt (morseChainA M n)))

theorem morseOuterCoreFactor_pos (M : MorseChainData) (n j : ℕ) (Cbound Co : ℝ) :
    0 < morseOuterCoreFactor M n j Cbound Co :=
  exp_pos _

theorem morseOuter_action_le_coreFactor (M : MorseChainData) (n j : ℕ)
    {Cbound Co : ℝ} (hCb : 0 ≤ Cbound) :
    exp (Co * ((j : ℝ) * sqrt (morseChainA M n))) ≤
      morseOuterCoreFactor M n j Cbound Co :=
  exp_le_exp.mpr (le_add_of_nonneg_left (mul_nonneg hCb (sq_nonneg _)))

/-- The valid global and localized conclusions of Lemma 6.5, for the same
operator and normalized natural vector. The ordinary conclusion is local. -/
structure MorseOuterInverseBounds
    {M : MorseChainData} {D : ReferenceData} {right : Bool} {n j : ℕ}
    {entry η K lam Cbound Co : ℝ}
    (G : MorseOuterGreenData M D right n j entry η K lam Cbound Co)
    (hpart : RadialPartition D) (Cenv : ℝ) : Prop where
  natural_bound : ‖G.inverse.natural_memLp.toLp G.pair.V‖ ≤
    sqrt lam * radialE n ^ Cenv * morseOuterCoreFactor M n j Cbound Co
  operator_bound : ‖G.inverse.operator‖ ≤
    radialE n ^ Cenv * morseOuterCoreFactor M n j Cbound Co ^ 2
  localized_bound : ∀ k m : ℕ,
    ‖outerWholeLocalizedOperator hpart right
        (morseTransitionPhysicalEntry M entry right n) k m G.inverse.operator‖ ≤
      radialE (D.cellIndex k) ^ Cenv * radialE (D.cellIndex m) ^ Cenv *
        morseOuterCoreFactor M n j Cbound Co ^ 2 *
          exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|)
  ordinary_bound : ∀ k m : ℕ,
    let μ := volume.restrict
      (Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
        (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    ∃ A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      ‖A‖ ≤ radialE (D.cellIndex k) ^ Cenv * radialE (D.cellIndex m) ^ Cenv *
        morseOuterCoreFactor M n j Cbound Co ^ 2 *
          exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|) ∧
      ∀ f : Lp ℝ 2 μ, (A f : ℝ → ℝ) =ᵐ[μ] fun x =>
        -(∫ y, outerWholeLocalizedKernel D right k m
          (outerGreenKernel lam G.pair.U G.pair.V) x y * f y ∂μ)

private theorem outer_pair_bound_enlarge
    {p q : ℕ} {W C act newAct attenuation : ℝ}
    (hW : W ≤ C) (hact : 0 ≤ act) (hA : act ≤ newAct) (hatt : 0 ≤ attenuation) :
    radialE p ^ W * radialE q ^ W * act * attenuation ≤
      radialE p ^ C * radialE q ^ C * newAct * attenuation := by
  have hp := outer_envelope_exponent_mono p hW
  have hq := outer_envelope_exponent_mono q hW
  have hp0 : 0 ≤ radialE p ^ C := rpow_nonneg (show 0 ≤ radialE p from (exp_pos _).le) _
  have hq0 : 0 ≤ radialE q ^ W := rpow_nonneg (show 0 ≤ radialE q from (exp_pos _).le) _
  have hqC0 : 0 ≤ radialE q ^ C := rpow_nonneg (show 0 ≤ radialE q from (exp_pos _).le) _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul hp hq hq0 hp0) hA hact (mul_nonneg hp0 hqC0)) hatt

/-- The actual pointwise kernel estimate, actual support labels, and
already constructed Green data imply every final norm bound. All three
exponents may be enlarged to one common exponent selected in advance. -/
theorem MorseOuterGreenData.manuscript_bounds
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {right : Bool} {n j : ℕ} {entry η K lam Cbound Co a b Q Cenv : ℝ}
    (G : MorseOuterGreenData M D right n j entry η K lam Cbound Co)
    (h : MorseChainRealization M σ D C) (hpart : RadialPartition D)
    (ha : D.a = a) (hb : D.b = b)
    (he : entry ∈ morseInitialMiddle M) (hN : M.index + 3 ≤ n)
    (hlabels : MorseOuterLocalizerLabels M D n) (hlam : 0 < lam)
    (hCb : 0 ≤ Cbound) (hQ : 0 ≤ Q) (hCenv : Cbound ≤ Cenv)
    (hW : outerMorseOperatorExponent a b C Q hQ ≤ Cenv)
    (hO : outerMorseOrdinaryExponent a b C Q hQ ≤ Cenv)
    (hpoint : ∀ p q x y, MorseOuterPoint M D entry right j n η K p x →
      MorseOuterPoint M D entry right j n η K q y →
      |outerGreenKernel lam G.pair.U G.pair.V x y| ≤
        radialE p ^ Q * radialE q ^ Q *
          exp (Co * ((j : ℝ) * sqrt (morseChainA M n))) ^ 2 *
            exp (-|radialS p - radialS q|)) :
    MorseOuterInverseBounds G hpart Cenv := by
  have hKn := morseOuter_action_le_coreFactor M n j hCb
  have hKn2 := pow_le_pow_left₀ (exp_pos _).le hKn 2
  have hweight := outer_envelope_exponent_mono n hCenv
  have hweight0 : 0 ≤ radialE n ^ Cenv :=
    rpow_nonneg (show 0 ≤ radialE n from (exp_pos _).le) _
  have hsqrt : 0 ≤ sqrt lam := (sqrt_pos.mpr hlam).le
  refine {
    natural_bound := G.natural_bound.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hweight hsqrt) hKn
        (exp_pos _).le (mul_nonneg hsqrt hweight0))
    operator_bound := G.operator_bound.trans
      (mul_le_mul hweight hKn2 (sq_nonneg _) hweight0)
    localized_bound := ?_
    ordinary_bound := ?_
  }
  · intro k m
    have hraw := G.localized_norm_le h ha hb he hN hlabels hQ (sq_nonneg _) hpoint k m
    exact hraw.trans (outer_pair_bound_enlarge hW (sq_nonneg _) hKn2 (exp_pos _).le)
  · intro k m
    obtain ⟨A, hAnorm, hAkernel⟩ := G.exists_localized_ordinary h ha hb he hN hlabels
      hQ (sq_nonneg _) hpoint k m
    exact ⟨A, hAnorm.trans (outer_pair_bound_enlarge hO (sq_nonneg _) hKn2 (exp_pos _).le),
      hAkernel⟩

end ContinuousFlexibility.Radial
