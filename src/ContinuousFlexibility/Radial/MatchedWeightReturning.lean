module

public import ContinuousFlexibility.Radial.MatchedWeightSuppression
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Returning-block norms after paying the matching margin

The three maps are the already weighted inner column, matching matrix,
and outer source column. Their composition is estimated with the actual
margin lower bound and the cross-exponent suppression. The intermediate
boundary spaces may in particular be the two-dimensional matching spaces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real

/-- A positive exponential lower bound for the actual matching margin
gives its precise reciprocal cost. -/
theorem matched_margin_inverse_bound {c₀ margin indexCost : ℝ}
    (hc₀ : 0 < c₀) (hmargin : c₀ * exp (-indexCost) ≤ margin) :
    margin⁻¹ ≤ c₀⁻¹ * exp indexCost := by
  have hlow : 0 < c₀ * exp (-indexCost) := mul_pos hc₀ (exp_pos _)
  calc
    margin⁻¹ = 1 / margin := (one_div margin).symm
    _ ≤ 1 / (c₀ * exp (-indexCost)) := one_div_le_one_div_of_le hlow hmargin
    _ = c₀⁻¹ * exp indexCost := by
      rw [one_div, mul_inv_rev, ← exp_neg, neg_neg]
      ring

/-- Paying the three column bounds and the actual inverse-margin cost
leaves half the inward action. The second conclusion is the uniform bound. -/
theorem matched_returning_composition_bounds {E B₁ B₂ F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B₁] [NormedSpace ℝ B₁]
    [NormedAddCommGroup B₂] [NormedSpace ℝ B₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : B₂ →L[ℝ] F) (M : B₁ →L[ℝ] B₂) (V : E →L[ℝ] B₁)
    {CP CM CV c₀ margin a b q indexCost Co c tin tout C : ℝ}
    (hCP : 0 ≤ CP) (hCM : 0 ≤ CM) (hCV : 0 ≤ CV)
    (hc₀ : 0 < c₀) (hc : 0 ≤ c) (htin : 0 ≤ tin)
    (hmargin : c₀ * exp (-indexCost) ≤ margin)
    (hP : ‖P‖ ≤ CP * exp (a * q - c * tin))
    (hM : ‖M‖ ≤ CM / margin)
    (hV : ‖V‖ ≤ CV * exp (b * q + Co * tout))
    (hcost : (a + b) * q + indexCost + Co * tout - c * tin ≤ C - c / 2 * tin) :
    ‖P.comp (M.comp V)‖ ≤
        ((CP * CM * CV / c₀) * exp C) * exp (-(c / 2 * tin)) ∧
      ‖P.comp (M.comp V)‖ ≤ (CP * CM * CV / c₀) * exp C := by
  have hmarginInv := matched_margin_inverse_bound hc₀ hmargin
  have hM' : ‖M‖ ≤ (CM * c₀⁻¹) * exp indexCost := by
    calc
      ‖M‖ ≤ CM / margin := hM
      _ = CM * margin⁻¹ := div_eq_mul_inv _ _
      _ ≤ CM * (c₀⁻¹ * exp indexCost) := mul_le_mul_of_nonneg_left hmarginInv hCM
      _ = (CM * c₀⁻¹) * exp indexCost := (mul_assoc _ _ _).symm
  have hP0 : 0 ≤ CP * exp (a * q - c * tin) := mul_nonneg hCP (exp_pos _).le
  have hM0 : 0 ≤ (CM * c₀⁻¹) * exp indexCost :=
    mul_nonneg (mul_nonneg hCM (inv_nonneg.mpr hc₀.le)) (exp_pos _).le
  have hcoef : 0 ≤ CP * CM * CV / c₀ :=
    div_nonneg (mul_nonneg (mul_nonneg hCP hCM) hCV) hc₀.le
  have hexp : exp (a * q - c * tin) * exp indexCost * exp (b * q + Co * tout) =
      exp ((a + b) * q + indexCost + Co * tout - c * tin) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  have hdecay : ‖P.comp (M.comp V)‖ ≤
      ((CP * CM * CV / c₀) * exp C) * exp (-(c / 2 * tin)) := by
    calc
      ‖P.comp (M.comp V)‖ ≤ ‖P‖ * ‖M.comp V‖ := P.opNorm_comp_le _
      _ ≤ ‖P‖ * (‖M‖ * ‖V‖) :=
        mul_le_mul_of_nonneg_left (M.opNorm_comp_le V) (norm_nonneg P)
      _ ≤ (CP * exp (a * q - c * tin)) *
          (((CM * c₀⁻¹) * exp indexCost) * (CV * exp (b * q + Co * tout))) :=
        mul_le_mul hP (mul_le_mul hM' hV (norm_nonneg V) hM0)
          (mul_nonneg (norm_nonneg M) (norm_nonneg V)) hP0
      _ = (CP * CM * CV / c₀) *
          exp ((a + b) * q + indexCost + Co * tout - c * tin) := by
        rw [← hexp]
        ring
      _ ≤ (CP * CM * CV / c₀) * exp (C - c / 2 * tin) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hcost) hcoef
      _ = ((CP * CM * CV / c₀) * exp C) * exp (-(c / 2 * tin)) := by
        rw [sub_eq_add_neg, exp_add]
        ring
  have hpref : 0 ≤ (CP * CM * CV / c₀) * exp C := mul_nonneg hcoef (exp_pos _).le
  have hdecayFactor : exp (-(c / 2 * tin)) ≤ 1 :=
    exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (div_nonneg hc (by norm_num)) htin))
  exact ⟨hdecay, hdecay.trans (mul_le_of_le_one_right hpref hdecayFactor)⟩

end ContinuousFlexibility.Radial
