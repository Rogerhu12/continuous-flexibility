import ContinuousFlexibility.Analysis.CircleSmoothReconstruction

/-!
# Continuous evaluation from two angular L² classes

The actual value class and its weak first derivative determine point
values through three continuous L² pairings. This finite-level lemma is
independent of the unfinished higher-jet evaluation construction.
-/

open Set Filter MeasureTheory
open scoped ContDiff ENNReal RealInnerProductSpace Topology

namespace ContinuousFlexibility.Statements

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem angleMeasure_univ_for_evaluation :
    angleMeasure univ = ENNReal.ofReal Real.pi := by
  rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]

private theorem angleMeasure_finite_for_evaluation : IsFiniteMeasure angleMeasure :=
  ⟨by
    rw [angleMeasure_univ_for_evaluation]
    exact ENNReal.ofReal_lt_top⟩

private theorem memLp_angleOne : MemLp (fun _ : ℝ => (1 : ℝ)) 2 angleMeasure :=
  memLp_angleMeasure_of_continuous continuous_const

private theorem memLp_angleIdentity : MemLp (fun x : ℝ => x) 2 angleMeasure :=
  memLp_angleMeasure_of_continuous continuous_id

/-- Test for the actual integral from zero to the indicated angle. -/
def anglePrefixTest (y : ℝ) : ℝ → ℝ :=
  (Ioc (0 : ℝ) y).indicator (fun _ => 1)

theorem memLp_anglePrefixTest (y : ℝ) : MemLp (anglePrefixTest y) 2 angleMeasure :=
  memLp_angleOne.indicator measurableSet_Ioc

theorem angleL2TestPairing_prefix (y : ℝ) (hy : 0 ≤ y) (d : AngleL2) :
    angleL2TestPairing (anglePrefixTest y) (memLp_anglePrefixTest y) d =
      angleIntegralPrimitive d y := by
  rw [angleL2TestPairing_apply, angleIntegralPrimitive, intervalIntegral.integral_of_le hy,
    ← integral_indicator measurableSet_Ioc]
  apply congrArg (fun f : ℝ → ℝ => ∫ t, f t ∂angleMeasure)
  funext t
  by_cases ht : t ∈ Ioc (0 : ℝ) y <;> simp [anglePrefixTest, ht]

/-- The three actual L² pairings that evaluate a continuous representative
from its value class and its weak first derivative. -/
def anglePairEvaluation (y : ℝ) : AngleL2 × AngleL2 →L[ℝ] ℝ :=
  Real.pi⁻¹ •
    ((angleL2TestPairing (fun _ => 1) memLp_angleOne).comp
      (ContinuousLinearMap.fst ℝ AngleL2 AngleL2) +
    (angleL2TestPairing (fun x => x) memLp_angleIdentity).comp
      (ContinuousLinearMap.snd ℝ AngleL2 AngleL2)) +
  (angleL2TestPairing (anglePrefixTest y) (memLp_anglePrefixTest y)).comp
    (ContinuousLinearMap.snd ℝ AngleL2 AngleL2)

private theorem anglePairEvaluation_apply_pairings (y : ℝ) (z : AngleL2 × AngleL2) :
    anglePairEvaluation y z =
      Real.pi⁻¹ *
        (angleL2TestPairing (fun _ => 1) memLp_angleOne z.1 +
          angleL2TestPairing (fun x => x) memLp_angleIdentity z.2) +
      angleL2TestPairing (anglePrefixTest y) (memLp_anglePrefixTest y) z.2 := rfl

theorem anglePairEvaluation_apply (y : ℝ) (hy : 0 ≤ y) (f d : AngleL2) :
    anglePairEvaluation y (f, d) =
      Real.pi⁻¹ * ((∫ t, f t ∂angleMeasure) + ∫ t, d t * t ∂angleMeasure) +
        angleIntegralPrimitive d y := by
  rw [anglePairEvaluation_apply_pairings]
  change Real.pi⁻¹ *
    (angleL2TestPairing (fun _ => 1) memLp_angleOne f +
      angleL2TestPairing (fun x => x) memLp_angleIdentity d) +
    angleL2TestPairing (anglePrefixTest y) (memLp_anglePrefixTest y) d = _
  rw [angleL2TestPairing_prefix y hy, angleL2TestPairing_apply, angleL2TestPairing_apply]
  simp only [mul_one]

theorem anglePairEvaluation_of_weakDerivative {f d : AngleL2} {g : ℝ → ℝ}
    (h : HasWeakAngularDerivative f d 1) (hg : Continuous g)
    (hgp : Function.Periodic g Real.pi) (hfg : (⇑f) =ᵐ[angleMeasure] g) (x : ℝ) :
    anglePairEvaluation (toIocMod Real.pi_pos 0 x) (f, d) = g x := by
  obtain ⟨c, hc, hends⟩ := exists_angleIntegralPrimitive_rep_of_hasWeakAngularDerivative h
  let q (t : ℝ) := c + angleIntegralPrimitive d t
  have hq : Continuous q := continuous_const.add (continuous_angleIntegralPrimitive d)
  have hqa : q =ᵐ[angleMeasure] anglePeriodize q := by
    have hmem : ∀ᵐ t ∂angleMeasure, t ∈ Ioc (0 : ℝ) Real.pi :=
      ae_restrict_mem measurableSet_Ioc
    exact hmem.mono fun t ht => (anglePeriodize_eqOn q ht).symm
  have hqeq : g = anglePeriodize q := angle_periodic_eq_of_ae_eq hg
    (continuous_anglePeriodize_of_endpoint_eq hq hends) hgp (anglePeriodize_periodic q)
    (hfg.symm.trans (hc.trans hqa))
  have hmeanP : (∫ t, angleIntegralPrimitive d t ∂angleMeasure) =
      -(∫ t, d t * t ∂angleMeasure) := by
    have hm := integral_angleIntegralPrimitive_mul_deriv d (φ := fun t => t) contDiff_id
    simpa only [deriv_id'', mul_one, integral_angleL2_eq_zero_of_hasWeakAngularDerivative h,
      mul_zero, zero_sub] using hm
  let := angleMeasure_finite_for_evaluation
  have hiP : Integrable (angleIntegralPrimitive d) angleMeasure :=
    (memLp_angleMeasure_of_continuous (continuous_angleIntegralPrimitive d)).integrable (by norm_num)
  have hmeanf : (∫ t, f t ∂angleMeasure) =
      Real.pi * c - ∫ t, d t * t ∂angleMeasure := by
    calc
      (∫ t, f t ∂angleMeasure) = ∫ t, c + angleIntegralPrimitive d t ∂angleMeasure :=
        integral_congr_ae hc
      _ = _ := by
        rw [integral_add (integrable_const _) hiP, hmeanP, integral_const, measureReal_def,
          angleMeasure_univ_for_evaluation, ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul,
          sub_eq_add_neg]
  have hc_eq : c = Real.pi⁻¹ *
      ((∫ t, f t ∂angleMeasure) + ∫ t, d t * t ∂angleMeasure) := by
    rw [← div_eq_inv_mul]
    apply (eq_div_iff Real.pi_ne_zero).2
    rw [hmeanf, sub_add_cancel, mul_comm]
  have hy : 0 ≤ toIocMod Real.pi_pos 0 x := (left_lt_toIocMod Real.pi_pos 0 x).le
  rw [anglePairEvaluation_apply _ hy, hqeq]
  change _ = c + angleIntegralPrimitive d (toIocMod Real.pi_pos 0 x)
  rw [← hc_eq]

private theorem angleL2TestPairing_norm_le (φ : ℝ → ℝ) (hφ : MemLp φ 2 angleMeasure)
    (v : AngleL2) :
    ‖angleL2TestPairing φ hφ v‖ ≤ ‖hφ.toLp φ‖ * ‖v‖ :=
  norm_inner_le_norm (𝕜 := ℝ) (hφ.toLp φ) v

private theorem anglePrefixTest_norm_le (y : ℝ) :
    ‖(memLp_anglePrefixTest y).toLp (anglePrefixTest y)‖ ≤
      ‖memLp_angleOne.toLp (fun _ => 1)‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  apply ENNReal.toReal_mono memLp_angleOne.eLpNorm_ne_top
  apply eLpNorm_mono (memLp_anglePrefixTest y).aestronglyMeasurable
  intro t
  by_cases ht : t ∈ Ioc (0 : ℝ) y <;> simp [anglePrefixTest, ht]

/-- A uniform real evaluation constant from the norms of two fixed tests. -/
def anglePairEvaluationConstant : ℝ :=
  Real.pi⁻¹ * (‖memLp_angleOne.toLp (fun _ => 1)‖ +
    ‖memLp_angleIdentity.toLp (fun x => x)‖) + ‖memLp_angleOne.toLp (fun _ => 1)‖

theorem anglePairEvaluationConstant_nonneg : 0 ≤ anglePairEvaluationConstant := by
  unfold anglePairEvaluationConstant
  exact add_nonneg (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _)

theorem anglePairEvaluation_norm_le (y : ℝ) (z : AngleL2 × AngleL2) :
    ‖anglePairEvaluation y z‖ ≤ anglePairEvaluationConstant * ‖z‖ := by
  let a := ‖memLp_angleOne.toLp (fun _ => 1)‖
  let b := ‖memLp_angleIdentity.toLp (fun x => x)‖
  let A := angleL2TestPairing (fun _ => 1) memLp_angleOne z.1
  let B := angleL2TestPairing (fun x => x) memLp_angleIdentity z.2
  let C := angleL2TestPairing (anglePrefixTest y) (memLp_anglePrefixTest y) z.2
  have hA : ‖A‖ ≤ a * ‖z‖ :=
    (angleL2TestPairing_norm_le _ _ _).trans (mul_le_mul_of_nonneg_left (norm_fst_le z) (norm_nonneg _))
  have hB : ‖B‖ ≤ b * ‖z‖ :=
    (angleL2TestPairing_norm_le _ _ _).trans (mul_le_mul_of_nonneg_left (norm_snd_le z) (norm_nonneg _))
  have hC : ‖C‖ ≤ a * ‖z‖ :=
    (angleL2TestPairing_norm_le _ _ _).trans (mul_le_mul (anglePrefixTest_norm_le y)
      (norm_snd_le z) (norm_nonneg _) (norm_nonneg _))
  rw [anglePairEvaluation_apply_pairings]
  change ‖Real.pi⁻¹ * (A + B) + C‖ ≤ _
  calc
    _ ≤ ‖Real.pi⁻¹ * (A + B)‖ + ‖C‖ := norm_add_le _ _
    _ = Real.pi⁻¹ * ‖A + B‖ + ‖C‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr Real.pi_pos.le)]
    _ ≤ Real.pi⁻¹ * (a * ‖z‖ + b * ‖z‖) + a * ‖z‖ :=
      add_le_add (mul_le_mul_of_nonneg_left ((norm_add_le A B).trans (add_le_add hA hB))
        (inv_nonneg.mpr Real.pi_pos.le)) hC
    _ = _ := by
      change Real.pi⁻¹ * (a * ‖z‖ + b * ‖z‖) + a * ‖z‖ =
        (Real.pi⁻¹ * (a + b) + a) * ‖z‖
      ring

end

end ContinuousFlexibility.Statements
