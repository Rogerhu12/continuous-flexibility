import ContinuousFlexibility.Analysis.AngularRegularityIntegral
import ContinuousFlexibility.Analysis.CircleEnergyPointwiseBounds
import ContinuousFlexibility.Analysis.ReturnCorrectionDisplacementRegularity

/-!
# Parameter integrals of actual weighted circle fields

All angular derivatives are differentiated under the scalar parameter
integral.  A bound by the complete energy of the same input component
survives integration on the unit interval, so the complete sum over
circles remains finite.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem contDiff_unitParameterIntegral
    {F : ℝ → ℝ → ℝ} (hF : ∀ n, AngularRegular n F) :
    ContDiff ℝ ∞ (fun θ => ∫ a in (0 : ℝ)..1, F a θ) :=
  contDiff_of_angularRegular_all (fun n => (hF n).radial_primitive 0) 1

theorem iteratedDeriv_unitParameterIntegral
    {F : ℝ → ℝ → ℝ} (hF : ∀ n, AngularRegular n F) (n : ℕ) :
    iteratedDeriv n (fun θ => ∫ a in (0 : ℝ)..1, F a θ) =
      fun θ => ∫ a in (0 : ℝ)..1, iteratedDeriv n (F a) θ := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    have hcont : Continuous
        (fun p : PolarPoint => iteratedDeriv n (F p.1) p.2) :=
      (hF n).iteratedDeriv_continuous
    have hdiff (a : ℝ) : Differentiable ℝ (iteratedDeriv n (F a)) :=
      (contDiff_of_angularRegular_all hF a).differentiable_iteratedDeriv n
        (by exact_mod_cast (ENat.natCast_lt_top n))
    have hnext : Continuous
        (fun p : PolarPoint => deriv (iteratedDeriv n (F p.1)) p.2) := by
      simpa only [iteratedDeriv_succ] using (hF (n + 1)).iteratedDeriv_continuous
    simpa only [iteratedDeriv_succ] using
      (angular_parameter_integral_hasDerivAt hcont hdiff hnext 0 1 θ).deriv

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal

def circleParameterIntegralField (F : ℝ → ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun m θ => ∫ a in (0 : ℝ)..1, F a m θ

theorem circleParameterIntegralField_apply (F : ℝ → ℕ → ℝ → ℝ)
    (m : ℕ) (θ : ℝ) :
    circleParameterIntegralField F m θ = ∫ a in (0 : ℝ)..1, F a m θ := rfl

theorem circleMember_unitParameterIntegral
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ} {F : ℝ → ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u)
    (hF : ∀ m n, AngularRegular n (fun a θ => F a m θ))
    (hp : ∀ a ∈ Icc (0 : ℝ) 1, ∀ m, Function.Periodic (F a m) Real.pi)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hbound : ∀ s, ∃ t : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ m b k, b + k ≤ s → ∀ a ∈ Icc (0 : ℝ) 1, ∀ θ,
        (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
          |iteratedDeriv b (F a m) θ| ≤
        K * Real.sqrt (circleComponentEnergy T γ t u m).toReal) :
    CircleMember T γ (circleParameterIntegralField F) := by
  have hreg (m : ℕ) : ContDiff ℝ ∞ (circleParameterIntegralField F m) :=
    contDiff_unitParameterIntegral (hF m)
  apply circleMember_of_component_pointwise hu
  · intro m
    refine ⟨hreg m, ?_⟩
    intro θ
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' : a ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ha
    exact hp a ha' m θ
  · exact hM
  · exact hH
  · intro s
    obtain ⟨t, K, hK, hb⟩ := hbound s
    refine ⟨t, K, hK, fun m b k horder θ => ?_⟩
    let w := T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)
    have hw : 0 ≤ w := mul_nonneg (pow_nonneg (hM m) k) (Real.rpow_nonneg (hH m) _)
    have hjet : iteratedDeriv b (circleParameterIntegralField F m) θ =
        ∫ a in (0 : ℝ)..1, iteratedDeriv b (F a m) θ :=
      congrFun (iteratedDeriv_unitParameterIntegral (hF m) b) θ
    rw [hjet]
    have hnorm : ‖∫ a in (0 : ℝ)..1, w * iteratedDeriv b (F a m) θ‖ ≤
        K * Real.sqrt (circleComponentEnergy T γ t u m).toReal := by
      have hb' : ∀ a ∈ uIoc (0 : ℝ) 1,
          ‖w * iteratedDeriv b (F a m) θ‖ ≤
            K * Real.sqrt (circleComponentEnergy T γ t u m).toReal := by
        intro a ha
        have ha' : a ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
            (uIoc_subset_uIcc ha)
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw] using hb m b k horder a ha' θ
      simpa only [sub_zero, abs_one, mul_one] using
        intervalIntegral.norm_integral_le_of_norm_le_const hb'
    simpa only [intervalIntegral.integral_const_mul, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg hw] using hnorm

end ContinuousFlexibility.Statements
