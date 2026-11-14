import ContinuousFlexibility.Analysis.N04FlowQualitative
import ContinuousFlexibility.Analysis.ParametricSpatialClosedJets

/-!
# Integral equations for every actual mixed spatial flow jet

The original closed-time scalar ODE gives the value integral equation.
The derived smooth time reparametrization gives true endpoint continuity
of every spatial jet of the composed field. Differentiating the actual
value integral by the compact-integral theorem therefore gives the
integral equation at every order, without a supplied flow-jet tower.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {F : ℝ × N04FlowPoint → ℝ}
  {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}

def n04FlowComposedField (F : ℝ × N04FlowPoint → ℝ)
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (z : N04FlowPoint × ℝ) : ℝ :=
  F (z.2, (z.1.1, Θ z.1.1 z.2 z.1.2))

theorem n04Flow_compactTime_surjOn :
    SurjOn (compactScalarFlowTime 0 1) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
  intro t ht
  apply intermediate_value_Icc zero_le_one
    (contDiff_compactScalarFlowTime 0 1).continuous.continuousOn
  simpa only [compactScalarFlowTime_zero, compactScalarFlowTime_one] using ht

theorem n04Flow_compactTime_mem (s : ℝ) :
    compactScalarFlowTime 0 1 s ∈ Icc (0 : ℝ) 1 := by
  simpa only [uIcc_of_le zero_le_one] using compactScalarFlowTime_mem 0 1 s

theorem n04FlowComposedField_contDiff_timeReparam
    (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) :
    ContDiff ℝ ∞ (fun z : N04FlowPoint × ℝ =>
      n04FlowComposedField F Θ (z.1, compactScalarFlowTime 0 1 z.2)) := by
  have hΨ := n04Flow_contDiff_timeChange hF hperiod hΘ
  exact hF.comp
    (((contDiff_compactScalarFlowTime 0 1).comp contDiff_snd).prodMk
      (contDiff_fst.fst.prodMk hΨ))

theorem n04Flow_spatialJet_continuousOn
    (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) (n : ℕ) :
    ContinuousOn (parametricSpatialJet
      (fun z : N04FlowPoint × ℝ => Θ z.1.1 z.2 z.1.2) n)
      (univ ×ˢ Icc (0 : ℝ) 1) :=
  continuousOn_parametricSpatialJet_of_timeReparam
    (contDiff_compactScalarFlowTime 0 1).continuous
    (fun s _ => n04Flow_compactTime_mem s) n04Flow_compactTime_surjOn
    (n04Flow_contDiff_timeChange hF hperiod hΘ) n

theorem n04FlowComposedField_spatialJet_continuousOn
    (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) (n : ℕ) :
    ContinuousOn (parametricSpatialJet (n04FlowComposedField F Θ) n)
      (univ ×ˢ Icc (0 : ℝ) 1) :=
  continuousOn_parametricSpatialJet_of_timeReparam
    (contDiff_compactScalarFlowTime 0 1).continuous
    (fun s _ => n04Flow_compactTime_mem s) n04Flow_compactTime_surjOn
    (n04FlowComposedField_contDiff_timeReparam hF hperiod hΘ) n

theorem n04Flow_integral_eq (hF : ContDiff ℝ ∞ F)
    (hΘ : N04FlowEquations F Θ) (q : N04FlowPoint)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Θ q.1 t q.2 = q.2 + ∫ r in (0 : ℝ)..t, n04FlowComposedField F Θ (q, r) := by
  have hu := n04Flow_time_continuousOn hΘ q.1 q.2
  have hconstant : ContinuousOn (fun _r : ℝ => q.1) (Icc (0 : ℝ) 1) :=
    continuousOn_const
  have hpath : ContinuousOn (fun r : ℝ => (r, (q.1, Θ q.1 r q.2)))
      (Icc (0 : ℝ) 1) :=
    continuousOn_id.prodMk (hconstant.prodMk hu)
  have hc : ContinuousOn
      (fun r : ℝ => n04FlowComposedField F Θ (q, r)) (Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun r : ℝ => F (r, (q.1, Θ q.1 r q.2)))
      (Icc (0 : ℝ) 1)
    exact hF.continuous.comp_continuousOn hpath
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hu.mono (Icc_subset_Icc le_rfl ht.2))
    (fun r hr => n04Flow_time_hasDerivAt hΘ q.1 q.2 ⟨hr.1, hr.2.trans_le ht.2⟩)
    ((hc.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
  rw [hΘ.1 q.1 q.2] at hFTC
  exact (eq_add_of_sub_eq hFTC.symm).trans (add_comm _ _)

/-- The true mixed spatial jets satisfy the integral equation obtained
by differentiating the original scalar time equation at that same order. -/
theorem n04Flow_spatialJet_integral_eq
    (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) (n : ℕ) (q : N04FlowPoint)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    iteratedFDeriv ℝ n (fun y : N04FlowPoint => Θ y.1 t y.2) q =
      iteratedFDeriv ℝ n (fun y : N04FlowPoint => y.2) q +
        ∫ r in (0 : ℝ)..t, parametricSpatialJet (n04FlowComposedField F Θ) n (q, r) := by
  have hI := parametricIntervalIntegral_closed_contDiff_and_iteratedFDeriv
    (contDiff_compactScalarFlowTime 0 1).continuous
    (fun s _ => n04Flow_compactTime_mem s) n04Flow_compactTime_surjOn
    (n04FlowComposedField_contDiff_timeReparam hF hperiod hΘ) ht
  have hfun : (fun y : N04FlowPoint => Θ y.1 t y.2) =
      (fun y : N04FlowPoint => y.2) +
        (fun y : N04FlowPoint => ∫ r in (0 : ℝ)..t, n04FlowComposedField F Θ (y, r)) :=
    funext (fun y => n04Flow_integral_eq hF hΘ y ht)
  rw [hfun, iteratedFDeriv_add_apply
    (contDiffAt_snd.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    (hI.1.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)), hI.2 n q]

theorem n04Flow_displacement_abs_le (hF : ContDiff ℝ ∞ F)
    (hΘ : N04FlowEquations F Θ) (v : ℝ × ℝ) (θ : ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ r ∈ Icc (0 : ℝ) 1, ∀ η : ℝ, |F (r, (v, η))| ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |Θ v t θ - θ| ≤ M := by
  have he : Θ v t θ - θ =
      ∫ r in (0 : ℝ)..t, n04FlowComposedField F Θ ((v, θ), r) := by
    rw [n04Flow_integral_eq hF hΘ (v, θ) ht]
    exact add_sub_cancel_left _ _
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun r => n04FlowComposedField F Θ ((v, θ), r))
    (a := (0 : ℝ)) (b := t) (C := M) (fun r hr => by
      have hr' : r ∈ Icc (0 : ℝ) t := by
        simpa only [uIcc_of_le ht.1] using uIoc_subset_uIcc hr
      simpa only [Real.norm_eq_abs, n04FlowComposedField] using
        hbound r ⟨hr'.1, hr'.2.trans ht.2⟩ (Θ v r θ))
  have hb' : |∫ r in (0 : ℝ)..t, n04FlowComposedField F Θ ((v, θ), r)| ≤ M * t := by
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] using hb
  rw [he]
  exact hb'.trans (mul_le_of_le_one_right hM ht.2)

end ContinuousFlexibility.Analysis
