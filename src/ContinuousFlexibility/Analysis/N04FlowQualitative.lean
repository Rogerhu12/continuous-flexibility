import ContinuousFlexibility.Analysis.N04FlowJetsTarget
import ContinuousFlexibility.Analysis.SmoothPeriodicScalarFlowEndpoint
import ContinuousFlexibility.Analysis.OneHighCircleFlowJacobian

/-!
# Qualitative facts for the actual family in the mixed-flow target

Closed-time ODE data determine the chosen family uniquely. Its joint
continuity and smooth spatial slices therefore follow from the already
constructed Picard family. The angular exponential bounds use only the
angular time majorant. These are prerequisites for, rather than the
all-order quantitative conclusion of, N04FlowJetsTarget.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {F : ℝ × N04FlowPoint → ℝ}
  {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}

theorem n04Flow_time_continuousOn (hΘ : N04FlowEquations F Θ)
    (v : ℝ × ℝ) (θ : ℝ) :
    ContinuousOn (fun t => Θ v t θ) (Icc (0 : ℝ) 1) :=
  fun t ht => (hΘ.2 v θ t ht).continuousWithinAt

theorem n04Flow_time_hasDerivAt (hΘ : N04FlowEquations F Θ)
    (v : ℝ × ℝ) (θ : ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r => Θ v r θ) (F (t, (v, Θ v t θ))) t :=
  (hΘ.2 v θ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem n04Flow_field_contDiff (hF : ContDiff ℝ ∞ F) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun z : PolarPoint => F (z.1, (v, z.2))) :=
  hF.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))

theorem n04Flow_period_add (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) (v : ℝ × ℝ) (θ : ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Θ v t (θ + Real.pi) = Θ v t θ + Real.pi :=
  circleFlow_lift_add (G := fun z : PolarPoint => F (z.1, (v, z.2)))
    (Θ := fun z : PolarPoint => Θ v z.1 z.2)
    (n04Flow_field_contDiff hF v) (fun r => hperiod r v)
    (n04Flow_time_continuousOn hΘ v) (hΘ.1 v)
    (fun r hr η => n04Flow_time_hasDerivAt hΘ v η hr) ht θ

/-- Joint continuity is derived for every chosen actual solution family;
it is not an additional hypothesis about its choice. -/
theorem n04Flow_joint_continuousOn (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) :
    ContinuousOn (fun z : N04FlowPoint × ℝ => Θ z.1.1 z.2 z.1.2)
      (univ ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨Ψ, hi, hd, _, hc⟩ :=
    exists_continuous_periodicScalarFlowFamily
      (F := F) zero_le_one Real.pi_ne_zero hF (fun t _ => hperiod t)
  have heq (v : ℝ × ℝ) (θ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Θ v t θ = Ψ v t θ := by
    have hΨ : ContinuousOn (fun r => Ψ v r θ) (Icc (0 : ℝ) 1) :=
      fun r hr => (hd v θ r hr).continuousWithinAt
    have he := circleTrajectory_difference_eq_mul_exp
      (G := fun z : PolarPoint => F (z.1, (v, z.2)))
      (u := fun r => Θ v r θ) (v := fun r => Ψ v r θ)
      ht.1 (n04Flow_field_contDiff hF v)
      ((n04Flow_time_continuousOn hΘ v θ).mono (Icc_subset_Icc le_rfl ht.2))
      (hΨ.mono (Icc_subset_Icc le_rfl ht.2))
      (fun r hr => n04Flow_time_hasDerivAt hΘ v θ ⟨hr.1, hr.2.trans_le ht.2⟩)
      (fun r hr => (hd v θ r ⟨hr.1.le, hr.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2)))
    rw [hΘ.1 v θ, hi v θ, sub_self, zero_mul] at he
    exact sub_eq_zero.mp he
  exact hc.congr (fun z hz => heq z.1.1 z.1.2 z.2 hz.2)

theorem n04Flow_contDiff_slice (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun q : N04FlowPoint => Θ q.1 t q.2) := by
  have hfield : ContDiff ℝ ∞
      (fun z : N04FlowPoint × (ℝ × ℝ) => F (z.2.1, (z.1.1, z.2.2))) :=
    hF.comp (contDiff_snd.fst.prodMk (contDiff_fst.fst.prodMk contDiff_snd.snd))
  have hcont : ContinuousOn
      (fun z : N04FlowPoint × ℝ => Θ z.1.1 z.2 z.1.2)
      (univ ×ˢ uIcc (0 : ℝ) t) := by
    rw [uIcc_of_le ht.1]
    exact (n04Flow_joint_continuousOn hF hperiod hΘ).mono
      (fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans ht.2⟩)
  apply contDiff_scalarFlow_endpoint
    (F := fun z : N04FlowPoint × (ℝ × ℝ) => F (z.2.1, (z.1.1, z.2.2)))
    (Θ := fun z : N04FlowPoint × ℝ => Θ z.1.1 z.2 z.1.2)
    (v := fun q : N04FlowPoint => q.2)
    hfield contDiff_snd hcont (fun q => hΘ.1 q.1 q.2)
  intro q r hr
  rw [uIcc_of_le ht.1] at hr ⊢
  exact (hΘ.2 q.1 q.2 r ⟨hr.1, hr.2.trans ht.2⟩).mono
    (Icc_subset_Icc le_rfl ht.2)

/-- The actual family has a globally smooth compact time
reparametrization, used to obtain continuous spatial jets at the endpoints. -/
theorem n04Flow_contDiff_timeChange (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) :
    ContDiff ℝ ∞ (scalarFlowTimeChange
      (fun z : N04FlowPoint × ℝ => Θ z.1.1 z.2 z.1.2) 0 1) := by
  have hfield : ContDiff ℝ ∞
      (fun z : N04FlowPoint × (ℝ × ℝ) => F (z.2.1, (z.1.1, z.2.2))) :=
    hF.comp (contDiff_snd.fst.prodMk (contDiff_fst.fst.prodMk contDiff_snd.snd))
  have hcont : ContinuousOn
      (fun z : N04FlowPoint × ℝ => Θ z.1.1 z.2 z.1.2)
      (univ ×ˢ uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using n04Flow_joint_continuousOn hF hperiod hΘ
  apply contDiff_scalarFlow_timeChange
    (F := fun z : N04FlowPoint × (ℝ × ℝ) => F (z.2.1, (z.1.1, z.2.2)))
    (Θ := fun z : N04FlowPoint × ℝ => Θ z.1.1 z.2 z.1.2)
    (v := fun q : N04FlowPoint => q.2)
    hfield contDiff_snd hcont (fun q => hΘ.1 q.1 q.2)
  intro q r hr
  rw [uIcc_of_le zero_le_one] at hr ⊢
  exact hΘ.2 q.1 q.2 r hr

/-- Only the integrated angular derivative enters the genuine
Jacobian exponent; large external-parameter derivatives do not. -/
theorem n04Flow_angular_bounds (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) {Λ : ℝ} (hΛ : N04FlowAngularControl F Λ)
    {v : ℝ × ℝ} (hv : v ∈ n04FlowParameterBox)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    Real.exp (-Λ) ≤ deriv (fun η : ℝ => Θ v t η) θ ∧
      deriv (fun η : ℝ => Θ v t η) θ ≤ Real.exp Λ := by
  obtain ⟨α, hα, _, hb, hI⟩ := hΛ
  have hG := n04Flow_field_contDiff hF v
  have hbound (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (η : ℝ) :
      |angularPartial (fun z : PolarPoint => F (z.1, (v, z.2))) (r, η)| ≤ α r := by
    rw [← deriv_cylinder_angular_slice (hG.differentiable (by simp)) r η]
    exact hb r hr v hv η
  have hj := circleFlow_deriv_bounds
    (G := fun z : PolarPoint => F (z.1, (v, z.2)))
    (Θ := fun z : PolarPoint => Θ v z.1 z.2)
    hG Real.pi_pos (fun r => hperiod r v)
    (n04Flow_time_continuousOn hΘ v) (hΘ.1 v)
    (fun r hr η => n04Flow_time_hasDerivAt hΘ v η hr) hα hbound ht θ
  exact ⟨(Real.exp_le_exp.mpr (neg_le_neg hI)).trans hj.1,
    hj.2.trans (Real.exp_le_exp.mpr hI)⟩

end ContinuousFlexibility.Analysis
