module

public import ContinuousFlexibility.Analysis.N04FlowQualitative

/-!
# Actual inverse flows and preservation of the material inputs

Reversing time changes the field to `-F(1-t,q)`. Its spatial jets
and integrated angular bound are unchanged. Uniqueness of the actual
ODE identifies the reversed endpoint map as both a left and a right
inverse of the original endpoint map. Thus the fixed-loss flow theorem
applies to actual inverse maps with the original material constants.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

def n04FlowReverseField (F : ℝ × N04FlowPoint → ℝ) : ℝ × N04FlowPoint → ℝ :=
  fun z => -F (1 - z.1, z.2)

private theorem n04ReverseTime_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩

theorem n04FlowReverseField_reverse (F : ℝ × N04FlowPoint → ℝ) :
    n04FlowReverseField (n04FlowReverseField F) = F := by
  funext z
  simp only [n04FlowReverseField, sub_sub_cancel, neg_neg]

theorem n04FlowReverseField_contDiff {F : ℝ × N04FlowPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (n04FlowReverseField F) :=
  (hF.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)).neg

theorem n04FlowReverseField_periodic {F : ℝ × N04FlowPoint → ℝ}
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) :
    ∀ t v, Function.Periodic
      (fun θ : ℝ => n04FlowReverseField F (t, (v, θ))) Real.pi := by
  intro t v θ
  change -F (1 - t, (v, θ + Real.pi)) = -F (1 - t, (v, θ))
  have hp : F (1 - t, (v, θ + Real.pi)) = F (1 - t, (v, θ)) :=
    hperiod (1 - t) v θ
  rw [hp]

theorem n04FlowReverseField_rawJetBounds
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {inputLoss : ℕ} {A : ℕ → ℝ}
    {z : E} {W : ℝ} {F : ℝ × N04FlowPoint → ℝ}
    (hraw : N04FlowRawJetBounds p inputLoss A z W F) :
    N04FlowRawJetBounds p inputLoss A z W (n04FlowReverseField F) := by
  intro n t ht q hq
  have he : (fun y : N04FlowPoint => n04FlowReverseField F (t, y)) =
      -(fun y : N04FlowPoint => F (1 - t, y)) := rfl
  rw [he, iteratedFDeriv_neg_apply, norm_neg]
  exact hraw n (1 - t) (n04ReverseTime_mem ht) q hq

theorem n04FlowReverseField_angularControl
    {F : ℝ × N04FlowPoint → ℝ} {Λ : ℝ}
    (hcontrol : N04FlowAngularControl F Λ) :
    N04FlowAngularControl (n04FlowReverseField F) Λ := by
  obtain ⟨α, hα, hα0, hderiv, hI⟩ := hcontrol
  refine ⟨fun t => α (1 - t),
    hα.comp (continuous_const.sub continuous_id).continuousOn
      (fun _ ht => n04ReverseTime_mem ht),
    fun t ht => hα0 (1 - t) (n04ReverseTime_mem ht), ?_, ?_⟩
  · intro t ht v hv θ
    change |deriv (fun η : ℝ => -F (1 - t, (v, η))) θ| ≤ α (1 - t)
    rw [deriv.fun_neg, abs_neg]
    exact hderiv (1 - t) (n04ReverseTime_mem ht) v hv θ
  · calc
      (∫ t in (0 : ℝ)..1, α (1 - t)) = ∫ t in (0 : ℝ)..1, α t := by
        simpa only [sub_self, sub_zero] using
          (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) α 1)
      _ ≤ Λ := hI

/-- The reversed trajectory is compared with the genuine forward
solution starting from its terminal value. No regularity of a chosen
inverse map is postulated. -/
theorem n04Flow_reverse_endpoint_rightInverse
    {F : ℝ × N04FlowPoint → ℝ}
    {Θ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hΘ : N04FlowEquations F Θ)
    (hΨ : N04FlowEquations (n04FlowReverseField F) Ψ)
    (v : ℝ × ℝ) (θ : ℝ) : Θ v 1 (Ψ v 1 θ) = θ := by
  have hu : ContinuousOn (fun t => Ψ v (1 - t) θ) (Icc (0 : ℝ) 1) :=
    (n04Flow_time_continuousOn hΨ v θ).comp
      (continuous_const.sub continuous_id).continuousOn
      (fun _ ht => n04ReverseTime_mem ht)
  have hdu (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun s => Ψ v (1 - s) θ)
        (F (t, (v, Ψ v (1 - t) θ))) t := by
    have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hd := (n04Flow_time_hasDerivAt hΨ v θ ht').comp t
      ((hasDerivAt_id t).const_sub 1)
    simpa only [Function.comp_def, id_eq, n04FlowReverseField,
      sub_sub_cancel, mul_neg_one, neg_neg] using hd
  have he := circleTrajectory_difference_eq_mul_exp
    (G := fun q : PolarPoint => F (q.1, (v, q.2)))
    (u := fun t => Ψ v (1 - t) θ) (v := fun t => Θ v t (Ψ v 1 θ))
    zero_le_one (n04Flow_field_contDiff hF v) hu
    (n04Flow_time_continuousOn hΘ v (Ψ v 1 θ)) hdu
    (fun t ht => n04Flow_time_hasDerivAt hΘ v (Ψ v 1 θ) ht)
  have he' : θ - Θ v 1 (Ψ v 1 θ) = 0 := by
    simpa only [sub_self, sub_zero, hΨ.1 v θ, hΘ.1 v (Ψ v 1 θ), zero_mul] using he
  exact (sub_eq_zero.mp he').symm

/-- A smooth periodic field has an actual reversed flow whose endpoint
is the two-sided inverse of every chosen forward solution family. -/
theorem exists_n04Flow_actual_inverse
    {F : ℝ × N04FlowPoint → ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) :
    ∃ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (n04FlowReverseField F) Ψ ∧
      (∀ v θ, Θ v 1 (Ψ v 1 θ) = θ ∧ Ψ v 1 (Θ v 1 θ) = θ) ∧
      ContDiff ℝ ∞ (fun q : N04FlowPoint => Ψ q.1 1 q.2) := by
  obtain ⟨Ψ, hi, hd, _, _, hs, _⟩ :=
    exists_smooth_periodicScalarFlowFamily (F := n04FlowReverseField F)
      zero_le_one Real.pi_ne_zero (n04FlowReverseField_contDiff hF)
      (fun t _ v => n04FlowReverseField_periodic hperiod t v)
  have hΨ : N04FlowEquations (n04FlowReverseField F) Ψ := ⟨hi, hd⟩
  have hΘ' : N04FlowEquations
      (n04FlowReverseField (n04FlowReverseField F)) Θ := by
    rw [n04FlowReverseField_reverse]
    exact hΘ
  refine ⟨Ψ, hΨ, fun v θ => ⟨?_, ?_⟩, hs⟩
  · exact n04Flow_reverse_endpoint_rightInverse hF hΘ hΨ v θ
  · exact n04Flow_reverse_endpoint_rightInverse
      (n04FlowReverseField_contDiff hF) hΨ hΘ' v θ

/-- One choice of low order, loss and material constants controls both
the forward flow and its actual inverse endpoint flow. -/
theorem n04FlowJetsTarget_with_actual_inverse (hFlow : N04FlowJetsTarget)
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∀ Λ : ℝ, 0 ≤ Λ → ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ F : ℝ × N04FlowPoint → ℝ, ContDiff ℝ ∞ F →
        (∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) →
        N04FlowRawJetBounds p inputLoss A z W F → N04FlowAngularControl F Λ →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ, N04FlowEquations F Θ →
        N04FlowJetBounds p loss B z W Λ Θ ∧
        ∃ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
          N04FlowEquations (n04FlowReverseField F) Ψ ∧
          (∀ v θ, Θ v 1 (Ψ v 1 θ) = θ ∧ Ψ v 1 (Θ v 1 θ) = θ) ∧
          N04FlowJetBounds p loss B z W Λ Ψ := by
  obtain ⟨base, loss, hbase⟩ := hFlow E p hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA Λ hΛ
  obtain ⟨B, hB, hbound⟩ := hbase A hA Λ hΛ
  refine ⟨B, hB, ?_⟩
  intro z hz W hW F hF hperiod hraw hcontrol Θ hΘ
  obtain ⟨Ψ, hΨ, hinverse, _⟩ := exists_n04Flow_actual_inverse hF hperiod hΘ
  refine ⟨hbound z hz W hW F hF hperiod hraw hcontrol Θ hΘ,
    Ψ, hΨ, hinverse, ?_⟩
  exact hbound z hz W hW (n04FlowReverseField F)
    (n04FlowReverseField_contDiff hF) (n04FlowReverseField_periodic hperiod)
    (n04FlowReverseField_rawJetBounds hraw)
    (n04FlowReverseField_angularControl hcontrol) Ψ hΨ

end ContinuousFlexibility.Analysis
