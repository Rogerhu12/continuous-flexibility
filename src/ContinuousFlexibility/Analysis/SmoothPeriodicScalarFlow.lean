import ContinuousFlexibility.Analysis.PeriodicFlowParameterContinuity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Actual parameterized flows of smooth periodic scalar fields

For every external parameter, periodicity supplies the global angular
bounds needed by Picard--Lindelof on a prescribed compact time interval.
The chosen solutions are then jointly continuous in the parameter,
initial angle, and time.  This last assertion follows locally from the
actual field derivative on compact parameter balls; no continuity of
the choice of solutions is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The actual derivative in the parameter and angle is jointly smooth
when the time-dependent field is smooth. -/
private theorem contDiff_scalarField_partialFDeriv
    {F : ℝ × (P × ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞
      (fun q : ℝ × (P × ℝ) =>
        fderiv ℝ (fun y : P × ℝ => F (q.1, y)) q.2) := by
  have haux : ContDiff ℝ ∞
      (Function.uncurry
        (fun q : ℝ × (P × ℝ) => fun y : P × ℝ => F (q.1, y))) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact haux.fderiv contDiff_snd (by simp)

/-- A globally smooth angular-periodic field admits a genuine family of
solutions on the whole closed time interval.  The family is jointly
continuous for every parameter and every initial angle, and is
equivariant under one angular period.  The field coordinates are
(time, (parameter, current angle)); the family arguments are parameter,
time, and initial angle. -/
theorem exists_continuous_periodicScalarFlowFamily
    [FiniteDimensional ℝ P]
    {F : ℝ × (P × ℝ) → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hT : T ≠ 0)
    (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t ∈ Icc a b, ∀ p : P,
      Function.Periodic (fun θ => F (t, (p, θ))) T) :
    ∃ Θ : P → ℝ → ℝ → ℝ,
      (∀ p θ, Θ p a θ = θ) ∧
      (∀ p θ t, t ∈ Icc a b →
        HasDerivWithinAt (fun r => Θ p r θ)
          (F (t, (p, Θ p t θ))) (Icc a b) t) ∧
      (∀ p θ t, t ∈ Icc a b → Θ p t (θ + T) = Θ p t θ + T) ∧
      ContinuousOn (fun x : (P × ℝ) × ℝ => Θ x.1.1 x.2 x.1.2)
        (univ ×ˢ Icc a b) := by
  let DF : ℝ × (P × ℝ) → (P × ℝ) →L[ℝ] ℝ :=
    fun q => fderiv ℝ (fun y : P × ℝ => F (q.1, y)) q.2
  have hDF : Continuous DF :=
    (contDiff_scalarField_partialFDeriv hF).continuous
  have hDiff (t : ℝ) (x : P × ℝ) :
      DifferentiableAt ℝ (fun y : P × ℝ => F (t, y)) x := by
    have hs : ContDiff ℝ ∞ (fun y : P × ℝ => (t, y)) :=
      contDiff_const.prodMk contDiff_id
    exact ((hF.comp hs).differentiable (by simp)) x
  have hangle (p : P) (t θ : ℝ) :
      HasDerivAt (fun φ => F (t, (p, φ)))
        (DF (t, (p, θ)) ((0 : P), 1)) θ := by
    have hd := (hDiff t (p, θ)).hasFDerivAt.comp_hasDerivAt θ
      ((hasDerivAt_const θ p).prodMk (hasDerivAt_id θ))
    have he :
        (fun y : P × ℝ => F (t, y)) ∘ (fun φ : ℝ => (p, φ)) =
          (fun φ : ℝ => F (t, (p, φ))) := by
      funext φ
      exact Function.comp_apply
    rw [he] at hd
    exact hd
  have hex (p : P) :
      ∃ Ψ : ℝ → ℝ → ℝ,
        (∀ θ, Ψ θ a = θ) ∧
        (∀ θ t, t ∈ Icc a b →
          HasDerivWithinAt (Ψ θ) (F (t, (p, Ψ θ t))) (Icc a b) t) ∧
        (∀ θ t, t ∈ Icc a b → Ψ (θ + T) t = Ψ θ t + T) := by
    apply exists_periodicScalarFlow_on_Icc
      (F := fun x : ℝ × ℝ => F (x.1, (p, x.2)))
      (D := fun x : ℝ × ℝ => DF (x.1, (p, x.2)) ((0 : P), 1))
      hab hT
    · exact (hF.continuous.comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).continuousOn
    · exact ((hDF.comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).clm_apply
          continuous_const).continuousOn
    · intro t ht
      exact hperiod t ht p
    · intro t ht θ
      exact congrArg (fun L : (P × ℝ) →L[ℝ] ℝ => L ((0 : P), 1))
        ((fderiv_periodic_snd (hperiod t ht) p) θ)
    · intro t _ θ
      exact hangle p t θ
  choose Ψ hΨ using hex
  let Θ : P → ℝ → ℝ → ℝ := fun p t θ => Ψ p θ t
  refine ⟨Θ, fun p => (hΨ p).1,
    fun p => (hΨ p).2.1, fun p => (hΨ p).2.2, ?_⟩
  have hlocal (p : P) :
      ContinuousOn (fun x : (P × ℝ) × ℝ => Θ x.1.1 x.2 x.1.2)
        ((Metric.closedBall p 1 ×ˢ univ) ×ˢ Icc a b) := by
    apply continuousOn_periodicScalarFlow_parameters
      (F := fun t x => F (t, x))
      (isCompact_closedBall p 1) (convex_closedBall p 1) hT
    · intro t _ x _
      exact hDiff t x
    · exact (hDF.comp (continuous_fst.fst.prodMk
        (continuous_fst.snd.prodMk continuous_snd))).continuousOn
    · exact hperiod
    · intro q _ θ
      exact (hΨ q).1 θ
    · intro q _ θ t ht
      exact (hΨ q).2.1 θ t ht
  intro q hq
  have hc := hlocal q.1.1 q
    ⟨⟨Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1), mem_univ _⟩, hq.2⟩
  apply hc.mono_of_mem_nhdsWithin
  have hproj : Continuous (fun z : (P × ℝ) × ℝ => z.1.1) :=
    continuous_fst.fst
  have hn : ∀ᶠ z : (P × ℝ) × ℝ in 𝓝 q,
      z.1.1 ∈ Metric.closedBall q.1.1 1 :=
    hproj.continuousAt.eventually
      (Metric.closedBall_mem_nhds q.1.1 (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hn.filter_mono nhdsWithin_le_nhds]
    with z hz hzp
  exact ⟨⟨hzp, mem_univ _⟩, hz.2⟩

end ContinuousFlexibility.Analysis
