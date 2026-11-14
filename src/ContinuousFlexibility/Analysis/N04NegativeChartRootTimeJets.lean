module

public import ContinuousFlexibility.Analysis.N04NegativeChartRootFieldBounds
public import ContinuousFlexibility.Analysis.N04NegativeChartVariationForcing
public import ContinuousFlexibility.Analysis.N04FlowJetEquations

/-!
# State jets of the same reversed root flow

Time reversal negates the original state jet and replaces time by `1-t`.
The smooth compact time change multiplies every state and spatial jet by
its one fixed time derivative. Its numerical cost is chosen before all
orders, coefficients, and actual flow representatives. The endpoint jets
are those of the supplied inverse flow itself.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- Reversal acts on the actual parameter derivative, including order zero. -/
theorem negativeChartRootPlotReverseField_stateJet
    (d c : P × PolarPoint → ℝ) (δ : ℝ) (k : ℕ) (v : Fin k → P)
    (t : ℝ) (q : N04FlowPoint) :
    flowParameterField (negativeChartRootPlotReverseField d c δ) k (0, q.1)
      (fun i => (v i, (0 : PolarPoint))) (t, q.2) =
      -flowParameterField (negativeChartRootPlotField d c δ) k (0, q.1)
        (fun i => (v i, (0 : PolarPoint))) (1 - t, q.2) := by
  have he := iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := k)
    (f := fun z : P × PolarPoint => negativeChartRootPlotField d c δ (z, (1 - t, q.2)))
    (x := ((0 : P), q.1))
  exact congrArg (fun B : (P × PolarPoint) [×k]→L[ℝ] ℝ =>
    B (fun i => (v i, (0 : PolarPoint)))) he

theorem negativeChartRootPlotReverseField_contDiff
    {d c : P × PolarPoint → ℝ} (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (δ : ℝ) : ContDiff ℝ ∞ (negativeChartRootPlotReverseField d c δ) :=
  ((negativeChartRootPlotField_contDiff hd hc δ).comp
    (contDiff_fst.prodMk
      ((contDiff_const.sub contDiff_snd.fst).prodMk contDiff_snd.snd))).neg

/-- Reversal has exactly unit cost on every spatial jet of a state slice. -/
theorem negativeChartRootPlotReverseField_spatialJet_norm
    (d c : P × PolarPoint → ℝ) (δ : ℝ) (k j : ℕ) (v : Fin k → P)
    (t : ℝ) (q : N04FlowPoint) :
    ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
      flowParameterField (negativeChartRootPlotReverseField d c δ) k (0, y.1)
        (fun i => (v i, (0 : PolarPoint))) (t, y.2)) q‖ =
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        flowParameterField (negativeChartRootPlotField d c δ) k (0, y.1)
          (fun i => (v i, (0 : PolarPoint))) (1 - t, y.2)) q‖ := by
  have he : (fun y : N04FlowPoint =>
      flowParameterField (negativeChartRootPlotReverseField d c δ) k (0, y.1)
        (fun i => (v i, (0 : PolarPoint))) (t, y.2)) =
      -(fun y : N04FlowPoint =>
        flowParameterField (negativeChartRootPlotField d c δ) k (0, y.1)
          (fun i => (v i, (0 : PolarPoint))) (1 - t, y.2)) :=
    funext (negativeChartRootPlotReverseField_stateJet d c δ k v t)
  rw [he, iteratedFDeriv_neg_apply, norm_neg]

/-- A fixed time is constant in all state directions. No time derivative
of a state slot enters the actual time-changed field. -/
theorem n04NegativeChart_scalarTimeChange_parameterJet
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E × PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F)
    (k : ℕ) (x : E) (v : Fin k → E) (t θ : ℝ) :
    flowParameterField (scalarFieldTimeChange F 0 1) k x v (t, θ) =
      deriv (compactScalarFlowTime 0 1) t *
        flowParameterField F k x v (compactScalarFlowTime 0 1 t, θ) := by
  have hs : ContDiff ℝ ∞ (fun y : E => F (y, (compactScalarFlowTime 0 1 t, θ))) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have he := iteratedFDeriv_const_smul_apply' (a := deriv (compactScalarFlowTime 0 1) t)
    (x := x) (hs.contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
  exact congrArg (fun B : E [×k]→L[ℝ] ℝ => B v) he

/-- The same fixed multiplier survives differentiation in every root
coordinate and the initial angle. -/
theorem n04NegativeChart_scalarTimeChange_spatialJet_norm
    {F : (P × PolarPoint) × PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F)
    (k j : ℕ) (v : Fin k → P) (t : ℝ) (q : N04FlowPoint) :
    ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
      flowParameterField (scalarFieldTimeChange F 0 1) k (0, y.1)
        (fun i => (v i, (0 : PolarPoint))) (t, y.2)) q‖ =
      |deriv (compactScalarFlowTime 0 1) t| *
        ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
          flowParameterField F k (0, y.1) (fun i => (v i, (0 : PolarPoint)))
            (compactScalarFlowTime 0 1 t, y.2)) q‖ := by
  let u : Fin k → P × PolarPoint := fun i => (v i, (0 : PolarPoint))
  have hs : ContDiff ℝ ∞ (fun y : N04FlowPoint =>
      flowParameterField F k (0, y.1) u (compactScalarFlowTime 0 1 t, y.2)) :=
    (n04NegativeChart_flowParameterField_joint_contDiff hF k u).comp
      ((contDiff_const.prodMk contDiff_fst).prodMk (contDiff_const.prodMk contDiff_snd))
  have he : (fun y : N04FlowPoint =>
      flowParameterField (scalarFieldTimeChange F 0 1) k (0, y.1) u (t, y.2)) =
      fun y : N04FlowPoint => deriv (compactScalarFlowTime 0 1) t •
        flowParameterField F k (0, y.1) u (compactScalarFlowTime 0 1 t, y.2) := by
    funext y
    exact n04NegativeChart_scalarTimeChange_parameterJet hF k (0, y.1) u t y.2
  change ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
    flowParameterField (scalarFieldTimeChange F 0 1) k (0, y.1) u (t, y.2)) q‖ = _
  rw [he, iteratedFDeriv_const_smul_apply' (a := deriv (compactScalarFlowTime 0 1) t)
    (hs.contDiffAt.of_le (by simp : (j : ℕ∞ω) ≤ ∞)), norm_smul, Real.norm_eq_abs]

/-- One time-change cost works for every state order, spatial order,
component, material factor and supplied pair of actual coefficients. -/
theorem n04NegativeChart_reverseTimeChange_spatialJet_le :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ d c : P × PolarPoint → ℝ,
      ContDiff ℝ ∞ d → ContDiff ℝ ∞ c → ∀ δ : ℝ,
      ∀ k j : ℕ, ∀ v : Fin k → P, ∀ q : N04FlowPoint, ∀ M : ℝ,
      (∀ r ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
          flowParameterField (negativeChartRootPlotField d c δ) k (0, y.1)
            (fun i => (v i, (0 : PolarPoint))) (r, y.2)) q‖ ≤ M) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
          flowParameterField
            (scalarFieldTimeChange (negativeChartRootPlotReverseField d c δ) 0 1)
            k (0, y.1) (fun i => (v i, (0 : PolarPoint))) (t, y.2)) q‖ ≤ T * M := by
  have hτ : Continuous (deriv (compactScalarFlowTime 0 1)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_compactScalarFlowTime 0 1)).2.continuous
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hτ.continuousOn
  let T : ℝ := max 1 B
  have hT : 1 ≤ T := le_max_left _ _
  have htau (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |deriv (compactScalarFlowTime 0 1) t| ≤ T :=
    (show |deriv (compactScalarFlowTime 0 1) t| ≤ B from
      by simpa only [Real.norm_eq_abs] using hB t ht).trans (le_max_right _ _)
  refine ⟨T, hT, fun d c hd hc δ k j v q M hraw t ht => ?_⟩
  have hτmem := n04Flow_compactTime_mem t
  have hreverse : 1 - compactScalarFlowTime 0 1 t ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith only [hτmem.2], by linarith only [hτmem.1]⟩
  rw [n04NegativeChart_scalarTimeChange_spatialJet_norm
    (negativeChartRootPlotReverseField_contDiff hd hc δ),
    negativeChartRootPlotReverseField_spatialJet_norm]
  exact mul_le_mul (htau t ht)
    (hraw (1 - compactScalarFlowTime 0 1 t) hreverse)
    (norm_nonneg _) (zero_le_one.trans hT)

/-- Endpoint differentiation retains the supplied inverse. This equality
does not choose another flow or assume its extension is smooth in time. -/
theorem NegativeChartRootFlowData.inverse_endpoint_spatialJet
    {d c : P × PolarPoint → ℝ} {δ : ℝ} (A : NegativeChartRootFlowData d c δ)
    (k j : ℕ) (v : Fin k → P) (q : N04FlowPoint) :
    iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
      flowParameterField (negativeChartRootPlotTimeChange A.inverse) k (0, y.1)
        (fun i => (v i, (0 : PolarPoint))) (1, y.2)) q =
      iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        flowParameterField (fun z : (P × PolarPoint) × PolarPoint =>
          A.inverse z.1.1 z.1.2 z.2.1 z.2.2) k (0, y.1)
            (fun i => (v i, (0 : PolarPoint))) (1, y.2)) q := by
  simp only [flowParameterField, negativeChartRootPlotTimeChange, compactScalarFlowTime_one]

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_reverseTimeChange_spatialJet_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_reverseTimeChange_spatialJet_le
