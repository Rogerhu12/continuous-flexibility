import ContinuousFlexibility.Analysis.N04NegativeChartFieldJetBounds
import ContinuousFlexibility.Analysis.RootRescaledFieldJets
import ContinuousFlexibility.Analysis.N01cFlowVariationCircleData

/-!
# Actual state jets of the regularized root field

The root field is linear in its drift and divided speed. Taking genuine
state derivatives therefore preserves the coefficient weight exactly.
The spatial estimate uses those same derivatives at the physical point;
it does not require any estimate on the negative radial extension.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- Evaluation on state directions commutes with the actual polynomial
root regularization. The two independent radial slots remain fixed. -/
theorem negativeChartRootPlotField_stateJet
    {d c : P × PolarPoint → ℝ} (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (δ : ℝ) (k : ℕ) (v : Fin k → P) (t : ℝ) (q : N04FlowPoint) :
    flowParameterField (negativeChartRootPlotField d c δ) k (0, q.1)
      (fun i => (v i, (0 : PolarPoint))) (t, q.2) =
        rootRescaledField (negativeChartCoefficientJet d k v)
          (negativeChartCoefficientJet c k v) δ (t, q) := by
  let f : P × PolarPoint → ℝ := fun z => negativeChartRootPlotField d c δ (z, (t, q.2))
  have hf : ContDiff ℝ ∞ f :=
    (negativeChartRootPlotField_contDiff hd hc δ).comp (contDiff_id.prodMk contDiff_const)
  change iteratedFDeriv ℝ k f (0, q.1) (fun i => (v i, (0 : PolarPoint))) = _
  rw [← flowParameterField_eq_joint hf k 0 v q.1]
  let p : PolarPoint := (δ * q.1.1 * t ^ 2, q.2)
  let a : ℝ := 2 * (δ * q.1.1) * t
  let b : ℝ := 2 * (δ * q.1.2) * t ^ 2
  have hdp : ContDiff ℝ ∞ (fun y : P => d (y, p)) :=
    hd.comp (contDiff_id.prodMk contDiff_const)
  have hcp : ContDiff ℝ ∞ (fun y : P => c (y, p)) :=
    hc.comp (contDiff_id.prodMk contDiff_const)
  have had : ContDiff ℝ ∞ (fun y : P => a • d (y, p)) := contDiff_const.smul hdp
  have hbc : ContDiff ℝ ∞ (fun y : P => b • c (y, p)) := contDiff_const.smul hcp
  have he : (fun y : P => f (y, q.1)) =
      (fun y : P => a • d (y, p)) + (fun y : P => b • c (y, p)) := rfl
  change iteratedFDeriv ℝ k (fun y : P => f (y, q.1)) 0 v = _
  rw [he, iteratedFDeriv_add_apply
    (had.contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
    (hbc.contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞)),
    iteratedFDeriv_const_smul_apply' (a := a)
      (hdp.contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞)),
    iteratedFDeriv_const_smul_apply' (a := b)
      (hcp.contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞)),
    ContinuousMultilinearMap.add_apply]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have hde : iteratedFDeriv ℝ k (fun y : P => d (y, p)) 0 v =
      negativeChartCoefficientJet d k v p := flowParameterField_eq_joint hd k 0 v p
  have hce : iteratedFDeriv ℝ k (fun y : P => c (y, p)) 0 v =
      negativeChartCoefficientJet c k v p := flowParameterField_eq_joint hc k 0 v p
  rw [hde, hce]

/-- The same-order root estimate retains a marked coefficient weight
and charges only `j - 1` to the spatial interpolation degree. -/
theorem negativeChartRootPlotField_stateJet_spatial_le
    {d c : P × PolarPoint → ℝ} (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    {δ M W ρ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hM : 0 ≤ M) (hW : 0 ≤ W) (hρ : 1 ≤ ρ)
    (k j D : ℕ) (v : Fin k → P) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {q : N04FlowPoint} (hq : q.1 ∈ n04FlowParameterBox)
    (hdb : ∀ l, l ≤ j →
      ‖iteratedFDeriv ℝ l (negativeChartCoefficientJet d k v)
        (δ * q.1.1 * t ^ 2, q.2)‖ ≤ M * W * ρ ^ (l - 1 + D))
    (hcb : ∀ l, l ≤ j →
      ‖iteratedFDeriv ℝ l (negativeChartCoefficientJet c k v)
        (δ * q.1.1 * t ^ 2, q.2)‖ ≤ M * W * ρ ^ (l - 1 + D)) :
    ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
      flowParameterField (negativeChartRootPlotField d c δ) k (0, y.1)
        (fun i => (v i, (0 : PolarPoint))) (t, y.2)) q‖ ≤
      (4 * linearWeightedCompositionJetConstant j) * M * W * ρ ^ (j - 1 + D) := by
  have he : (fun y : N04FlowPoint =>
      flowParameterField (negativeChartRootPlotField d c δ) k (0, y.1)
        (fun i => (v i, (0 : PolarPoint))) (t, y.2)) =
      fun y : N04FlowPoint => rootRescaledField (negativeChartCoefficientJet d k v)
        (negativeChartCoefficientJet c k v) δ (t, y) :=
    funext (negativeChartRootPlotField_stateJet hd hc δ k v t)
  rw [he]
  have hMW : 0 ≤ M * W := mul_nonneg hM hW
  have hscale (l : ℕ) (hl : l ≤ j) :
      M * W * ρ ^ (l - 1 + D) ≤ M * W * ρ ^ (j - 1 + D) :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hρ (Nat.add_le_add_right (Nat.sub_le_sub_right hl 1) D)) hMW
  have hb := rootRescaledField_jet_le
    (negativeChartCoefficientJet_contDiff hd k v) (negativeChartCoefficientJet_contDiff hc k v)
    hδ hδone (mul_nonneg hMW (pow_nonneg (zero_le_one.trans hρ) _)) ht hq j
    (fun l hl => (hdb l hl).trans (hscale l hl))
    (fun l hl => (hcb l hl).trans (hscale l hl))
  exact hb.trans_eq (by ring)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.negativeChartRootPlotField_stateJet_spatial_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.negativeChartRootPlotField_stateJet_spatial_le
