module

public import ContinuousFlexibility.Analysis.OperatorCoefficientClassification
public import ContinuousFlexibility.Analysis.EffectiveRadialCoefficient
public import ContinuousFlexibility.Analysis.CoordinatePotentialRegularity

/-!
# Faithfulness at a genuine closure point

Continuity of the actual operator outputs extends the interior action to
the boundary. The pointwise test argument then gives actual mixed-field
differentiability there. Its interior equality extends by continuity and
excludes the degenerate alternative. No continuity of the stored angular
coefficient and no common smooth extension of both pieces is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem scalar_eq_at_closure_of_continuousAt
    {U : Set PolarPoint} {f g : PolarPoint → ℝ} {p : PolarPoint}
    (hp : p ∈ closure U) (hf : ContinuousAt f p) (hg : ContinuousAt g p)
    (he : EqOn f g U) : f p = g p := by
  haveI : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left nhdsWithin_le_nhds) (hg.mono_left nhdsWithin_le_nhds)
    (he.eventuallyEq_of_mem self_mem_nhdsWithin)

/-- Genuine operator-output continuity and interior coefficient equality
recover all stored coefficient values at the closure point. -/
theorem operatorCoefficients_eq_at_closure_of_output_continuous
    {U : Set PolarPoint} {L B : SymmetricCoefficients} {p : PolarPoint}
    (hp : p ∈ closure U) (hLa : DifferentiableAt ℝ L.a p) (hLa0 : L.a p ≠ 0)
    (hBa : ContDiffAt ℝ ∞ B.a p) (hBb : ContDiffAt ℝ ∞ B.b p)
    (hBc : ContDiffAt ℝ ∞ B.c p)
    (hdisc : 0 < B.b p ^ 2 - B.a p * B.c p)
    (hbeq : EqOn L.b B.b U)
    (houtput : ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u →
      ContinuousAt (divergenceOperator L u) p)
    (haction : ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u →
      EqOn (divergenceOperator L u) (divergenceOperator B u) U) :
    L.a p = B.a p ∧ L.b p = B.b p ∧ L.c p = B.c p := by
  have hBad := hBa.differentiableAt (by simp)
  have hBbd := hBb.differentiableAt (by simp)
  have hBcd := hBc.differentiableAt (by simp)
  have hop (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u) :
      divergenceOperator L u p = divergenceOperator B u p :=
    scalar_eq_at_closure_of_continuousAt hp (houtput u hu)
      (contDiffAt_divergenceOperator hBa hBb hBc hu.contDiffAt).continuousAt
      (haction u hu)
  have hrad : B.a p = L.a p := radialCoefficient_eq_of_operator_action hLa hBad
    (hop _ (contDiff_radialCenteredSquare p.1))
  have hBa0 : B.a p ≠ 0 := by rw [hrad]; exact hLa0
  have hLb := differentiableAt_mixedCoefficient_of_operator_action
    hLa hBad hBbd hBcd hBa0 hop
  have hvalue : L.b p = B.b p :=
    scalar_eq_at_closure_of_continuousAt hp hLb.continuousAt hBb.continuousAt hbeq
  rcases operatorCoefficients_value_alternative hLa hBad hBbd hBcd hBa0 hop with hgood | hbad
  · exact hgood
  · have hzero : B.b p = 0 := by linarith only [hvalue, hbad.2.1]
    rw [hzero, hbad.2.2] at hdisc
    norm_num at hdisc

end ContinuousFlexibility.Analysis
