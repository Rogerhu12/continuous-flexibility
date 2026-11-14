module

public import ContinuousFlexibility.Analysis.N04FlowJetEquations
public import ContinuousFlexibility.Analysis.FlowJetIntegralGronwall

/-!
# Gronwall applied to the actual mixed spatial flow jets

The integral equation and closed-time continuity of the actual
Fréchet jets were derived from the original ODE. This adapter applies
the norm estimate to those genuine multilinear-valued functions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04Flow_spatialJet_norm_le_of_composed_bound
    {F : ℝ × N04FlowPoint → ℝ} {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) (n : ℕ) (q : N04FlowPoint)
    {α : ℝ → ℝ} {M Λ : ℝ}
    (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hα0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ α t)
    (hM : 0 ≤ M) (hΛ : (∫ t in (0 : ℝ)..1, α t) ≤ Λ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖parametricSpatialJet (n04FlowComposedField F Θ) n (q, t)‖ ≤
        α t * ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => Θ y.1 t y.2) q‖ + M) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => Θ y.1 t y.2) q‖ ≤
        (‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => y.2) q‖ + M) * Real.exp Λ := by
  have hu : ContinuousOn
      (fun t : ℝ => iteratedFDeriv ℝ n
        (fun y : N04FlowPoint => Θ y.1 t y.2) q) (Icc (0 : ℝ) 1) :=
    (n04Flow_spatialJet_continuousOn hF hperiod hΘ n).comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun t ht => ⟨mem_univ q, ht⟩)
  have hsource : ContinuousOn
      (fun t : ℝ => parametricSpatialJet (n04FlowComposedField F Θ) n (q, t))
      (Icc (0 : ℝ) 1) :=
    (n04FlowComposedField_spatialJet_continuousOn hF hperiod hΘ n).comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun t ht => ⟨mem_univ q, ht⟩)
  exact flowJet_norm_le_of_integral_equation hu hsource hα hα0 hM hΛ
    (fun t ht => n04Flow_spatialJet_integral_eq hF hperiod hΘ n q ht) hbound

end ContinuousFlexibility.Analysis
