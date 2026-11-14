module

public import ContinuousFlexibility.Analysis.RootDividedModelMaterialJets
public import ContinuousFlexibility.Analysis.RootDividedModelPeriodicity
public import ContinuousFlexibility.Analysis.PeriodicOrdinaryJetBounds
public import ContinuousFlexibility.Analysis.RootChartExtensionGeometry

/-!
# Actual root model jets at every angle

The positive-order chart jets and every height and inverse-height jet
extend from one period to all angles. The chart's zeroth-order lift is
deliberately absent. No constant, neighborhood or loss is changed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def RootPhysicalFieldJetBound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (B : ℕ → ℝ) (z : E)
    (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) (q : PolarPoint) : Prop :=
  ContDiffAt ℝ ∞ F q ∧ ContDiffAt ℝ ∞ h q ∧ 0 < h q ∧
    (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F q‖ ≤
      B n * (1 + p (n + loss) z)) ∧
    PointwiseMaterialJetBound p loss B z h q ∧
    PointwiseMaterialJetBound p loss B z (fun y => (h y)⁻¹) q

theorem rootDividedModel_jetBound_allAngles
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {B : ℕ → ℝ} {z : E}
    {G : ℝ × ℝ × ℝ → ℝ} {V : PolarPoint → ℝ} {δ r : ℝ}
    (hδ : 0 < δ) (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi)
    (hVperiod : ∀ x θ, V (x, θ + Real.pi) = V (x, θ))
    (hvalues : ∀ θ : ℝ, ContDiffAt ℝ ∞ V (r, θ) ∧
      0 < V (r, θ) ∧ 0 < extendedRootOddCoefficient G (r, θ))
    (hjet : ∀ θ ∈ Icc (-Real.pi) Real.pi,
      RootDividedModelJetBound p loss B z δ V G (r, θ)) :
    ∀ θ : ℝ, RootPhysicalFieldJetBound p loss B z
      (extendedRootEvenOddChart G) (rootDividedHeight δ V G) (r, θ) := by
  have hχperiod : ∀ x, 0 ≤ x →
      Function.Periodic (fun θ => rootOddCoefficient G (x, θ)) Real.pi :=
    fun x _ => rootOddCoefficient_periodic hperiod x
  have hφperiod : ∀ x, 0 ≤ x → ∀ θ,
      rootEven G (x, θ + Real.pi) = rootEven G (x, θ) + Real.pi :=
    fun x _ θ => rootEven_period_add hperiod x θ
  have hχsmooth := contDiff_extendedRootOddCoefficient hG Real.pi_ne_zero hχperiod
  have hF (θ : ℝ) : ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) (r, θ) :=
    contDiffAt_extendedRootEvenOddChart_of_ne_zero hG Real.pi_ne_zero
      hχperiod hφperiod (hvalues θ).2.2.ne'
  have hH (θ : ℝ) : ContDiffAt ℝ ∞ (rootDividedHeight δ V G) (r, θ) ∧
      0 < rootDividedHeight δ V G (r, θ) :=
    contDiffAt_rootDividedHeight hδ (hvalues θ).1 hχsmooth.contDiffAt
      (hvalues θ).2.1 (hvalues θ).2.2
  have hFperiod := extendedRootEvenOddChart_period hχperiod hφperiod
  have hHperiod := rootDividedHeight_period_add (δ := δ) hperiod hVperiod
  have hIperiod (x θ : ℝ) :
      (rootDividedHeight δ V G (x, θ + Real.pi))⁻¹ =
        (rootDividedHeight δ V G (x, θ))⁻¹ :=
    congrArg (fun t : ℝ => t⁻¹) (hHperiod x θ)
  intro θ
  refine ⟨hF θ, (hH θ).1, (hH θ).2, ?_, ?_, ?_⟩
  · intro n hn
    exact norm_iteratedFDeriv_le_of_snd_periodic n
      (iteratedFDeriv_snd_periodic_of_lift hFperiod hF hn)
      (fun t ht => (hjet t ht).1.2.2.1 n) θ
  · intro n
    exact norm_iteratedFDeriv_le_of_snd_periodic n
      (iteratedFDeriv_snd_periodic_of_periodic hHperiod n r)
      (fun t ht => (hjet t ht).2.2.2.1 n) θ
  · intro n
    exact norm_iteratedFDeriv_le_of_snd_periodic n
      (iteratedFDeriv_snd_periodic_of_periodic hIperiod n r)
      (fun t ht => (hjet t ht).2.2.2.2 n) θ

end ContinuousFlexibility.Analysis
