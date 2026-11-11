import ContinuousFlexibility.Analysis.PositiveReferenceBlend
import ContinuousFlexibility.Analysis.CircleInverseExistence
import ContinuousFlexibility.Analysis.ParameterizedScalarInverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The actual positive reference coordinate

Integrating the normalized slope gives a smooth coordinate with prescribed
endpoint values. Positivity gives a genuine global bijection and a smooth
actual inverse. Endpoint matching uses equality of actual derivatives and
one value, rather than an asserted Taylor compatibility.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def positiveReferenceCoordinate (l r δ : ℝ) (aL aR : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in l..x, positiveReferenceSlope l r δ aL aR t

theorem hasDerivAt_positiveReferenceCoordinate
    {l r δ : ℝ} {aL aR : ℝ → ℝ} (hδ : 0 < δ)
    (hL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ aL x)
    (hR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ aR x) (x : ℝ) :
    HasDerivAt (positiveReferenceCoordinate l r δ aL aR)
      (positiveReferenceSlope l r δ aL aR x) x :=
  ((contDiff_positiveReferenceSlope hδ hL hR).continuous.integral_hasStrictDerivAt l x).hasDerivAt

theorem contDiff_positiveReferenceCoordinate
    {l r δ : ℝ} {aL aR : ℝ → ℝ} (hδ : 0 < δ)
    (hL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ aL x)
    (hR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ aR x) :
    ContDiff ℝ ∞ (positiveReferenceCoordinate l r δ aL aR) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_positiveReferenceCoordinate hδ hL hR x).differentiableAt, ?_⟩
  have heq : deriv (positiveReferenceCoordinate l r δ aL aR) =
      positiveReferenceSlope l r δ aL aR :=
    funext (fun x => (hasDerivAt_positiveReferenceCoordinate hδ hL hR x).deriv)
  rw [heq]
  exact contDiff_positiveReferenceSlope hδ hL hR

theorem positiveReferenceCoordinate_left (l r δ : ℝ) (aL aR : ℝ → ℝ) :
    positiveReferenceCoordinate l r δ aL aR l = 0 := by
  simp only [positiveReferenceCoordinate, intervalIntegral.integral_same]

theorem positiveReferenceCoordinate_right
    {l r δ : ℝ} {aL aR : ℝ → ℝ} (hδ : 0 < δ)
    (hgap : 2 * δ < r - l)
    (hL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ aL x)
    (hR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ aR x) :
    positiveReferenceCoordinate l r δ aL aR r = 1 :=
  integral_positiveReferenceSlope hδ hgap hL hR

/-- The positive slope gives the actual inverse, including its smoothness.
The smallness input is the explicit endpoint integral of the chosen fields. -/
theorem positiveReferenceCoordinate_bijective_smoothInverse
    {l r δ A : ℝ} {aL aR : ℝ → ℝ} (hδ : 0 < δ)
    (hgap : 2 * δ < r - l)
    (hL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ aL x)
    (hR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ aR x)
    (hA : 0 < A)
    (hAL : ∀ x ∈ Metric.ball l δ, A ≤ aL x)
    (hAR : ∀ x ∈ Metric.ball r δ, A ≤ aR x)
    (hsmall : positiveReferenceEndMass l r δ aL aR < 1) :
    Function.Bijective (positiveReferenceCoordinate l r δ aL aR) ∧
      ContDiff ℝ ∞ (Function.invFun (positiveReferenceCoordinate l r δ aL aR)) := by
  let Y := positiveReferenceCoordinate l r δ aL aR
  let A₀ := min A (positiveReferenceScale l r δ aL aR)
  have hA₀ : 0 < A₀ := lt_min hA (positiveReferenceScale_pos hδ hgap hsmall)
  have hder : ∀ x : ℝ, A₀ ≤ deriv Y x := by
    intro x
    change A₀ ≤ deriv (positiveReferenceCoordinate l r δ aL aR) x
    rw [(hasDerivAt_positiveReferenceCoordinate hδ hL hR x).deriv]
    exact positiveReferenceSlope_lower hδ hgap.le hAL hAR x
  have hbij := bijective_of_deriv_lower_bound hA₀ hder
  have hY : ContDiff ℝ ∞ Y := contDiff_positiveReferenceCoordinate hδ hL hR
  have hInv : ContDiff ℝ ∞ (fun z : ℝ × ℝ => Function.invFun Y z.2) :=
    contDiff_parameterized_scalar_rightInverse
      (F := fun z : ℝ × ℝ => Y z.2)
      (hY.comp contDiff_snd)
      (fun z => hA₀.trans_le (hder z.2))
      (fun z => Function.rightInverse_invFun hbij.2 z.2)
  have hline : ContDiff ℝ ∞ (fun y : ℝ => ((0 : ℝ), y)) :=
    contDiff_const.prodMk contDiff_id
  exact ⟨hbij, hInv.comp hline⟩

/-- Equality of derivative germs and a value gives equality of function
germs on the real line. The second field is required smooth only locally. -/
theorem eventuallyEq_of_deriv_germ_and_value
    {f g : ℝ → ℝ} {c : ℝ} (hf : Differentiable ℝ f)
    (hg : ∀ᶠ x in 𝓝 c, DifferentiableAt ℝ g x)
    (hder : deriv f =ᶠ[𝓝 c] deriv g) (hc : f c = g c) :
    f =ᶠ[𝓝 c] g := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hg.and hder)
  have heq : EqOn f g (Metric.ball c δ) :=
    isOpen_ball.eqOn_of_deriv_eq (convex_ball c δ).isPreconnected
      hf.differentiableOn
      (fun x hx => (hball hx).1.differentiableWithinAt)
      (fun x hx => (hball hx).2) (Metric.mem_ball_self hδ) hc
  filter_upwards [Metric.ball_mem_nhds c hδ] with x hx
  exact heq hx

/-- The coordinate agrees with the prescribed endpoint coordinate germs.
The right endpoint field is already normalized to have value one. -/
theorem positiveReferenceCoordinate_endpoint_germ
    {l r δ : ℝ} {yL yR : ℝ → ℝ} (hδ : 0 < δ)
    (hgap : 2 * δ < r - l)
    (hL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ yL x)
    (hR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ yR x)
    (hvL : yL l = 0) (hvR : yR r = 1) (side : Bool) :
    positiveReferenceCoordinate l r δ (deriv yL) (deriv yR) =ᶠ[𝓝 (if side then r else l)]
      (if side then yR else yL) := by
  have hdL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ (deriv yL) x :=
    fun x hx => (hL x hx).derivWithin (by simp)
  have hdR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ (deriv yR) x :=
    fun x hx => (hR x hx).derivWithin (by simp)
  have hY := contDiff_positiveReferenceCoordinate hδ hdL hdR
  have hder : deriv (positiveReferenceCoordinate l r δ (deriv yL) (deriv yR)) =
      positiveReferenceSlope l r δ (deriv yL) (deriv yR) :=
    funext (fun x => (hasDerivAt_positiveReferenceCoordinate hδ hdL hdR x).deriv)
  apply eventuallyEq_of_deriv_germ_and_value (hY.differentiable (by simp))
  · cases side
    · filter_upwards [Metric.ball_mem_nhds l hδ] with x hx
      exact (hL x hx).differentiableAt (by simp)
    · filter_upwards [Metric.ball_mem_nhds r hδ] with x hx
      exact (hR x hx).differentiableAt (by simp)
  · rw [hder]
    have h := positiveReferenceSlope_endpoint_germ
      (aL := deriv yL) (aR := deriv yR) hδ hgap side
    cases side <;> exact h
  · cases side
    · exact (positiveReferenceCoordinate_left l r δ (deriv yL) (deriv yR)).trans hvL.symm
    · exact (positiveReferenceCoordinate_right hδ hgap hdL hdR).trans hvR.symm

end ContinuousFlexibility.Analysis
