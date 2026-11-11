import ContinuousFlexibility.Analysis.PositiveEndpointCutoff
import Mathlib.Analysis.Calculus.IteratedFDeriv.Lemmas

/-!
# Globalizing a genuinely smooth cylinder collar

A radial cutoff supported inside the given open collar gives one global
smooth field. It equals the original field as a joint germ along the
whole boundary circle, so every actual boundary jet is unchanged.
The auxiliary collar may depend on the field: no derivative of its
cutoff enters the endpoint jet identities or their numerical bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cylinderEndpointLocalization (c δ : ℝ) (f : PolarPoint → E) (p : PolarPoint) : E :=
  positiveEndpointCutoff c δ p.1 • f p

/-- The input is smooth on the actual open collar, not merely pointwise
smooth to all orders at its boundary. -/
theorem contDiff_cylinderEndpointLocalization
    {c δ : ℝ} {f : PolarPoint → E} (hδ : 0 < δ)
    (hf : ∀ p : PolarPoint, p.1 ∈ Metric.ball c δ → ContDiffAt ℝ ∞ f p) :
    ContDiff ℝ ∞ (cylinderEndpointLocalization c δ f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 ∈ tsupport (positiveEndpointCutoff c δ)
  · exact (((contDiff_positiveEndpointCutoff c δ).comp contDiff_fst).contDiffAt).smul
      (hf p (tsupport_positiveEndpointCutoff_subset_ball hδ hp))
  · have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
      (continuous_fst.tendsto p)
    have he : cylinderEndpointLocalization c δ f =ᶠ[𝓝 p] (fun _ => (0 : E)) := by
      filter_upwards [hz] with q hq
      have hq' : positiveEndpointCutoff c δ q.1 = 0 := by
        simpa only [Function.comp_apply, Pi.zero_apply] using hq
      simp only [cylinderEndpointLocalization, hq', zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem cylinderEndpointLocalization_eventuallyEq
    (c δ : ℝ) (f : PolarPoint → E) (θ : ℝ) :
    cylinderEndpointLocalization c δ f =ᶠ[𝓝 (c, θ)] f := by
  have hone := (positiveEndpointCutoff_one_germ c δ).comp_tendsto
    (continuous_fst.tendsto (c, θ))
  filter_upwards [hone] with p hp
  have hp' : positiveEndpointCutoff c δ p.1 = 1 := by
    simpa only [Function.comp_apply, Pi.one_apply] using hp
  simp only [cylinderEndpointLocalization, hp', one_smul]

/-- Actual boundary derivatives are unchanged at every order, regardless
of the size of the auxiliary globalization collar. -/
theorem iteratedFDeriv_cylinderEndpointLocalization_boundary
    (c δ : ℝ) (f : PolarPoint → E) (n : ℕ) (θ : ℝ) :
    iteratedFDeriv ℝ n (cylinderEndpointLocalization c δ f) (c, θ) =
      iteratedFDeriv ℝ n f (c, θ) :=
  ((cylinderEndpointLocalization_eventuallyEq c δ f θ).iteratedFDeriv ℝ n).self_of_nhds

/-- The periodic hypothesis is only needed where the original field is
actually used by the cutoff. -/
theorem cylinderEndpointLocalization_periodic
    {c δ T : ℝ} {f : PolarPoint → E} (hδ : 0 < δ)
    (hf : ∀ r ∈ Metric.ball c δ, ∀ θ, f (r, θ + T) = f (r, θ))
    (r θ : ℝ) :
    cylinderEndpointLocalization c δ f (r, θ + T) =
      cylinderEndpointLocalization c δ f (r, θ) := by
  by_cases hr : r ∈ Metric.ball c δ
  · simp only [cylinderEndpointLocalization, hf r hr θ]
  · simp only [cylinderEndpointLocalization,
      positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hr, zero_smul]

theorem cylinderEndpointLocalization_reflect
    {c δ s : ℝ} {f : PolarPoint → E} (hδ : 0 < δ)
    (hf : ∀ r ∈ Metric.ball c δ, ∀ θ, f (r, -θ) = s • f (r, θ))
    (r θ : ℝ) :
    cylinderEndpointLocalization c δ f (r, -θ) =
      s • cylinderEndpointLocalization c δ f (r, θ) := by
  by_cases hr : r ∈ Metric.ball c δ
  · simp only [cylinderEndpointLocalization, hf r hr θ, smul_smul]
    rw [mul_comm]
  · simp only [cylinderEndpointLocalization,
      positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hr, zero_smul, smul_zero]

/-- In particular the genuine collar supplies a global smooth representative
of all its boundary germs. The chosen radius is not a quantitative input. -/
theorem exists_global_cylinderField_of_collar
    {c δ : ℝ} {f : PolarPoint → E} (hδ : 0 < δ)
    (hf : ∀ p : PolarPoint, p.1 ∈ Metric.ball c δ → ContDiffAt ℝ ∞ f p) :
    ∃ F : PolarPoint → E, ContDiff ℝ ∞ F ∧
      ∀ θ, F =ᶠ[𝓝 (c, θ)] f :=
  ⟨cylinderEndpointLocalization c δ f,
    contDiff_cylinderEndpointLocalization hδ hf,
    cylinderEndpointLocalization_eventuallyEq c δ f⟩

end ContinuousFlexibility.Analysis

