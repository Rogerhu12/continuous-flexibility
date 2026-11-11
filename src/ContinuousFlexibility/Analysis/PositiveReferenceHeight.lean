import ContinuousFlexibility.Analysis.PositiveEndpointCutoff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Positive reference heights from endpoint data

The logarithmic endpoint fields are clipped with the same small cutoffs
used for the coordinate. Exponentiation gives a globally positive smooth
height, matching both endpoint germs and equal to one on every forbidden
set avoided by the cutoff collars.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def positiveReferenceHeight (l r δ : ℝ) (hL hR : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (positiveEndpointCutoff l δ x * Real.log (hL x) +
    positiveEndpointCutoff r δ x * Real.log (hR x))

theorem positiveReferenceHeight_pos
    (l r δ : ℝ) (hL hR : ℝ → ℝ) (x : ℝ) :
    0 < positiveReferenceHeight l r δ hL hR x :=
  Real.exp_pos _

theorem contDiff_positiveReferenceHeight
    {l r δ : ℝ} {hL hR : ℝ → ℝ} (hδ : 0 < δ)
    (hcL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ hL x)
    (hcR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ hR x)
    (hpL : ∀ x ∈ Metric.ball l δ, 0 < hL x)
    (hpR : ∀ x ∈ Metric.ball r δ, 0 < hR x) :
    ContDiff ℝ ∞ (positiveReferenceHeight l r δ hL hR) := by
  have hlogL : ∀ x ∈ Metric.ball l δ,
      ContDiffAt ℝ ∞ (fun y => Real.log (hL y)) x :=
    fun x hx => (hcL x hx).log (hpL x hx).ne'
  have hlogR : ∀ x ∈ Metric.ball r δ,
      ContDiffAt ℝ ∞ (fun y => Real.log (hR y)) x :=
    fun x hx => (hcR x hx).log (hpR x hx).ne'
  exact Real.contDiff_exp.comp
    ((contDiff_positiveEndpointCutoff_mul hδ hlogL).add
      (contDiff_positiveEndpointCutoff_mul hδ hlogR))

theorem positiveReferenceHeight_eq_one_on_forbidden
    {F : Set ℝ} {l r δ : ℝ} {hL hR : ℝ → ℝ} (hδ : 0 < δ)
    (havoidL : Disjoint (Metric.ball l δ) F)
    (havoidR : Disjoint (Metric.ball r δ) F) {x : ℝ} (hx : x ∈ F) :
    positiveReferenceHeight l r δ hL hR x = 1 := by
  have hxL : x ∉ Metric.ball l δ := fun h =>
    (Set.disjoint_left.mp havoidL) h hx
  have hxR : x ∉ Metric.ball r δ := fun h =>
    (Set.disjoint_left.mp havoidR) h hx
  simp only [positiveReferenceHeight,
    positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hxL,
    positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hxR,
    zero_mul, zero_add, Real.exp_zero]

/-- The same formula matches either endpoint height on a full two-sided germ. -/
theorem positiveReferenceHeight_endpoint_germ
    {l r δ : ℝ} {hL hR : ℝ → ℝ} (hδ : 0 < δ)
    (hgap : 2 * δ < r - l)
    (hpL : ∀ x ∈ Metric.ball l δ, 0 < hL x)
    (hpR : ∀ x ∈ Metric.ball r δ, 0 < hR x) (side : Bool) :
    positiveReferenceHeight l r δ hL hR =ᶠ[𝓝 (if side then r else l)]
      (if side then hR else hL) := by
  have hsep : 0 ≤ r - l := by linarith
  cases side
  · have hcutR := positiveEndpointCutoff_zero_germ_of_separation
      (c := l) (d := r) hδ (by
        rw [abs_sub_comm, abs_of_nonneg hsep]
        linarith)
    filter_upwards [positiveEndpointCutoff_one_germ l δ, hcutR,
      Metric.ball_mem_nhds l hδ] with x hxL hxR hx
    simp only [positiveReferenceHeight, hxL, hxR, Pi.one_apply, Pi.zero_apply,
      one_mul, zero_mul, add_zero]
    exact Real.exp_log (hpL x hx)
  · have hcutL := positiveEndpointCutoff_zero_germ_of_separation
      (c := r) (d := l) hδ (by
        rw [abs_of_nonneg hsep]
        linarith)
    filter_upwards [positiveEndpointCutoff_one_germ r δ, hcutL,
      Metric.ball_mem_nhds r hδ] with x hxR hxL hx
    simp only [positiveReferenceHeight, hxL, hxR, Pi.one_apply, Pi.zero_apply,
      one_mul, zero_mul, zero_add]
    exact Real.exp_log (hpR x hx)

end ContinuousFlexibility.Analysis
