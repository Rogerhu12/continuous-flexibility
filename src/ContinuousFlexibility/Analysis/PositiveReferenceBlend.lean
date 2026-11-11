import ContinuousFlexibility.Analysis.PositiveEndpointCutoffIntegral

/-!
# The normalized positive reference slope

The middle slope is an explicit scalar fixed by the integral constraint.
Small endpoint masses make this scalar positive. A common positive lower
bound for the endpoint slopes then gives a genuine positive lower bound
on the whole real line.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def positiveReferenceMiddleMass (l r δ : ℝ) : ℝ :=
  ∫ x in l..r,
    (1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x)

def positiveReferenceEndMass (l r δ : ℝ) (aL aR : ℝ → ℝ) : ℝ :=
  ∫ x in l..r,
    (positiveEndpointCutoff l δ x * aL x + positiveEndpointCutoff r δ x * aR x)

/-- The unique constant middle slope making the total integral equal to one. -/
def positiveReferenceScale (l r δ : ℝ) (aL aR : ℝ → ℝ) : ℝ :=
  (1 - positiveReferenceEndMass l r δ aL aR) / positiveReferenceMiddleMass l r δ

def positiveReferenceSlope (l r δ : ℝ) (aL aR : ℝ → ℝ) (x : ℝ) : ℝ :=
  positiveEndpointCutoff l δ x * aL x + positiveEndpointCutoff r δ x * aR x +
    positiveReferenceScale l r δ aL aR *
      (1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x)

theorem contDiff_positiveReferenceSlope
    {l r δ : ℝ} {aL aR : ℝ → ℝ} (hδ : 0 < δ)
    (hL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ aL x)
    (hR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ aR x) :
    ContDiff ℝ ∞ (positiveReferenceSlope l r δ aL aR) :=
  ((contDiff_positiveEndpointCutoff_mul hδ hL).add
    (contDiff_positiveEndpointCutoff_mul hδ hR)).add
      (contDiff_const.mul
        ((contDiff_const.sub (contDiff_positiveEndpointCutoff l δ)).sub
          (contDiff_positiveEndpointCutoff r δ)))

theorem positiveReferenceEndMass_le
    {l r δ M : ℝ} {aL aR : ℝ → ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ aL x)
    (hR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ aR x)
    (hbL : ∀ x ∈ Metric.ball l δ, |aL x| ≤ M)
    (hbR : ∀ x ∈ Metric.ball r δ, |aR x| ≤ M) :
    positiveReferenceEndMass l r δ aL aR ≤ 2 * M * δ := by
  have hleft := abs_integral_positiveEndpointCutoff_mul
    (c := l) (d := r) hδ hM hL hbL
  have hright := abs_integral_positiveEndpointCutoff_mul
    (c := r) (d := l) hδ hM hR hbR
  rw [intervalIntegral.integral_symm, abs_neg] at hright
  unfold positiveReferenceEndMass
  rw [intervalIntegral.integral_add
    ((contDiff_positiveEndpointCutoff_mul hδ hL).continuous.intervalIntegrable
      (μ := MeasureTheory.volume) l r)
    ((contDiff_positiveEndpointCutoff_mul hδ hR).continuous.intervalIntegrable
      (μ := MeasureTheory.volume) l r)]
  have hleft' := (le_abs_self _).trans hleft
  have hright' := (le_abs_self _).trans hright
  linarith

theorem positiveReferenceScale_pos
    {l r δ : ℝ} {aL aR : ℝ → ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l)
    (hsmall : positiveReferenceEndMass l r δ aL aR < 1) :
    0 < positiveReferenceScale l r δ aL aR :=
  div_pos (sub_pos.mpr hsmall)
    (integral_positiveEndpointCutoff_complement_pos hδ hgap)

/-- The lower bound is global, including the portions beyond both roots. -/
theorem positiveReferenceSlope_lower
    {l r δ A : ℝ} {aL aR : ℝ → ℝ} (hδ : 0 < δ)
    (hgap : 2 * δ ≤ r - l)
    (hL : ∀ x ∈ Metric.ball l δ, A ≤ aL x)
    (hR : ∀ x ∈ Metric.ball r δ, A ≤ aR x) (x : ℝ) :
    min A (positiveReferenceScale l r δ aL aR) ≤
      positiveReferenceSlope l r δ aL aR x := by
  let μ := positiveReferenceScale l r δ aL aR
  have hηL := positiveEndpointCutoff_nonneg l δ x
  have hηR := positiveEndpointCutoff_nonneg r δ x
  have hη := positiveEndpointCutoff_add_le_one hδ hgap x
  have hmid : 0 ≤ 1 - positiveEndpointCutoff l δ x -
      positiveEndpointCutoff r δ x := by linarith
  have hAL := positiveEndpointCutoff_mul_lower hδ hL x
  have hAR := positiveEndpointCutoff_mul_lower hδ hR x
  have hmL := mul_le_mul_of_nonneg_right (min_le_left A μ) hηL
  have hmR := mul_le_mul_of_nonneg_right (min_le_left A μ) hηR
  have hmM := mul_le_mul_of_nonneg_right (min_le_right A μ) hmid
  change min A μ ≤ positiveEndpointCutoff l δ x * aL x +
    positiveEndpointCutoff r δ x * aR x +
    μ * (1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x)
  nlinarith

theorem integral_positiveReferenceSlope
    {l r δ : ℝ} {aL aR : ℝ → ℝ} (hδ : 0 < δ)
    (hgap : 2 * δ < r - l)
    (hL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ aL x)
    (hR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ aR x) :
    (∫ x in l..r, positiveReferenceSlope l r δ aL aR x) = 1 := by
  have hcL := (contDiff_positiveEndpointCutoff_mul hδ hL).continuous
  have hcR := (contDiff_positiveEndpointCutoff_mul hδ hR).continuous
  have hcM : Continuous (fun x : ℝ =>
      1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x) :=
    (continuous_const.sub (contDiff_positiveEndpointCutoff l δ).continuous).sub
      (contDiff_positiveEndpointCutoff r δ).continuous
  have hmass : positiveReferenceMiddleMass l r δ ≠ 0 :=
    (integral_positiveEndpointCutoff_complement_pos hδ hgap).ne'
  unfold positiveReferenceSlope
  rw [intervalIntegral.integral_add
    ((hcL.add hcR).intervalIntegrable (μ := MeasureTheory.volume) l r)
    ((continuous_const.mul hcM).intervalIntegrable (μ := MeasureTheory.volume) l r),
    intervalIntegral.integral_const_mul]
  change positiveReferenceEndMass l r δ aL aR +
    positiveReferenceScale l r δ aL aR * positiveReferenceMiddleMass l r δ = 1
  rw [positiveReferenceScale, div_mul_cancel₀ _ hmass]
  ring

/-- Both endpoint slope germs are matched by the same construction. -/
theorem positiveReferenceSlope_endpoint_germ
    {l r δ : ℝ} {aL aR : ℝ → ℝ} (hδ : 0 < δ)
    (hgap : 2 * δ < r - l) (side : Bool) :
    positiveReferenceSlope l r δ aL aR =ᶠ[𝓝 (if side then r else l)]
      (if side then aR else aL) := by
  have hsep : 0 ≤ r - l := by linarith
  cases side
  · have hR := positiveEndpointCutoff_zero_germ_of_separation
      (c := l) (d := r) hδ (by
        rw [abs_sub_comm, abs_of_nonneg hsep]
        linarith)
    filter_upwards [positiveEndpointCutoff_one_germ l δ, hR] with x hxL hxR
    simp only [positiveReferenceSlope, hxL, hxR, Pi.one_apply, Pi.zero_apply,
      one_mul, zero_mul, sub_self, sub_zero, mul_zero, add_zero]
  · have hL := positiveEndpointCutoff_zero_germ_of_separation
      (c := r) (d := l) hδ (by
        rw [abs_of_nonneg hsep]
        linarith)
    filter_upwards [positiveEndpointCutoff_one_germ r δ, hL] with x hxR hxL
    simp only [positiveReferenceSlope, hxL, hxR, Pi.one_apply, Pi.zero_apply,
      one_mul, zero_mul, sub_zero, sub_self, mul_zero, zero_add, add_zero]

end ContinuousFlexibility.Analysis
