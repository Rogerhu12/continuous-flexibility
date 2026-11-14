module

public import ContinuousFlexibility.Radial.SeedCentralCutoff
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A positive bridge from the decaying cone mode to the growing cone mode

The slope below is the logarithmic derivative of r²+r⁻² on the cone w=r.
It runs from -2 to 2. Its Riccati identity gives profile slope exactly one.
The uniform cutoff construction makes both endpoint slopes exact without
losing positivity. This also covers a tail whose auxiliary cone solution
has only the exceptional pure mode; no first-band assumption is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

def positiveConeBridgeSlope (y : ℝ) : ℝ := 2 - 4 / (1 + exp (4 * y))

theorem positiveConeBridgeSlope_contDiff :
    ContDiff ℝ ∞ positiveConeBridgeSlope := by
  apply contDiff_const.sub
  exact contDiff_const.div
    (contDiff_const.add ((contDiff_const.mul contDiff_id).exp))
    (fun y => (show 0 < 1 + exp (4 * y) by positivity).ne')

theorem positiveConeBridgeSlope_bounds (y : ℝ) :
    -2 < positiveConeBridgeSlope y ∧ positiveConeBridgeSlope y < 2 := by
  have hden : 0 < 1 + exp (4 * y) := by positivity
  have hq : 0 < (4 : ℝ) / (1 + exp (4 * y)) := div_pos (by norm_num) hden
  have hq' : (4 : ℝ) / (1 + exp (4 * y)) < 4 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [exp_pos (4 * y)]
  dsimp only [positiveConeBridgeSlope]
  constructor <;> linarith

theorem positiveConeBridgeSlope_below_four (y : ℝ) :
    positiveConeBridgeSlope y < 4 :=
  (positiveConeBridgeSlope_bounds y).2.trans (by norm_num)

theorem hasDerivAt_positiveConeBridgeSlope (y : ℝ) :
    HasDerivAt positiveConeBridgeSlope (4 - positiveConeBridgeSlope y ^ 2) y := by
  have he := ((hasDerivAt_id' y).const_mul (4 : ℝ)).exp
  have hden : 1 + exp (4 * y) ≠ 0 := (show 0 < 1 + exp (4 * y) by positivity).ne'
  have h := (hasDerivAt_const y (2 : ℝ)).sub
    ((hasDerivAt_const y (4 : ℝ)).div (he.const_add 1) hden)
  apply h.congr_deriv
  simp only [positiveConeBridgeSlope, Function.comp_apply]
  field_simp [hden]
  <;> ring

theorem positiveConeBridgeSlope_connectorSlope (y : ℝ) :
    connectorSlope positiveConeBridgeSlope y = 0 := by
  rw [connectorSlope, (hasDerivAt_positiveConeBridgeSlope y).deriv]
  rw [show positiveConeBridgeSlope y ^ 2 +
    (4 - positiveConeBridgeSlope y ^ 2) - 4 = 0 by ring, zero_div]

theorem positiveConeBridgeSlope_ratio (y : ℝ) :
    (positiveConeBridgeSlope y ^ 2 - positiveConeBridgeSlope y +
      deriv positiveConeBridgeSlope y) / (4 - positiveConeBridgeSlope y) = 1 := by
  rw [← one_add_connectorSlope positiveConeBridgeSlope (positiveConeBridgeSlope_below_four y),
    positiveConeBridgeSlope_connectorSlope, add_zero]

theorem positiveConeBridgeSlope_reciprocal (y : ℝ) :
    positiveConeBridgeSlope y = -2 + 4 / (1 + exp (-4 * y)) := by
  have hE : exp (4 * y) ≠ 0 := (exp_pos (4 * y)).ne'
  have hD : 1 + exp (4 * y) ≠ 0 := (show 0 < 1 + exp (4 * y) by positivity).ne'
  have hI : 1 + (exp (4 * y))⁻¹ ≠ 0 :=
    (show 0 < 1 + (exp (4 * y))⁻¹ by positivity).ne'
  rw [positiveConeBridgeSlope, show -4 * y = -(4 * y) by ring, exp_neg]
  field_simp [hE, hD, hI]
  <;> ring

theorem positiveConeBridgeSlope_left_tendsto :
    Tendsto positiveConeBridgeSlope atBot (𝓝 (-2)) := by
  change Tendsto (fun y : ℝ => 2 - 4 / (1 + exp (4 * y))) atBot (𝓝 (-2))
  have ht : Tendsto (fun y : ℝ => exp (4 * y)) atBot (𝓝 0) :=
    tendsto_exp_atBot.comp (Tendsto.const_mul_atBot (by norm_num) tendsto_id)
  have h := (tendsto_const_nhds (x := (2 : ℝ))).sub
    ((tendsto_const_nhds (x := (4 : ℝ))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).add ht) (by norm_num))
  simpa only [positiveConeBridgeSlope, Pi.div_apply, add_zero, div_one,
    show (2 : ℝ) - 4 = -2 by norm_num] using h

theorem positiveConeBridgeSlope_right_tendsto :
    Tendsto positiveConeBridgeSlope atTop (𝓝 2) := by
  have ht : Tendsto (fun y : ℝ => exp (-4 * y)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (by norm_num) tendsto_id)
  have h := (tendsto_const_nhds (x := (-2 : ℝ))).add
    ((tendsto_const_nhds (x := (4 : ℝ))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).add ht) (by norm_num))
  have heq : positiveConeBridgeSlope = fun y => -2 + 4 / (1 + exp (-4 * y)) :=
    funext positiveConeBridgeSlope_reciprocal
  rw [heq]
  simpa only [Pi.div_apply, add_zero, div_one, show (-2 : ℝ) + 4 = 2 by norm_num] using h

theorem positiveConeBridgeSlope_deriv_tendsto {F : Filter ℝ} {a : ℝ}
    (ha : a ^ 2 = 4) (hk : Tendsto positiveConeBridgeSlope F (𝓝 a)) :
    Tendsto (deriv positiveConeBridgeSlope) F (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (4 : ℝ))).sub (hk.pow 2)
  have heq : deriv positiveConeBridgeSlope = fun y => 4 - positiveConeBridgeSlope y ^ 2 :=
    funext fun y => (hasDerivAt_positiveConeBridgeSlope y).deriv
  rw [heq]
  simpa only [ha, sub_self] using h

theorem positiveConeBridgeSlope_C1_left :
    Tendsto positiveConeBridgeSlope atBot (𝓝 (-2)) ∧
      Tendsto (deriv positiveConeBridgeSlope) atBot (𝓝 0) :=
  ⟨positiveConeBridgeSlope_left_tendsto,
    positiveConeBridgeSlope_deriv_tendsto (by norm_num) positiveConeBridgeSlope_left_tendsto⟩

theorem positiveConeBridgeSlope_C1_right :
    Tendsto positiveConeBridgeSlope atTop (𝓝 2) ∧
      Tendsto (deriv positiveConeBridgeSlope) atTop (𝓝 0) :=
  ⟨positiveConeBridgeSlope_right_tendsto,
    positiveConeBridgeSlope_deriv_tendsto (by norm_num) positiveConeBridgeSlope_right_tendsto⟩

/-- The cut-off bridge is positive also in its retained middle interval. -/
theorem SeedSlopeCutoff.positive_bridge
    (B : SeedSlopeCutoff positiveConeBridgeSlope (-2) 2 0 0) (y : ℝ) :
    (3 / 4 : ℝ) ≤
      (B.slope y ^ 2 - B.slope y + deriv B.slope y) / (4 - B.slope y) := by
  by_cases hL : y ≤ B.left
  · exact B.positive_left y hL
  by_cases hR : B.right ≤ y
  · exact B.positive_right y hR
  have hyL : B.left < y := lt_of_not_ge hL
  have hyR : y < B.right := lt_of_not_ge hR
  have hEq : B.slope =ᶠ[𝓝 y] positiveConeBridgeSlope :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds hyL hyR)
      (fun t ht => B.retained t ⟨ht.1.le, ht.2.le⟩)
  rw [B.retained y ⟨hyL.le, hyR.le⟩, hEq.deriv_eq,
    positiveConeBridgeSlope_ratio]
  norm_num

theorem exists_positiveSeedBridge :
    Nonempty (SeedSlopeCutoff positiveConeBridgeSlope (-2) 2 0 0) :=
  exists_seedSlopeCutoff positiveConeBridgeSlope_contDiff positiveConeBridgeSlope_below_four
    (by norm_num) (by norm_num) positiveConeBridgeSlope_C1_left
    positiveConeBridgeSlope_C1_right 0 0

theorem SeedSlopeCutoff.positive_bridge_profile_deriv
    (B : SeedSlopeCutoff positiveConeBridgeSlope (-2) 2 0 0)
    (y₀ f₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < deriv (connectorProfile B.slope y₀ f₀) r := by
  rw [(hasDerivAt_connectorProfile B.smooth B.below_four y₀ f₀ hr).deriv]
  apply mul_pos (exp_pos _)
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) (B.positive_bridge (log r))

end ContinuousFlexibility.Radial
