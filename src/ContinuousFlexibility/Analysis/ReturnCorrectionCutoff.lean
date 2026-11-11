import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith

/-!
# An actual interpolation cutoff for each negative component

The cutoff is smooth, takes values in `[0,1]`, is zero near the left
endpoint, and is one near the right endpoint. Its derivative is supported
in the closed middle third. These qualitative facts suffice for the exact
corrected-flow construction. The manuscript's uniform weighted estimates
require a quantitatively chosen root collar in addition to these facts.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A fixed smooth transition within the middle third of `(l,h)`. -/
def returnCorrectionCutoff (l h r : ℝ) : ℝ :=
  Real.smoothTransition ((3 * r - (2 * l + h)) / (h - l))

theorem returnCorrectionCutoff_apply (l h r : ℝ) :
    returnCorrectionCutoff l h r =
      Real.smoothTransition ((3 * r - (2 * l + h)) / (h - l)) := rfl

theorem returnCorrectionCutoff_contDiff (l h : ℝ) :
    ContDiff ℝ ∞ (returnCorrectionCutoff l h) :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const).div_const (h - l))

theorem returnCorrectionCutoff_mem_Icc (l h r : ℝ) :
    returnCorrectionCutoff l h r ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem returnCorrectionCutoff_zero_of_le {l h r : ℝ} (hlh : l < h)
    (hr : r ≤ (2 * l + h) / 3) : returnCorrectionCutoff l h r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hlh.le)

theorem returnCorrectionCutoff_one_of_ge {l h r : ℝ} (hlh : l < h)
    (hr : (l + 2 * h) / 3 ≤ r) : returnCorrectionCutoff l h r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (sub_pos.mpr hlh)).mpr
  linarith

theorem returnCorrectionCutoff_eventually_zero {l h r : ℝ} (hlh : l < h)
    (hr : r < (2 * l + h) / 3) :
    returnCorrectionCutoff l h =ᶠ[𝓝 r] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds hr] with s hs
  exact returnCorrectionCutoff_zero_of_le hlh hs.le

theorem returnCorrectionCutoff_eventually_one {l h r : ℝ} (hlh : l < h)
    (hr : (l + 2 * h) / 3 < r) :
    returnCorrectionCutoff l h =ᶠ[𝓝 r] fun _ => 1 := by
  filter_upwards [Ioi_mem_nhds hr] with s hs
  exact returnCorrectionCutoff_one_of_ge hlh hs.le

theorem returnCorrectionCutoff_eventually_zero_left {l h : ℝ} (hlh : l < h) :
    returnCorrectionCutoff l h =ᶠ[𝓝 l] fun _ => 0 :=
  returnCorrectionCutoff_eventually_zero hlh (by linarith)

theorem returnCorrectionCutoff_eventually_one_right {l h : ℝ} (hlh : l < h) :
    returnCorrectionCutoff l h =ᶠ[𝓝 h] fun _ => 1 :=
  returnCorrectionCutoff_eventually_one hlh (by linarith)

theorem returnCorrectionCutoff_left {l h : ℝ} (hlh : l < h) :
    returnCorrectionCutoff l h l = 0 :=
  (returnCorrectionCutoff_eventually_zero_left hlh).eq_of_nhds

theorem returnCorrectionCutoff_right {l h : ℝ} (hlh : l < h) :
    returnCorrectionCutoff l h h = 1 :=
  (returnCorrectionCutoff_eventually_one_right hlh).eq_of_nhds

theorem returnCorrectionCutoff_deriv_zero_of_lt {l h r : ℝ} (hlh : l < h)
    (hr : r < (2 * l + h) / 3) : deriv (returnCorrectionCutoff l h) r = 0 := by
  rw [(returnCorrectionCutoff_eventually_zero hlh hr).deriv_eq, deriv_const]

theorem returnCorrectionCutoff_deriv_zero_of_gt {l h r : ℝ} (hlh : l < h)
    (hr : (l + 2 * h) / 3 < r) : deriv (returnCorrectionCutoff l h) r = 0 := by
  rw [(returnCorrectionCutoff_eventually_one hlh hr).deriv_eq, deriv_const]

theorem returnCorrectionCutoff_deriv_support_subset {l h : ℝ} (hlh : l < h) :
    Function.support (deriv (returnCorrectionCutoff l h)) ⊆
      Icc ((2 * l + h) / 3) ((l + 2 * h) / 3) := by
  intro r hr
  constructor
  · by_contra h
    exact hr (returnCorrectionCutoff_deriv_zero_of_lt hlh (lt_of_not_ge h))
  · by_contra h
    exact hr (returnCorrectionCutoff_deriv_zero_of_gt hlh (lt_of_not_ge h))

theorem returnCorrectionCutoff_deriv_support_subset_component {l h : ℝ} (hlh : l < h) :
    Function.support (deriv (returnCorrectionCutoff l h)) ⊆ Ioo l h := by
  intro r hr
  have hmid := returnCorrectionCutoff_deriv_support_subset hlh hr
  constructor <;> linarith [hmid.1, hmid.2]

theorem returnCorrectionCutoff_deriv_eventually_zero_left {l h : ℝ} (hlh : l < h) :
    deriv (returnCorrectionCutoff l h) =ᶠ[𝓝 l] fun _ => 0 := by
  simpa only [deriv_const'] using (returnCorrectionCutoff_eventually_zero_left hlh).deriv

theorem returnCorrectionCutoff_deriv_eventually_zero_right {l h : ℝ} (hlh : l < h) :
    deriv (returnCorrectionCutoff l h) =ᶠ[𝓝 h] fun _ => 0 := by
  simpa only [deriv_const'] using (returnCorrectionCutoff_eventually_one_right hlh).deriv

end ContinuousFlexibility.Analysis
