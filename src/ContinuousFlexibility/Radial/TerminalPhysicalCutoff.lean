import ContinuousFlexibility.Radial.MorsePositiveJoin
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# A physical transition on the actual cutoff layer

Both orientations use the existing Morse join weights, with their
parameters chosen so that the transition occupies exactly [a,b].
The cutoff is globally smooth, is constant on either side, and all
derivatives cost only the corresponding inverse power of the physical
width b-a.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

/-- The Boolean chooses which side has value one. -/
def terminalPhysicalCutoff (rising : Bool) (a b : ℝ) : ℝ → ℝ :=
  if rising then morseJoinRightWeight (2 * b - a) (2 * (b - a))
  else morseJoinLeftWeight (2 * a - b) (2 * (b - a))

theorem terminalPhysicalCutoff_smooth (rising : Bool) (a b : ℝ) :
    ContDiff ℝ ∞ (terminalPhysicalCutoff rising a b) := by
  cases rising
  · exact contDiff_morseJoinLeftWeight _ _
  · exact contDiff_morseJoinRightWeight _ _

theorem terminalPhysicalCutoff_range (rising : Bool) (a b x : ℝ) :
    0 ≤ terminalPhysicalCutoff rising a b x ∧ terminalPhysicalCutoff rising a b x ≤ 1 := by
  cases rising <;> exact ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

theorem terminalPhysicalCutoff_left (rising : Bool) {a b x : ℝ}
    (hab : a < b) (hx : x ≤ a) :
    terminalPhysicalCutoff rising a b x = if rising then 0 else 1 := by
  have hh : 0 < 2 * (b - a) := mul_pos (by norm_num) (sub_pos.mpr hab)
  cases rising
  · exact morseJoinLeftWeight_one hh (by linarith only [hx])
  · exact morseJoinRightWeight_zero hh (by linarith only [hx])

theorem terminalPhysicalCutoff_right (rising : Bool) {a b x : ℝ}
    (hab : a < b) (hx : b ≤ x) :
    terminalPhysicalCutoff rising a b x = if rising then 1 else 0 := by
  have hh : 0 < 2 * (b - a) := mul_pos (by norm_num) (sub_pos.mpr hab)
  cases rising
  · exact morseJoinLeftWeight_zero hh (by linarith only [hx])
  · exact morseJoinRightWeight_one hh (by linarith only [hx])

theorem terminalPhysicalCutoff_left_germ (rising : Bool) {a b x : ℝ}
    (hab : a < b) (hx : x < a) :
    terminalPhysicalCutoff rising a b =ᶠ[𝓝 x] fun _ => if rising then 0 else 1 := by
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact terminalPhysicalCutoff_left rising hab hy.le

theorem terminalPhysicalCutoff_right_germ (rising : Bool) {a b x : ℝ}
    (hab : a < b) (hx : b < x) :
    terminalPhysicalCutoff rising a b =ᶠ[𝓝 x] fun _ => if rising then 1 else 0 := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact terminalPhysicalCutoff_right rising hab hy.le

/-- The value support stays on the chosen side of the layer. -/
theorem terminalPhysicalCutoff_support (rising : Bool) {a b : ℝ} (hab : a < b) :
    Function.support (terminalPhysicalCutoff rising a b) ⊆
      if rising then Ioi a else Iio b := by
  cases rising
  · intro x hx
    change x < b
    by_contra h
    have hz := terminalPhysicalCutoff_right false hab (le_of_not_gt h)
    exact hx hz
  · intro x hx
    change a < x
    by_contra h
    have hz := terminalPhysicalCutoff_left true hab (le_of_not_gt h)
    exact hx hz

/-- Both derivative supports lie in the actual physical layer. -/
theorem terminalPhysicalCutoff_tsupport_deriv (rising : Bool) {a b : ℝ} (hab : a < b) :
    tsupport (deriv (terminalPhysicalCutoff rising a b)) ⊆ Icc a b := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  change deriv (terminalPhysicalCutoff rising a b) x ≠ 0 at hx
  constructor
  · by_contra h
    have hg := terminalPhysicalCutoff_left_germ rising hab (lt_of_not_ge h)
    have hz : deriv (terminalPhysicalCutoff rising a b) x = 0 := by
      simpa only [deriv_const] using hg.deriv_eq
    exact hx hz
  · by_contra h
    have hg := terminalPhysicalCutoff_right_germ rising hab (lt_of_not_ge h)
    have hz : deriv (terminalPhysicalCutoff rising a b) x = 0 := by
      simpa only [deriv_const] using hg.deriv_eq
    exact hx hz

theorem terminalPhysicalCutoff_tsupport_second (rising : Bool) {a b : ℝ} (hab : a < b) :
    tsupport (deriv (deriv (terminalPhysicalCutoff rising a b))) ⊆ Icc a b :=
  tsupport_deriv_subset.trans (terminalPhysicalCutoff_tsupport_deriv rising hab)

/-- Constants are inherited from the already constructed smooth
transition, independently of the position, width, and orientation. -/
def terminalPhysicalCutoffJetConstant (k : ℕ) : ℝ :=
  Classical.choose (exists_morseJoinWeight_jet_bound k)

theorem terminalPhysicalCutoffJetConstant_nonneg (k : ℕ) :
    0 ≤ terminalPhysicalCutoffJetConstant k :=
  (Classical.choose_spec (exists_morseJoinWeight_jet_bound k)).1

theorem terminalPhysicalCutoff_jet_bound (k : ℕ) (rising : Bool)
    {a b : ℝ} (hab : a < b) (x : ℝ) :
    |iteratedDeriv k (terminalPhysicalCutoff rising a b) x| ≤
      terminalPhysicalCutoffJetConstant k / (b - a) ^ k := by
  have hh : 0 < 2 * (b - a) := mul_pos (by norm_num) (sub_pos.mpr hab)
  have hb := (Classical.choose_spec (exists_morseJoinWeight_jet_bound k)).2
    (2 * a - b) (2 * b - a) (2 * (b - a)) hh x
  have hscale : (2 : ℝ) / (2 * (b - a)) = (b - a)⁻¹ := by
    field_simp [(sub_pos.mpr hab).ne'] <;> ring
  have he : terminalPhysicalCutoffJetConstant k * (2 / (2 * (b - a))) ^ k =
      terminalPhysicalCutoffJetConstant k / (b - a) ^ k := by
    rw [hscale, inv_pow, div_eq_mul_inv]
  rw [← he]
  cases rising
  · exact hb.1
  · exact hb.2

theorem terminalPhysicalCutoff_deriv_bound (rising : Bool)
    {a b : ℝ} (hab : a < b) (x : ℝ) :
    |deriv (terminalPhysicalCutoff rising a b) x| ≤
      terminalPhysicalCutoffJetConstant 1 / (b - a) := by
  simpa only [iteratedDeriv_one, pow_one] using terminalPhysicalCutoff_jet_bound 1 rising hab x

theorem terminalPhysicalCutoff_second_bound (rising : Bool)
    {a b : ℝ} (hab : a < b) (x : ℝ) :
    |deriv (deriv (terminalPhysicalCutoff rising a b)) x| ≤
      terminalPhysicalCutoffJetConstant 2 / (b - a) ^ 2 := by
  simpa only [iteratedDeriv_succ', iteratedDeriv_one, iteratedDeriv_zero] using
    terminalPhysicalCutoff_jet_bound 2 rising hab x

end ContinuousFlexibility.Radial
