module

public import ContinuousFlexibility.Radial.TerminalPhysicalCutoff
public import ContinuousFlexibility.Radial.TerminalMorseLongGeometry

/-!
# Physical cutoff layers in the same normalized Morse cell

The endpoints are actual radius values at one quarter and one half of
the corresponding cap. The existing positive velocity proves their
order, a lower width bound, and surjectivity of the model layer onto the
physical layer. One Boolean handles the short decreasing cutoff and the
long increasing cutoff.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

def terminalMorseLayerOrigin (long : Bool) (A B : ℝ) : ℝ :=
  if long then morseRightTurn A B else morseCellLeftCut

def terminalMorseLayerLength (long : Bool) (A : ℝ) : ℝ :=
  if long then morseRightCapLength A (1 / 100) else morseShortLeftCapLength

def terminalMorseLayerRadius (long : Bool) (A B s : ℝ) (r : ℝ → ℝ) : ℝ → ℝ :=
  terminalMorseCapRadius s (terminalMorseLayerOrigin long A B) 1 r

def terminalMorseLayerLeft (long : Bool) (A B s : ℝ) (r : ℝ → ℝ) : ℝ :=
  terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A / 4)

def terminalMorseLayerRight (long : Bool) (A B s : ℝ) (r : ℝ → ℝ) : ℝ :=
  terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A / 2)

def terminalMorsePhysicalCutoff (long : Bool) (A B s : ℝ) (r : ℝ → ℝ) : ℝ → ℝ :=
  terminalPhysicalCutoff long (terminalMorseLayerLeft long A B s r)
    (terminalMorseLayerRight long A B s r)

theorem terminalMorseLayerLength_pos (long : Bool) {A : ℝ} (hA : 0 < A) :
    0 < terminalMorseLayerLength long A := by
  cases long
  · exact morseShortLeftCapLength_pos
  · exact morseRightCapLength_pos hA (by norm_num)

theorem terminalMorseLayerRadius_smooth (long : Bool) (A B s : ℝ) {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) : ContDiff ℝ ∞ (terminalMorseLayerRadius long A B s r) :=
  terminalMorseCapRadius_smooth _ _ _ hr

theorem terminalMorseLayer_point_mem (long : Bool) {A B t : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A)
    (ht : t ∈ Icc 0 (terminalMorseLayerLength long A)) :
    terminalMorseLayerOrigin long A B + t ∈
      Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hend : morseRightTurn A B ≤ morseRightCapEnd A B (1 / 100) :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  cases long
  · change t ∈ Icc 0 morseShortLeftCapLength at ht
    change morseCellLeftCut + t ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100))
    have hshort : morseShortLeftCapCut < morseRightTurn A B :=
      (morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)
    dsimp only [morseShortLeftCapLength] at ht
    constructor <;> linarith only [ht.1, ht.2, hshort, hend]
  · change t ∈ Icc 0 (morseRightCapLength A (1 / 100)) at ht
    change morseRightTurn A B + t ∈
      Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100))
    have hleft := morseCellLeftCut_lt_rightTurn hB hAB
    constructor
    · linarith only [ht.1, hleft]
    · dsimp only [morseRightCapEnd]
      linarith only [ht.2]

theorem terminalMorse_retained_radius_bounds {A B x : ℝ} {r : ℝ → ℝ}
    (hr : IsNormalizedMorseCell A B r)
    (hx : x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100))) :
    0 < r x ∧ r x ≤ 2 := by
  by_cases ht : x ≤ morseRightTurn A B
  · have h := hr.left_half x ⟨hx.1, ht⟩
    exact ⟨h.2.1, h.2.2.1⟩
  · have h := hr.right_half x ⟨le_of_not_ge ht, hx.2⟩
    exact ⟨h.2.1, h.2.2.1⟩

theorem terminalMorseLayerRadius_pos (long : Bool) {A B s t : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hr : IsNormalizedMorseCell A B r)
    (ht : t ∈ Icc 0 (terminalMorseLayerLength long A)) :
    0 < terminalMorseLayerRadius long A B s r t := by
  have hp := (terminalMorse_retained_radius_bounds hr
    (terminalMorseLayer_point_mem long hB hAB ht)).1
  simpa only [terminalMorseLayerRadius, terminalMorseCapRadius, one_mul] using mul_pos hs hp

theorem terminalMorseLayerLeft_pos (long : Bool) {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r) :
    0 < terminalMorseLayerLeft long A B s r := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL := terminalMorseLayerLength_pos long hA
  exact terminalMorseLayerRadius_pos long hB hAB hs hr
    ⟨by linarith only [hL], by linarith only [hL]⟩

/-- The same actual normalized cell controls the physical speed on
every retained point, including either cutoff layer. -/
theorem terminalMorse_retained_speed_lower {A B x : ℝ} {r : ℝ → ℝ}
    (hr : IsNormalizedMorseCell A B r)
    (hx : x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100))) :
    A ^ 5 / 100 ≤ deriv r x := by
  by_cases ht : x ≤ morseRightTurn A B
  · have h := (hr.left_half x ⟨hx.1, ht⟩).2.2.2.1
    linarith only [h]
  · have h := (hr.right_half x ⟨le_of_not_ge ht, hx.2⟩).2.2.2.1
    linarith only [h]

theorem terminalMorseLayerRadius_speed_lower (long : Bool) {A B s t : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hr : IsNormalizedMorseCell A B r)
    (ht : t ∈ Icc 0 (terminalMorseLayerLength long A)) :
    s * A ^ 5 / 100 ≤ deriv (terminalMorseLayerRadius long A B s r) t := by
  have h := mul_le_mul_of_nonneg_left
    (terminalMorse_retained_speed_lower hr (terminalMorseLayer_point_mem long hB hAB ht)) hs.le
  change s * A ^ 5 / 100 ≤ deriv (terminalMorseCapRadius s
    (terminalMorseLayerOrigin long A B) 1 r) t
  rw [terminalMorseCapRadius_deriv _ _ _ _ hr.smooth]
  simpa only [one_mul, mul_one, mul_div_assoc] using h

theorem terminalMorseLayerRadius_strictMono (long : Bool) {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hr : IsNormalizedMorseCell A B r) :
    StrictMonoOn (terminalMorseLayerRadius long A B s r)
      (Icc 0 (terminalMorseLayerLength long A)) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  apply morseCell_strictMonoOn (terminalMorseLayerRadius_smooth long A B s hr.smooth)
  intro t ht
  exact (by positivity : 0 < s * A ^ 5 / 100).trans_le
    (terminalMorseLayerRadius_speed_lower long hB hAB hs hr ht)

/-- The physical transition width is bounded below by the model
length times a genuine lower bound on the physical speed. -/
theorem terminalMorseLayer_width_lower (long : Bool) {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hr : IsNormalizedMorseCell A B r) :
    s * A ^ 5 * terminalMorseLayerLength long A / 400 ≤
      terminalMorseLayerRight long A B s r - terminalMorseLayerLeft long A B s r := by
  let L := terminalMorseLayerLength long A
  let R := terminalMorseLayerRadius long A B s r
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 < L := terminalMorseLayerLength_pos long hA
  have hR : ContDiff ℝ ∞ R := terminalMorseLayerRadius_smooth long A B s hr.smooth
  have hquarter : L / 4 ∈ Icc 0 L := ⟨by linarith only [hL], by linarith only [hL]⟩
  have hhalf : L / 2 ∈ Icc 0 L := ⟨by linarith only [hL], by linarith only [hL]⟩
  have hbound := (convex_Icc (0 : ℝ) L).mul_sub_le_image_sub_of_le_deriv
    hR.continuous.continuousOn (hR.differentiable (by simp)).differentiableOn
    (fun t ht => terminalMorseLayerRadius_speed_lower long hB hAB hs hr (interior_subset ht))
    (L / 4) hquarter (L / 2) hhalf (by linarith only [hL])
  change s * A ^ 5 * L / 400 ≤ R (L / 2) - R (L / 4)
  convert hbound using 1 <;> ring

theorem terminalMorseLayer_order (long : Bool) {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hr : IsNormalizedMorseCell A B r) :
    terminalMorseLayerLeft long A B s r < terminalMorseLayerRight long A B s r := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL := terminalMorseLayerLength_pos long hA
  have hbound := terminalMorseLayer_width_lower long hB hAB hs hr
  exact sub_pos.mp ((by positivity : 0 < s * A ^ 5 * terminalMorseLayerLength long A / 400).trans_le hbound)

/-- Every point of the physical layer comes from the same model layer,
so its physical height is controlled by the already proved attenuation. -/
theorem terminalMorseLayer_preimage (long : Bool) {A B s z : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hr : IsNormalizedMorseCell A B r)
    (hz : z ∈ Icc (terminalMorseLayerLeft long A B s r) (terminalMorseLayerRight long A B s r)) :
    ∃ t ∈ Icc (terminalMorseLayerLength long A / 4) (terminalMorseLayerLength long A / 2),
      terminalMorseLayerRadius long A B s r t = z := by
  let L := terminalMorseLayerLength long A
  let R := terminalMorseLayerRadius long A B s r
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 < L := terminalMorseLayerLength_pos long hA
  have hsub : Icc (L / 4) (L / 2) ⊆ Icc 0 L :=
    Icc_subset_Icc (by linarith only [hL]) (by linarith only [hL])
  have hm : MonotoneOn R (Icc (L / 4) (L / 2)) :=
    (terminalMorseLayerRadius_strictMono long hB hAB hs hr).monotoneOn.mono hsub
  have hc : ContinuousOn R (Icc (L / 4) (L / 2)) :=
    (terminalMorseLayerRadius_smooth long A B s hr.smooth).continuous.continuousOn
  have him := hc.image_Icc_of_monotoneOn (by linarith only [hL] : L / 4 ≤ L / 2) hm
  have hmem : z ∈ R '' Icc (L / 4) (L / 2) := by
    rw [him]
    exact hz
  exact hmem

theorem terminalMorsePhysicalCutoff_smooth (long : Bool) (A B s : ℝ) (r : ℝ → ℝ) :
    ContDiff ℝ ∞ (terminalMorsePhysicalCutoff long A B s r) :=
  terminalPhysicalCutoff_smooth _ _ _

theorem terminalMorsePhysicalCutoff_tsupport_deriv (long : Bool) {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r) :
    tsupport (deriv (terminalMorsePhysicalCutoff long A B s r)) ⊆
      Icc (terminalMorseLayerLeft long A B s r) (terminalMorseLayerRight long A B s r) :=
  terminalPhysicalCutoff_tsupport_deriv long (terminalMorseLayer_order long hB hAB hs hr)

/-- At the normalized end this very cutoff is identically one on a
neighborhood, so the physical normalized trace and flux are unchanged. -/
theorem terminalMorsePhysicalCutoff_join_germ (long : Bool) {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r) :
    let R := terminalMorseLayerRadius long A B s r
    let L := terminalMorseLayerLength long A
    terminalMorsePhysicalCutoff long A B s r =ᶠ[𝓝 (if long then R L else R 0)] fun _ => 1 := by
  dsimp only
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  let L := terminalMorseLayerLength long A
  let R := terminalMorseLayerRadius long A B s r
  have hL : 0 < L := terminalMorseLayerLength_pos long hA
  have hm := terminalMorseLayerRadius_strictMono long hB hAB hs hr
  have hleft : R 0 < terminalMorseLayerLeft long A B s r :=
    hm ⟨le_rfl, hL.le⟩ ⟨by linarith only [hL], by linarith only [hL]⟩
      (by linarith only [hL])
  have hright : terminalMorseLayerRight long A B s r < R L :=
    hm ⟨by linarith only [hL], by linarith only [hL]⟩ ⟨hL.le, le_rfl⟩
      (by linarith only [hL])
  have hab := terminalMorseLayer_order long hB hAB hs hr
  cases long
  · exact terminalPhysicalCutoff_left_germ false hab hleft
  · exact terminalPhysicalCutoff_right_germ true hab hright

/-- The cut at the opposite end has a zero germ. -/
theorem terminalMorsePhysicalCutoff_wall_germ (long : Bool) {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r) :
    let R := terminalMorseLayerRadius long A B s r
    let L := terminalMorseLayerLength long A
    terminalMorsePhysicalCutoff long A B s r =ᶠ[𝓝 (if long then R 0 else R L)] fun _ => 0 := by
  dsimp only
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  let L := terminalMorseLayerLength long A
  let R := terminalMorseLayerRadius long A B s r
  have hL : 0 < L := terminalMorseLayerLength_pos long hA
  have hm := terminalMorseLayerRadius_strictMono long hB hAB hs hr
  have hleft : R 0 < terminalMorseLayerLeft long A B s r :=
    hm ⟨le_rfl, hL.le⟩ ⟨by linarith only [hL], by linarith only [hL]⟩
      (by linarith only [hL])
  have hright : terminalMorseLayerRight long A B s r < R L :=
    hm ⟨by linarith only [hL], by linarith only [hL]⟩ ⟨hL.le, le_rfl⟩
      (by linarith only [hL])
  have hab := terminalMorseLayer_order long hB hAB hs hr
  cases long
  · exact terminalPhysicalCutoff_right_germ false hab hright
  · exact terminalPhysicalCutoff_left_germ true hab hleft

end ContinuousFlexibility.Radial
