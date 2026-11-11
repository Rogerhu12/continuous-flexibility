import ContinuousFlexibility.Radial.SeedPureTailReplacement
import ContinuousFlexibility.Radial.SeedBridgePair
import ContinuousFlexibility.Radial.SeedThreePiece

/-!
# Orienting the pure inward mode of a natural tail

The positive bridge changes an exceptional pure cone mode to the mode
needed by the central reference pair.  The complete original outward tail
is retained, including its endpoint jets and its signed normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Insert a dilated positive bridge whose outward pure cone agrees
exactly with the original inward cone. -/
theorem SeedPureTail.bridge_to_opposite_retaining {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (T : SeedPureTail D right entry u)
    (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D)
    (B : SeedBridgePair) {R splice : ℝ} (hR : 0 < R)
    (hmode : T.mode = (if right then (2 : ℝ) else -2))
    (hregion : if right then R * B.right < splice ∧ splice < T.cut
      else T.cut < splice ∧ splice < R * B.left) :
    ∃ V : SeedPureTail D right entry u,
      V.mode = (if right then (-2 : ℝ) else 2) ∧
      (if right then V.cut < T.cut else T.cut < V.cut) ∧
      (∀ r, (if right then T.cut ≤ r else r ≤ T.cut) →
        V.profile =ᶠ[𝓝 r] T.profile ∧ V.height =ᶠ[𝓝 r] T.height) ∧
      ∀ r, 0 < r → 0 < deriv T.profile r → 0 < deriv V.profile r := by
  let cOld : ℝ := if right then B.rightScale else B.leftScale
  let aOld : ℝ := if right then B.rightHeight else B.leftHeight
  let cNew : ℝ := if right then B.leftScale else B.rightScale
  let aNew : ℝ := if right then B.leftHeight else B.rightHeight
  let p : ℝ := if right then -2 else 2
  let H : ℝ := T.cone_scale / cOld
  let A : ℝ := T.amplitude * R ^ T.mode / aOld
  let W := seedRescale R (H * R) B.profile
  let U := seedRescale R A B.height
  let cut : ℝ := if right then R * B.left / 2 else 2 * R * B.right
  have hcOld : 0 < cOld := by
    cases right
    · exact B.leftScale_pos
    · exact B.rightScale_pos
  have haOld : 0 < aOld := by
    cases right
    · exact B.leftHeight_pos
    · exact B.rightHeight_pos
  have hcNew : 0 < cNew := by
    cases right
    · exact B.rightScale_pos
    · exact B.leftScale_pos
  have haNew : 0 < aNew := by
    cases right
    · exact B.rightHeight_pos
    · exact B.leftHeight_pos
  have hH : 0 < H := div_pos T.scale_pos hcOld
  have hA : A ≠ 0 := div_ne_zero
    (mul_ne_zero T.amplitude_ne_zero (rpow_pos_of_pos hR T.mode).ne') haOld.ne'
  have hright : 0 < B.right := B.left_pos.trans B.ordered
  have hcoordpos (r : ℝ) (hr : 0 < r) : 0 < R⁻¹ * r :=
    mul_pos (inv_pos.mpr hR) hr
  have hcoord_lt {r x : ℝ} (h : r < R * x) : R⁻¹ * r < x := by
    have hh : r / R < x := (div_lt_iff₀ hR).mpr (by simpa only [mul_comm] using h)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hlt_coord {r x : ℝ} (h : R * x < r) : x < R⁻¹ * r := by
    have hh : x < r / R := (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using h)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have houter (r : ℝ) (hr : 0 < r)
      (hout : if right then R * B.right < r else r < R * B.left) :
      W r = T.cone_scale * r ∧ U r = T.amplitude * r ^ T.mode := by
    cases right
    · obtain ⟨hw, hu⟩ := B.left_eq (R⁻¹ * r) (hcoordpos r hr) (hcoord_lt hout)
      simpa [W, U, H, A, cOld, aOld, hmode] using
        (seedRescale_match_cone (c := T.cone_scale) (a := T.amplitude)
          hR hr B.leftScale_pos.ne' B.leftHeight_pos.ne' hw hu)
    · obtain ⟨hw, hu⟩ := B.right_eq (R⁻¹ * r) (hlt_coord hout)
      simpa [W, U, H, A, cOld, aOld, hmode] using
        (seedRescale_match_cone (c := T.cone_scale) (a := T.amplitude)
          hR hr B.rightScale_pos.ne' B.rightHeight_pos.ne' hw hu)
  have hmatch : ∀ᶠ r in 𝓝 splice, W r = T.profile r ∧ U r = T.height r := by
    cases right
    · filter_upwards [Ioo_mem_nhds hregion.1 hregion.2] with r hr
      have hrpos : 0 < r := T.cut_pos.trans hr.1
      obtain ⟨hw, hu⟩ := houter r hrpos hr.2
      obtain ⟨htw, htu⟩ := T.pure_eq r hrpos hr.1
      exact ⟨hw.trans htw.symm, hu.trans htu.symm⟩
    · filter_upwards [Ioo_mem_nhds hregion.1 hregion.2] with r hr
      have hrpos : 0 < r := (mul_pos hR hright).trans hr.1
      obtain ⟨hw, hu⟩ := houter r hrpos hr.1
      obtain ⟨htw, htu⟩ := T.pure_eq r hrpos hr.2
      exact ⟨hw.trans htw.symm, hu.trans htu.symm⟩
  have hsplice : if right then splice < entry else entry < splice := by
    cases right
    · exact T.cut_order.trans hregion.1
    · exact hregion.2.trans T.cut_order
  have hcut : 0 < cut := by
    cases right
    · change 0 < 2 * R * B.right
      positivity
    · change 0 < R * B.left / 2
      exact div_pos (mul_pos hR B.left_pos) (by norm_num)
  have hcutsplice : if right then cut ≤ splice else splice ≤ cut := by
    have horder := mul_lt_mul_of_pos_left B.ordered hR
    cases right
    · change splice ≤ 2 * R * B.right
      have hs : splice < R * B.left := hregion.2
      nlinarith [mul_pos hR hright]
    · change R * B.left / 2 ≤ splice
      have hs : R * B.right < splice := hregion.1
      nlinarith [mul_pos hR B.left_pos]
  have hpos (r : ℝ) (hr : 0 < r) : 0 < W r :=
    mul_pos (mul_pos hH hR) (B.positive _ (hcoordpos r hr))
  have hderiv (r : ℝ) (hr : 0 < r) : 0 < deriv W r :=
    seedRescale_deriv_pos hR (mul_pos hH hR) (B.increasing _ (hcoordpos r hr))
  have hode (r : ℝ) (hr : 0 < r) : radialJacobi 4 W U r = 0 := by
    have h := radialJacobi_seedRescale (H := H) (A := A) (a := 4)
      (w := B.profile) (u := B.height) hR.ne' (hcoordpos r hr).ne'
    simpa only [mul_inv_cancel_left₀ hR.ne',
      B.homogeneous _ (hcoordpos r hr), mul_zero] using h
  have hp : p ^ 2 = 4 := by
    cases right <;> norm_num [p]
  have hpure (r : ℝ) (hr : 0 < r)
      (hrcut : if right then r < cut else cut < r) :
      W r = (H * cNew) * r ∧ U r = (A * aNew / R ^ p) * r ^ p := by
    cases right
    · have hs : R * B.right < r := by
        change 2 * R * B.right < r at hrcut
        nlinarith [mul_pos hR hright]
      obtain ⟨hw, hu⟩ := B.right_eq (R⁻¹ * r) (hlt_coord hs)
      simpa [W, U, cNew, aNew, p] using
        And.intro (seedRescale_cone (H := H) hR.ne' hw)
          (seedRescale_power (A := A) hR hr hu)
    · have hs : r < R * B.left := by
        change r < R * B.left / 2 at hrcut
        linarith [mul_pos hR B.left_pos]
      obtain ⟨hw, hu⟩ := B.left_eq (R⁻¹ * r) (hcoordpos r hr) (hcoord_lt hs)
      simpa [W, U, cNew, aNew, p] using
        And.intro (seedRescale_cone (H := H) hR.ne' hw)
          (seedRescale_power (A := A) hR hr hu)
  obtain ⟨V, hVm, hVc, hVret, hVpos⟩ := T.replace_inward_retaining hD hentry hsplice hcut hcutsplice
    (contDiffOn_seedRescale hR B.profile_smooth)
    (contDiffOn_seedRescale hR B.height_smooth) hpos hderiv hode
    (hmatch.mono fun _ h => h.1) (hmatch.mono fun _ h => h.2)
    (mul_pos hH hcNew)
    (div_ne_zero (mul_ne_zero hA haNew.ne') (rpow_pos_of_pos hR p).ne') hp hpure
  refine ⟨V, hVm, ?_, ?_, hVpos⟩
  · rw [hVc]
    cases right
    · exact hregion.1.trans_le hcutsplice
    · exact hcutsplice.trans_lt hregion.2
  · intro r hr
    apply hVret r
    cases right
    · exact hr.trans hregion.1.le
    · exact hregion.2.le.trans hr

/-- The original bridge interface. -/
theorem SeedPureTail.bridge_to_opposite {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (T : SeedPureTail D right entry u)
    (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D)
    (B : SeedBridgePair) {R splice : ℝ} (hR : 0 < R)
    (hmode : T.mode = (if right then (2 : ℝ) else -2))
    (hregion : if right then R * B.right < splice ∧ splice < T.cut
      else T.cut < splice ∧ splice < R * B.left) :
    ∃ V : SeedPureTail D right entry u,
      V.mode = (if right then (-2 : ℝ) else 2) := by
  obtain ⟨V, hm, _, _, _⟩ := T.bridge_to_opposite_retaining hD hentry B hR hmode hregion
  exact ⟨V, hm⟩

/-- Every pure tail can be continued farther inward with the canonical
mode: +2 on the left, -2 on the right. -/
theorem SeedPureTail.toCanonical_retaining {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (T : SeedPureTail D right entry u)
    (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D) :
    ∃ V : SeedPureTail D right entry u,
      V.mode = (if right then (-2 : ℝ) else 2) ∧
      (if right then V.cut ≤ T.cut else T.cut ≤ V.cut) ∧
      (∀ r, (if right then T.cut ≤ r else r ≤ T.cut) →
        V.profile =ᶠ[𝓝 r] T.profile ∧ V.height =ᶠ[𝓝 r] T.height) ∧
      ∀ r, 0 < r → 0 < deriv T.profile r → 0 < deriv V.profile r := by
  by_cases hm : T.mode = (if right then (-2 : ℝ) else 2)
  · refine ⟨T, hm, ?_, fun _ _ => ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩,
      fun _ _ hd => hd⟩
    cases right <;> exact le_rfl
  have hmode : T.mode = (if right then (2 : ℝ) else -2) := by
    have hz : (T.mode - 2) * (T.mode + 2) = 0 := by nlinarith [T.mode_sq]
    rcases mul_eq_zero.mp hz with hz | hz
    · have hp : T.mode = 2 := by linarith
      cases right
      · exact False.elim (hm hp)
      · exact hp
    · have hp : T.mode = -2 := by linarith
      cases right
      · exact hp
      · exact False.elim (hm hp)
  obtain ⟨B⟩ := exists_seedBridgePair
  cases right
  · have hR : 0 < 4 * T.cut / B.left :=
      div_pos (mul_pos (by norm_num) T.cut_pos) B.left_pos
    have heq : (4 * T.cut / B.left) * B.left = 4 * T.cut := by
      field_simp [B.left_pos.ne']
    have hregion : T.cut < 2 * T.cut ∧ 2 * T.cut < (4 * T.cut / B.left) * B.left := by
      rw [heq]
      constructor <;> linarith [T.cut_pos]
    obtain ⟨V, hm, hc, hr, hd⟩ :=
      T.bridge_to_opposite_retaining hD hentry B (splice := 2 * T.cut) hR hmode hregion
    exact ⟨V, hm, hc.le, hr, hd⟩
  · have hright : 0 < B.right := B.left_pos.trans B.ordered
    have hR : 0 < T.cut / (4 * B.right) :=
      div_pos T.cut_pos (mul_pos (by norm_num) hright)
    have heq : (T.cut / (4 * B.right)) * B.right = T.cut / 4 := by
      field_simp [hright.ne']
      <;> ring
    have hregion : (T.cut / (4 * B.right)) * B.right < T.cut / 2 ∧ T.cut / 2 < T.cut := by
      rw [heq]
      constructor <;> linarith [T.cut_pos]
    obtain ⟨V, hm, hc, hr, hd⟩ :=
      T.bridge_to_opposite_retaining hD hentry B (splice := T.cut / 2) hR hmode hregion
    exact ⟨V, hm, hc.le, hr, hd⟩

/-- The original canonical-mode interface. -/
theorem SeedPureTail.toCanonical {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (T : SeedPureTail D right entry u)
    (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D) :
    ∃ V : SeedPureTail D right entry u,
      V.mode = (if right then (-2 : ℝ) else 2) := by
  obtain ⟨V, hm, _, _, _⟩ := T.toCanonical_retaining hD hentry
  exact ⟨V, hm⟩

end ContinuousFlexibility.Radial
