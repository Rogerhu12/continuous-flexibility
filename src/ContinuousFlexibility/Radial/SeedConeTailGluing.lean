import ContinuousFlexibility.Radial.SeedConeTail
import ContinuousFlexibility.Radial.SeedConeProfileExtension
import ContinuousFlexibility.Radial.SeedGlobalRadialContinuation
import ContinuousFlexibility.Radial.SeedOutwardMatching
import ContinuousFlexibility.Radial.SeedOrientedGluing

/-!
# Gluing a smooth natural tail to its inward cone continuation

This construction depends only on the ordinary smooth tail and its Cauchy
data. The Morse endpoint machinery is used separately to supply those inputs.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem exists_seedConeTail_of_logExtension {D : ReferenceData} {right : Bool} {entry : ℝ}
    {u V : ℝ → ℝ} (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D)
    (E : SeedPositiveLogExtension (fun y => log (D.w (exp y))) (log entry))
    (hV : ContDiff ℝ ∞ V)
    (hVtail : ∀ r ∈ radialTailInterval D right entry, V r = u r)
    (hVzero : ∀ r, (if right then D.b ≤ r else r ≤ D.a) → V r = 0)
    (hODE : radialJacobi 4 D.w V entry = 0 ∧
      ∀ r ∈ radialTailInterval D right entry, radialJacobi 4 D.w V r = 0)
    (hne : (V entry, deriv V entry) ≠ (0, 0)) :
    ∃ T : SeedConeTail D right entry u,
      ∀ r, (if right then r ≤ entry else entry ≤ r) →
        T.profile =ᶠ[𝓝 r] E.radialProfile := by
  have hGeometry : RadialProfileGeometry D := hD
  obtain ⟨ha, hab, hwFlat, hphiFlat, hwpos, hphine, hwcrit⟩ := hD
  have hepos : 0 < entry := ha.trans hentry.1
  have hdata : (V entry, entry * deriv V entry) ≠ (0, 0) := by
    intro hz
    apply hne
    have h₁ : V entry = 0 := congrArg Prod.fst hz
    have h₂ : deriv V entry = 0 :=
      (mul_eq_zero.mp (congrArg Prod.snd hz)).resolve_left hepos.ne'
    exact Prod.ext h₁ h₂
  obtain ⟨S⟩ := exists_seedGlobalLogContinuation E (V entry) (entry * deriv V entry) hdata
  let U := seedRadialHeight S.height
  have hUs : ContDiffOn ℝ ∞ U (Ioi 0) := seedRadialHeight_contDiffOn S.smooth
  have hU₀ : U entry = V entry := by
    simpa only [exp_log hepos] using S.radial_value
  have hU₁ : deriv U entry = deriv V entry := by
    have hd := S.radial_deriv_value
    rw [exp_log hepos] at hd
    change deriv (seedRadialHeight S.height) entry = deriv V entry
    rw [hd]
    field_simp [hepos.ne']
  have hUg (r : ℝ) (hr : 0 < r) :
      radialJacobi 4 E.radialProfile U r = 0 := S.radial_equation E.smooth hr
  have hWg : E.radialProfile =ᶠ[𝓝 entry] D.w :=
    E.radialProfile_germ hepos hwFlat.1.continuous.continuousAt (hwpos entry hentry)
  obtain ⟨c, hc, hWc, hUc, hcollar⟩ :=
    exists_seedOutwardMatchingCut hGeometry hentry E.smooth hUs hV hUg hODE hWg hU₀ hU₁
  let W := seedOrientedGlue right c E.radialProfile D.w
  let P := seedOrientedGlue right c U V
  have hWi (r : ℝ) (hr : if right then r ≤ c else c ≤ r) :
      W =ᶠ[𝓝 r] E.radialProfile := seedOrientedGlue_inward_germ hWc hr
  have hWo (r : ℝ) (hr : if right then c ≤ r else r ≤ c) :
      W =ᶠ[𝓝 r] D.w := seedOrientedGlue_outward_germ hWc hr
  have hPi (r : ℝ) (hr : if right then r ≤ c else c ≤ r) :
      P =ᶠ[𝓝 r] U := seedOrientedGlue_inward_germ hUc hr
  have hPo (r : ℝ) (hr : if right then c ≤ r else r ≤ c) :
      P =ᶠ[𝓝 r] V := seedOrientedGlue_outward_germ hUc hr
  have hdompos (r : ℝ) (hr : r ∈ seedConeTailDomain D right) : 0 < r := by
    cases right with
    | false => exact ha.trans hr
    | true => exact hr.1
  have htailcore (r : ℝ) (hr : r ∈ radialTailInterval D right entry) :
      r ∈ radialCore D := by
    cases right with
    | false => exact ⟨hr.1, hr.2.trans hentry.2⟩
    | true => exact ⟨hentry.1.trans hr.1, hr.2⟩
  have houttail (r : ℝ) (hr : r ∈ seedConeTailDomain D right)
      (ho : if right then c ≤ r else r ≤ c) :
      r ∈ radialTailInterval D right entry := by
    cases right with
    | false => exact ⟨hr, ho.trans_lt hc.2⟩
    | true => exact ⟨hc.1.trans_le ho, hr.2⟩
  obtain ⟨cL, cR, hcL, hcR, hconeL, hconeR⟩ := E.radialProfile_cones
  let cut := if right then exp (E.left - 1) else exp (E.right + 1)
  have hcutpos : 0 < cut := by cases right <;> exact exp_pos _
  have hcutorder : if right then cut < entry else entry < cut := by
    cases right with
    | false =>
        change entry < exp (E.right + 1)
        have h := exp_lt_exp.mpr (show log entry < E.right + 1 by linarith only [E.right_gt])
        simpa only [exp_log hepos] using h
    | true =>
        change exp (E.left - 1) < entry
        have h := exp_lt_exp.mpr (show E.left - 1 < log entry by linarith only [E.left_lt])
        simpa only [exp_log hepos] using h
  have hconeinner (r : ℝ) (hr : if right then r < cut else cut < r) :
      if right then r ≤ c else c ≤ r := by
    cases right with
    | false => exact (hc.2.trans (hcutorder.trans hr)).le
    | true => exact (hr.trans (hcutorder.trans hc.1)).le
  refine ⟨{
    profile := W
    height := P
    profile_smooth := contDiffOn_seedOrientedGlue E.radialProfile_smooth hwFlat.1.contDiffOn hWc
    height_smooth := contDiffOn_seedOrientedGlue hUs hV.contDiffOn hUc
    outward_zero := ?_
    tail_eq := ?_
    positive := ?_
    simple_critical := ?_
    homogeneous := ?_
    cut := cut
    cut_pos := hcutpos
    cut_order := hcutorder
    cone_scale := if right then cL else cR
    coneA := if right then S.leftA else S.rightA
    coneB := if right then S.leftB else S.rightB
    scale_pos := by cases right <;> assumption
    coeff_ne_zero := by cases right <;> first | exact S.right_ne | exact S.left_ne
    cone_eq := ?_
  }, ?_⟩
  · intro r hr
    have ho : if right then c ≤ r else r ≤ c := by
      cases right with
      | false => exact hr.trans hc.1.le
      | true => exact hc.2.le.trans hr
    rw [(hWo r ho).eq_of_nhds, (hPo r ho).eq_of_nhds]
    refine ⟨hwFlat.2 r ?_, hVzero r hr⟩
    cases right with
    | false => exact Or.inl hr
    | true => exact Or.inr hr
  · intro r hr
    rcases seedOrientedGlue_sides right c r with hi | ho
    · have hm := hcollar r hr hi
      exact ⟨(hWi r hi).eq_of_nhds.trans hm.1,
        (hPi r hi).eq_of_nhds.trans (hm.2.trans (hVtail r hr))⟩
    · exact ⟨(hWo r ho).eq_of_nhds, (hPo r ho).eq_of_nhds.trans (hVtail r hr)⟩
  · intro r hr
    rcases seedOrientedGlue_sides right c r with hi | ho
    · rw [(hWi r hi).eq_of_nhds]
      exact E.radialProfile_pos r
    · rw [(hWo r ho).eq_of_nhds]
      exact hwpos r (htailcore r (houttail r hr ho))
  · intro r hr hz
    rcases seedOrientedGlue_sides right c r with hi | ho
    · have hp := E.radialProfile_deriv_pos (hdompos r hr)
      rw [← (hWi r hi).deriv_eq, hz] at hp
      exact (lt_irrefl 0 hp).elim
    · rw [(hWo r ho).deriv_eq] at hz
      rw [(hWo r ho).deriv.deriv_eq]
      exact hwcrit r (htailcore r (houttail r hr ho)) hz
  · intro r hr
    rcases seedOrientedGlue_sides right c r with hi | ho
    · exact (radialJacobi_eq_of_germs (hWi r hi) (hPi r hi)).trans (hUg r (hdompos r hr))
    · exact (radialJacobi_eq_of_germs (hWo r ho) (hPo r ho)).trans
        (hODE.2 r (houttail r hr ho))
  · intro r hr hcut
    have hi := hconeinner r hcut
    rw [(hWi r hi).eq_of_nhds, (hPi r hi).eq_of_nhds]
    cases right with
    | false =>
        change exp (E.right + 1) < r at hcut
        have hy : E.right + 1 < log r := by
          simpa only [Real.log_exp] using log_lt_log (exp_pos (E.right + 1)) hcut
        exact ⟨hconeR r hr (by linarith only [hy]),
          S.radial_right_modes hr hy.le⟩
    | true =>
        change r < exp (E.left - 1) at hcut
        have hy : log r < E.left - 1 := by
          simpa only [Real.log_exp] using log_lt_log hr hcut
        exact ⟨hconeL r hr (by linarith only [hy]),
          S.radial_left_modes hr hy.le⟩
  · intro r hr
    apply hWi r
    cases right
    · exact hc.2.le.trans hr
    · exact hr.trans hc.1.le

/-- The original interface chooses a positive logarithmic extension from
the entry germ. The stronger constructor permits a prescribed extension. -/
theorem exists_seedConeTail_of_smoothNatural {D : ReferenceData} {right : Bool} {entry : ℝ}
    {u V : ℝ → ℝ} (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D)
    (hder : 0 < deriv D.w entry) (hV : ContDiff ℝ ∞ V)
    (hVtail : ∀ r ∈ radialTailInterval D right entry, V r = u r)
    (hVzero : ∀ r, (if right then D.b ≤ r else r ≤ D.a) → V r = 0)
    (hODE : radialJacobi 4 D.w V entry = 0 ∧
      ∀ r ∈ radialTailInterval D right entry, radialJacobi 4 D.w V r = 0)
    (hne : (V entry, deriv V entry) ≠ (0, 0)) :
    Nonempty (SeedConeTail D right entry u) := by
  have hGeometry : RadialProfileGeometry D := hD
  obtain ⟨ha, _, hwFlat, _, hwpos, _, _⟩ := hD
  obtain ⟨E⟩ := exists_seedConeProfileExtension ha hentry hwFlat.1 hwpos hder
  obtain ⟨T, _⟩ := exists_seedConeTail_of_logExtension hGeometry hentry E hV hVtail hVzero hODE hne
  exact ⟨T⟩

end ContinuousFlexibility.Radial
