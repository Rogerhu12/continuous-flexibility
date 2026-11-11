import ContinuousFlexibility.Statements.RadialTargets
import ContinuousFlexibility.Radial.SeedRadialContinuation
import ContinuousFlexibility.Radial.MorseJoinActualGerms
import ContinuousFlexibility.Radial.RadialTailSmoothExtension

/-! # A natural second-mode tail has a nonzero entrance Cauchy state -/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem radialNaturalTail_entry_state_ne_zero {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (hD : RadialProfileGeometry D)
    (hentry : entry ∈ radialCore D) (hu : RadialNaturalTail D right 2 entry u) :
    (u entry, deriv u entry) ≠ (0, 0) := by
  intro hz
  have hu₀ : u entry = 0 := congrArg Prod.fst hz
  have hu₁ : deriv u entry = 0 := congrArg Prod.snd hz
  obtain ⟨x, hx, hux⟩ := hu.2.2.2
  have hentryODE := radialNaturalTail_entry_radialJacobi hD hentry hu
  obtain ⟨ha, hab, hwFlat, hphiFlat, hwpos, hphine, hwcrit⟩ := hD
  have hepos : 0 < entry := ha.trans hentry.1
  have hxcore : x ∈ radialCore D := by
    cases right with
    | false => exact ⟨hx.1, hx.2.trans hentry.2⟩
    | true => exact ⟨hentry.1.trans hx.1, hx.2⟩
  have hxpos : 0 < x := ha.trans hxcore.1
  let a := min entry x
  let b := max entry x
  have haCore : a ∈ radialCore D := by
    rcases le_total entry x with he | he
    · simpa only [a, min_eq_left he] using hentry
    · simpa only [a, min_eq_right he] using hxcore
  have hbCore : b ∈ radialCore D := by
    rcases le_total entry x with he | he
    · simpa only [b, max_eq_right he] using hxcore
    · simpa only [b, max_eq_left he] using hentry
  have hap : 0 < a := ha.trans haCore.1
  have hbp : 0 < b := ha.trans hbCore.1
  have hab' : a ≤ b := (min_le_left entry x).trans (le_max_left entry x)
  have hmap : MapsTo exp (Ioo (log D.a) (log D.b)) (radialCore D) := by
    intro y hy
    exact ⟨by simpa only [exp_log ha] using exp_lt_exp.mpr hy.1,
      by simpa only [exp_log (ha.trans hab)] using exp_lt_exp.mpr hy.2⟩
  have hf : ContDiffOn ℝ ∞ (fun y => log (D.w (exp y))) (Ioo (log D.a) (log D.b)) :=
    (hwFlat.1.comp contDiff_exp).contDiffOn.log (fun y hy => (hwpos _ (hmap hy)).ne')
  obtain ⟨H, hHs, hHcompact, hHg⟩ :=
    exists_contDiff_joinGerm_extension (log_lt_log ha haCore.1)
      (log_le_log hap hab') (log_lt_log hbp hbCore.2) hf
  have hExpMap (y : ℝ) (hy : y ∈ Icc (log a) (log b)) : exp y ∈ Icc a b := by
    exact ⟨by simpa only [exp_log hap] using exp_le_exp.mpr hy.1,
      by simpa only [exp_log hbp] using exp_le_exp.mpr hy.2⟩
  have hspanCore (r : ℝ) (hr : r ∈ Icc a b) : r ∈ radialCore D :=
    ⟨haCore.1.trans_le hr.1, hr.2.trans_lt hbCore.2⟩
  have hspan (r : ℝ) (hr : r ∈ Icc a b) :
      r = entry ∨ r ∈ radialTailInterval D right entry := by
    by_cases he : r = entry
    · exact Or.inl he
    · right
      have hc := hspanCore r hr
      cases right with
      | false =>
          have hb : b = entry := max_eq_left hx.2.le
          have hre : r ≤ entry := by simpa only [hb] using hr.2
          exact ⟨hc.1, lt_of_not_ge (fun h => he (le_antisymm hre h))⟩
      | true =>
          have ha' : a = entry := min_eq_left hx.1.le
          have her : entry ≤ r := by simpa only [ha'] using hr.1
          exact ⟨lt_of_not_ge (fun h => he (le_antisymm h her)), hc.2⟩
  have htailopen : IsOpen (radialTailInterval D right entry) := by
    cases right <;> exact isOpen_Ioo
  have hpoint (r : ℝ) (hr : r ∈ Icc a b) :
      ContDiffAt ℝ ∞ u r ∧ radialJacobi 4 D.w u r = 0 := by
    rcases hspan r hr with he | ht
    · simpa only [he] using And.intro hu.1 hentryODE
    · refine ⟨hu.2.1.1.contDiffAt (htailopen.mem_nhds ht), ?_⟩
      simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hu.2.1.2 r ht
  have hWg (y : ℝ) (hy : y ∈ Icc (log a) (log b)) :
      seedRadialProfile H =ᶠ[𝓝 (exp y)] D.w := by
    have ht : Tendsto log (𝓝 (exp y)) (𝓝 y) := by
      simpa only [log_exp] using (Real.continuousAt_log (exp_pos y).ne').tendsto
    have hp := hwpos (exp y) (hspanCore _ (hExpMap y hy))
    filter_upwards [(hHg y hy).comp_tendsto ht, Ioi_mem_nhds (exp_pos y),
      hwFlat.1.continuous.continuousAt.eventually (Ioi_mem_nhds hp)] with r hH hr hwr
    simp only [Function.comp_apply] at hH
    rw [seedRadialProfile, hH, exp_log hr, exp_log hwr]
  have heI : log entry ∈ Icc (log a) (log b) :=
    ⟨log_le_log hap (min_le_left _ _), log_le_log hepos (le_max_left _ _)⟩
  let Z : ℝ → ℝ := fun _ => 0
  have hZ : ContDiff ℝ ∞ Z := contDiff_const
  have hrep := seedRadial_eqOn_exp hHs heI
    (fun y hy => by
      have hs := (hpoint (exp y) (hExpMap y hy)).1
      have hs' : ContDiffAt ℝ ∞ (deriv u) (exp y) := hs.derivWithin (by simp)
      exact ⟨hs.differentiableAt (by simp), hs'.differentiableAt (by simp)⟩)
    (fun y _ => ⟨hZ.differentiable (by simp) (exp y),
      (contDiff_infty_iff_deriv.mp hZ).2.differentiable (by simp) (exp y)⟩)
    (fun y hy => (radialJacobi_eq_of_profile_germ (hWg y hy)).trans
      (hpoint _ (hExpMap y hy)).2)
    (fun y _ => by simp [Z, radialJacobi])
    (by simpa only [exp_log hepos, Z] using hu₀)
    (by simpa only [exp_log hepos, Z, deriv_const] using hu₁)
  have hxI : log x ∈ Icc (log a) (log b) :=
    ⟨log_le_log hap (min_le_right _ _), log_le_log hxpos (le_max_right _ _)⟩
  apply hux
  simpa only [exp_log hxpos, Z] using (hrep (log x) hxI).1

end ContinuousFlexibility.Radial
