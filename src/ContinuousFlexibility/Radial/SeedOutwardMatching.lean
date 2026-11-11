import ContinuousFlexibility.Radial.SeedRadialContinuation
import ContinuousFlexibility.Radial.SeedPairGluing
import ContinuousFlexibility.Statements.Radial

/-! # Matching a continued solution on a genuine outward collar -/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem exists_seedOutwardMatchingCut {D : ReferenceData} {right : Bool} {entry : ℝ}
    {H U V : ℝ → ℝ} (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D)
    (hH : ContDiff ℝ ∞ H) (hU : ContDiffOn ℝ ∞ U (Ioi 0)) (hV : ContDiff ℝ ∞ V)
    (hnew : ∀ r, 0 < r → radialJacobi 4 (seedRadialProfile H) U r = 0)
    (hold : radialJacobi 4 D.w V entry = 0 ∧
      ∀ r ∈ radialTailInterval D right entry, radialJacobi 4 D.w V r = 0)
    (hW : seedRadialProfile H =ᶠ[𝓝 entry] D.w)
    (h₀ : U entry = V entry) (h₁ : deriv U entry = deriv V entry) :
    ∃ c : ℝ, c ∈ radialTailInterval D right entry ∧
      (seedRadialProfile H =ᶠ[𝓝 c] D.w) ∧ (U =ᶠ[𝓝 c] V) ∧
      ∀ r ∈ radialTailInterval D right entry, (if right then r ≤ c else c ≤ r) →
        seedRadialProfile H r = D.w r ∧ U r = V r := by
  have hepos : 0 < entry := hD.1.trans hentry.1
  have hnb : {r | seedRadialProfile H r = D.w r ∧ r ∈ radialCore D} ∈ 𝓝 entry :=
    hW.and (isOpen_Ioo.mem_nhds hentry)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnb
  rw [Real.ball_eq_Ioo] at hεsub
  let l := entry - ε / 2
  let h := entry + ε / 2
  have hle : l < entry := by dsimp only [l]; linarith
  have heh : entry < h := by dsimp only [h]; linarith
  have hLl : entry - ε < l := by dsimp only [l]; linarith
  have hhR : h < entry + ε := by dsimp only [h]; linarith
  have hclosed (r : ℝ) (hr : r ∈ Icc l h) :
      seedRadialProfile H r = D.w r ∧ r ∈ radialCore D :=
    hεsub ⟨hLl.trans_le hr.1, hr.2.trans_lt hhR⟩
  have hWg (r : ℝ) (hr : r ∈ Icc l h) :
      seedRadialProfile H =ᶠ[𝓝 r] D.w :=
    Filter.eventuallyEq_of_mem
      (Ioo_mem_nhds (hLl.trans_le hr.1) (hr.2.trans_lt hhR))
      (fun t ht => (hεsub ht).1)
  let p := if right then entry else l
  let q := if right then h else entry
  have hpq : p < q := by cases right <;> assumption
  have hpe : p ≤ entry := by
    cases right with
    | false => exact hle.le
    | true => exact le_rfl
  have heq : entry ≤ q := by
    cases right with
    | false => exact le_rfl
    | true => exact heh.le
  have hsub : Icc p q ⊆ Icc l h := by
    intro r hr
    cases right with
    | false => exact ⟨hr.1, hr.2.trans heh.le⟩
    | true => exact ⟨hle.le.trans hr.1, hr.2⟩
  have hpr : 0 < p := hD.1.trans (hclosed p (hsub ⟨le_rfl, hpq.le⟩)).2.1
  have hqr : 0 < q := hpr.trans hpq
  have hOldRange (r : ℝ) (hr : r ∈ Icc p q) :
      r = entry ∨ r ∈ radialTailInterval D right entry := by
    by_cases he : r = entry
    · exact Or.inl he
    · right
      have hcore := (hclosed r (hsub hr)).2
      cases right with
      | false => exact ⟨hcore.1, lt_of_not_ge (fun h => he (le_antisymm hr.2 h))⟩
      | true => exact ⟨lt_of_not_ge (fun h => he (le_antisymm h hr.1)), hcore.2⟩
  have hy₀ : log entry ∈ Icc (log p) (log q) :=
    ⟨Real.log_le_log hpr hpe, Real.log_le_log hepos heq⟩
  have hExpMap (y : ℝ) (hy : y ∈ Icc (log p) (log q)) : exp y ∈ Icc p q := by
    exact ⟨by simpa only [exp_log hpr] using exp_le_exp.mpr hy.1,
      by simpa only [exp_log hqr] using exp_le_exp.mpr hy.2⟩
  have hUd : ContDiffOn ℝ ∞ (deriv U) (Ioi 0) :=
    hU.deriv_of_isOpen isOpen_Ioi (by simp)
  have hUV := seedRadial_eqOn_exp hH hy₀
    (fun y _ => ⟨(hU.contDiffAt (Ioi_mem_nhds (exp_pos y))).differentiableAt (by simp),
      (hUd.contDiffAt (Ioi_mem_nhds (exp_pos y))).differentiableAt (by simp)⟩)
    (fun y _ => ⟨hV.differentiable (by simp) (exp y),
      (contDiff_infty_iff_deriv.mp hV).2.differentiable (by simp) (exp y)⟩)
    (fun y _ => hnew (exp y) (exp_pos y))
    (fun y hy => (radialJacobi_eq_of_profile_germ (hWg (exp y) (hsub (hExpMap y hy)))).trans
      (by
        rcases hOldRange (exp y) (hExpMap y hy) with he | ht
        · simpa only [he] using hold.1
        · exact hold.2 _ ht))
    (by simpa only [exp_log hepos] using h₀)
    (by simpa only [exp_log hepos] using h₁)
  have hUVr (r : ℝ) (hr : r ∈ Icc p q) : U r = V r := by
    have hrpos : 0 < r := hpr.trans_le hr.1
    have hlog : log r ∈ Icc (log p) (log q) :=
      ⟨Real.log_le_log hpr hr.1, Real.log_le_log hrpos hr.2⟩
    simpa only [exp_log hrpos] using (hUV (log r) hlog).1
  let c := (p + q) / 2
  have hpc : p < c := by dsimp only [c]; linarith only [hpq]
  have hcq : c < q := by dsimp only [c]; linarith only [hpq]
  have hc : c ∈ radialTailInterval D right entry := by
    have hcore := (hclosed c (hsub ⟨hpc.le, hcq.le⟩)).2
    cases right with
    | false => exact ⟨hcore.1, hcq⟩
    | true => exact ⟨hpc, hcore.2⟩
  refine ⟨c, hc, hWg c (hsub ⟨hpc.le, hcq.le⟩),
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds hpc hcq)
      (fun r hr => hUVr r ⟨hr.1.le, hr.2.le⟩), ?_⟩
  intro r hr hi
  have hrpq : r ∈ Icc p q := by
    cases right with
    | false => exact ⟨hpc.le.trans hi, hr.2.le⟩
    | true => exact ⟨hr.1.le, hi.trans hcq.le⟩
  exact ⟨(hclosed r (hsub hrpq)).1, hUVr r hrpq⟩

end ContinuousFlexibility.Radial
