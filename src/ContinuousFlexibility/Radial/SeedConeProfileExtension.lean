import ContinuousFlexibility.Radial.SeedPositiveLogExtension

/-!
# A positive radial profile with a prescribed germ and exact cone ends
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

namespace SeedPositiveLogExtension

def radialProfile {f : ℝ → ℝ} {y₀ : ℝ} (E : SeedPositiveLogExtension f y₀) (r : ℝ) : ℝ :=
  exp (E.logProfile (log r))

theorem radialProfile_pos {f : ℝ → ℝ} {y₀ : ℝ}
    (E : SeedPositiveLogExtension f y₀) (r : ℝ) : 0 < E.radialProfile r :=
  exp_pos _

theorem radialProfile_smooth {f : ℝ → ℝ} {y₀ : ℝ}
    (E : SeedPositiveLogExtension f y₀) :
    ContDiffOn ℝ ∞ E.radialProfile (Ioi 0) := by
  have hl : ContDiffOn ℝ ∞ log (Ioi (0 : ℝ)) :=
    contDiffOn_log.mono (fun r hr => by
      simpa only [mem_compl_iff, mem_singleton_iff] using hr.ne')
  exact (E.smooth.comp_contDiffOn hl).exp

theorem radialProfile_hasDerivAt {f : ℝ → ℝ} {y₀ r : ℝ}
    (E : SeedPositiveLogExtension f y₀) (hr : 0 < r) :
    HasDerivAt E.radialProfile
      (E.radialProfile r * deriv E.logProfile (log r) / r) r := by
  have h := (((E.smooth.differentiable (by simp) (log r)).hasDerivAt).comp r
    (hasDerivAt_log hr.ne')).exp
  apply h.congr_deriv
  simp only [radialProfile, Function.comp_apply]
  ring

theorem radialProfile_deriv_pos {f : ℝ → ℝ} {y₀ r : ℝ}
    (E : SeedPositiveLogExtension f y₀) (hr : 0 < r) :
    0 < deriv E.radialProfile r := by
  rw [(E.radialProfile_hasDerivAt hr).deriv]
  exact div_pos (mul_pos (E.radialProfile_pos r) (E.positive _)) hr

theorem radialProfile_cones {f : ℝ → ℝ} {y₀ : ℝ}
    (E : SeedPositiveLogExtension f y₀) :
    ∃ cL cR : ℝ, 0 < cL ∧ 0 < cR ∧
      (∀ r, 0 < r → log r < E.left → E.radialProfile r = cL * r) ∧
      (∀ r, 0 < r → E.right < log r → E.radialProfile r = cR * r) := by
  obtain ⟨a, b, ha, hb⟩ := E.affine_ends
  refine ⟨exp a, exp b, exp_pos a, exp_pos b, ?_, ?_⟩
  · intro r hr hlog
    rw [radialProfile, ha _ hlog, exp_add, exp_log hr, mul_comm]
  · intro r hr hlog
    rw [radialProfile, hb _ hlog, exp_add, exp_log hr, mul_comm]

theorem radialProfile_germ {w : ℝ → ℝ} {e : ℝ}
    (E : SeedPositiveLogExtension (fun y => log (w (exp y))) (log e))
    (he : 0 < e) (hw : ContinuousAt w e) (hwe : 0 < w e) :
    E.radialProfile =ᶠ[𝓝 e] w := by
  have ht := (continuousAt_log he.ne').tendsto
  have hg := E.germ.comp_tendsto ht
  filter_upwards [hg, Ioi_mem_nhds he, hw.eventually (Ioi_mem_nhds hwe)]
    with r hr hrpos hwpos
  rw [radialProfile, hr, exp_log hrpos, exp_log hwpos]

end SeedPositiveLogExtension

/-- The actual profile's positive derivative supplies the local data
needed for the positive logarithmic extension. -/
theorem exists_seedConeProfileExtension {w : ℝ → ℝ} {a b e : ℝ}
    (ha : 0 < a) (he : e ∈ Ioo a b) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ioo a b, 0 < w r) (hder : 0 < deriv w e) :
    Nonempty (SeedPositiveLogExtension (fun y => log (w (exp y))) (log e)) := by
  have hepos : 0 < e := ha.trans he.1
  have hbpos : 0 < b := hepos.trans he.2
  have hymem : log e ∈ Ioo (log a) (log b) :=
    ⟨log_lt_log ha he.1, log_lt_log hepos he.2⟩
  have hmap : MapsTo exp (Ioo (log a) (log b)) (Ioo a b) := by
    intro y hy
    exact ⟨by simpa only [exp_log ha] using exp_lt_exp.mpr hy.1,
      by simpa only [exp_log hbpos] using exp_lt_exp.mpr hy.2⟩
  have hf : ContDiffOn ℝ ∞ (fun y => log (w (exp y))) (Ioo (log a) (log b)) :=
    (hw.comp contDiff_exp).contDiffOn.log (fun y hy => (hpos _ (hmap hy)).ne')
  apply exists_seedPositiveLogExtension hf hymem
  have hd := (((hw.differentiable (by simp) (exp (log e))).hasDerivAt).comp (log e)
    (hasDerivAt_exp (log e))).log (by simpa only [exp_log hepos] using (hpos e he).ne')
  have hd' : HasDerivAt (fun y => log (w (exp y)))
      (deriv w e * e / w e) (log e) := by
    simpa only [exp_log hepos] using hd
  rw [hd'.deriv]
  exact div_pos (mul_pos hder hepos) (hpos e he)

end ContinuousFlexibility.Radial
