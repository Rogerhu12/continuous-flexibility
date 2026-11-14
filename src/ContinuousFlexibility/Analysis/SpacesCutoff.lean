module

public import ContinuousFlexibility.Statements.Analysis
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The endpoint-height cutoff in the physical spaces

The reference profile is positive between its zero endpoints. The mean
value theorem therefore supplies an interval on which its derivative is
positive. A smooth transition supported in that interval gives the
cutoff required by `CutoffConditions`; no choice of reference cutoff is
assumed in the input data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

/-- A left endpoint cutoff with its entire transition in `[l,h]`. -/
def spacesLeftCutoff (l h r : ℝ) : ℝ :=
  1 - Real.smoothTransition ((r - l) / (h - l))

theorem spacesLeftCutoff_contDiff (l h : ℝ) :
    ContDiff ℝ ∞ (spacesLeftCutoff l h) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (h - l)))

theorem spacesLeftCutoff_eq_one {l h r : ℝ} (hlh : l < h) (hr : r ≤ l) :
    spacesLeftCutoff l h r = 1 := by
  unfold spacesLeftCutoff
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) (sub_pos.mpr hlh).le), sub_zero]

theorem spacesLeftCutoff_eq_zero {l h r : ℝ} (hlh : l < h) (hr : h ≤ r) :
    spacesLeftCutoff l h r = 0 := by
  unfold spacesLeftCutoff
  rw [Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ (sub_pos.mpr hlh)).mpr (by linarith)), sub_self]

theorem spacesLeftCutoff_deriv_eq_zero {l h r : ℝ} (hlh : l < h)
    (hr : r ∉ Icc l h) : deriv (spacesLeftCutoff l h) r = 0 := by
  by_cases hrl : r < l
  · have he : spacesLeftCutoff l h =ᶠ[𝓝 r] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hrl] with x hx
      exact spacesLeftCutoff_eq_one hlh hx.le
    simpa only [deriv_const] using he.deriv_eq
  · have hhr : h < r := lt_of_not_ge (fun hrh => hr ⟨le_of_not_gt hrl, hrh⟩)
    have he : spacesLeftCutoff l h =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hhr] with x hx
      exact spacesLeftCutoff_eq_zero hlh hx.le
    simpa only [deriv_const] using he.deriv_eq

/-- Positivity of the profile creates a positive-derivative interval
strictly inside the annulus. -/
theorem spaces_exists_positive_deriv_interval {D : ReferenceData}
    (hD : RadialProfileGeometry D) :
    ∃ l h : ℝ, D.a < l ∧ l < h ∧ h < D.b ∧
      ∀ r ∈ Icc l h, 0 < deriv D.w r := by
  obtain ⟨ha, hab, hw, hphi, hwpos, hphipos, hroots⟩ := hD
  obtain ⟨x, hax, hxb⟩ := exists_between hab
  have hwa : D.w D.a = 0 := hw.2 D.a (Or.inl le_rfl)
  obtain ⟨t, ht, hder⟩ := exists_deriv_eq_slope D.w hax hw.1.continuous.continuousOn
    (hw.1.differentiable (by simp)).differentiableOn
  have htpos : 0 < deriv D.w t := by
    rw [hder, hwa, sub_zero]
    exact div_pos (hwpos x ⟨hax, hxb⟩) (sub_pos.mpr hax)
  have hdcont : Continuous (deriv D.w) := (contDiff_infty_iff_deriv.mp hw.1).2.continuous
  have hnb : {r : ℝ | r ∈ Ioo D.a D.b ∧ 0 < deriv D.w r} ∈ 𝓝 t :=
    inter_mem (Ioo_mem_nhds ht.1 (ht.2.trans hxb))
      (hdcont.continuousAt.preimage_mem_nhds (Ioi_mem_nhds htpos))
  obtain ⟨l₀, h₀, ht₀, hsub₀⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnb
  obtain ⟨l, hl₀, hlt⟩ := exists_between ht₀.1
  obtain ⟨h, hth, h₀h⟩ := exists_between ht₀.2
  have hlh : l < h := hlt.trans hth
  have hsub : Icc l h ⊆ {r : ℝ | r ∈ Ioo D.a D.b ∧ 0 < deriv D.w r} := by
    intro r hr
    exact hsub₀ ⟨hl₀.trans_le hr.1, hr.2.trans_lt h₀h⟩
  exact ⟨l, h, (hsub ⟨le_rfl, hlh.le⟩).1.1, hlh,
    (hsub ⟨hlh.le, le_rfl⟩).1.2, fun r hr => (hsub hr).2⟩

/-- The exact cutoff clause of W02 follows already from the profile geometry. -/
theorem spaces_exists_cutoff {D : ReferenceData} (hD : RadialProfileGeometry D) :
    ∃ χ : ℝ → ℝ, CutoffConditions D χ := by
  obtain ⟨l, h, hal, hlh, hhb, hpos⟩ := spaces_exists_positive_deriv_interval hD
  let δ : ℝ := min (l - D.a) (D.b - h) / 2
  have hd : 0 < δ := div_pos (lt_min (sub_pos.mpr hal) (sub_pos.mpr hhb)) (by norm_num)
  have hdl : δ ≤ (l - D.a) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hdr : δ ≤ (D.b - h) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  refine ⟨spacesLeftCutoff l h, spacesLeftCutoff_contDiff l h, ?_,
    Icc l h, isCompact_Icc, ?_, hpos, fun r hr => spacesLeftCutoff_deriv_eq_zero hlh hr⟩
  · refine ⟨δ, hd, by linarith, ?_, ?_⟩
    · intro r hr
      exact spacesLeftCutoff_eq_one hlh (by linarith)
    · intro r hr
      exact spacesLeftCutoff_eq_zero hlh (by linarith)
  · intro r hr
    exact ⟨hal.trans_le hr.1, hr.2.trans_lt hhb⟩

theorem spaces_exists_cutoff_of_accumulating {D : ReferenceData}
    (hD : IsAccumulatingProfile D) : ∃ χ : ℝ → ℝ, CutoffConditions D χ := by
  obtain ⟨C, hC⟩ := hD
  exact spaces_exists_cutoff hC.1

end ContinuousFlexibility.Statements
