module

public import ContinuousFlexibility.Statements.Analysis

/-!
# The endpoint-distance band of an actual component cutoff

A plateau around a complete closed characteristic interval is allowed to
leave its material cell. Its width is instead chosen from the distances
to the two annular endpoints. The resulting entire support stays in a
controlled endpoint band. This statement does not assert disjointness of
different expanded supports.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis (endpointX)

set_option backward.isDefEq.respectTransparency false

theorem continuous_endpointDistance (D : ReferenceData) : Continuous (endpointDistance D) :=
  (continuous_id.sub continuous_const).min (continuous_const.sub continuous_id)

theorem endpointDistance_positive {D : ReferenceData} {r : ℝ}
    (hr : r ∈ Ioo D.a D.b) : 0 < endpointDistance D r :=
  lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)

theorem endpointX_antitone_positive {d₀ d e : ℝ}
    (hd₀ : 0 < d₀) (hd : 0 < d) (hde : d ≤ e) :
    endpointX d₀ e ≤ endpointX d₀ d := by
  unfold endpointX
  apply Real.sqrt_le_sqrt
  rw [Real.log_div hd₀.ne' (hd.trans_le hde).ne', Real.log_div hd₀.ne' hd.ne']
  exact sub_le_sub_left (Real.log_le_log hd hde) _

private theorem sqrt_le_sqrt_add_error {a b c : ℝ} (hc : 0 ≤ c) (hab : a ≤ b + c) :
    Real.sqrt a ≤ Real.sqrt b + Real.sqrt c := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  have hb : b ≤ Real.sqrt b ^ 2 := by
    rw [Real.sq_sqrt']
    exact le_max_left _ _
  have hc' := Real.sq_sqrt hc
  have hp := mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c)
  nlinarith only [hab, hb, hc', hp]

/-- Changing the endpoint scale is uniformly bounded even away from the
asymptotic endpoint region. -/
theorem endpointX_scale_comparison {d₀ d : ℝ} (hd₀ : 0 < d₀) (hd : 0 < d) :
    |endpointX d₀ d - endpointX 1 d| ≤ Real.sqrt |Real.log d₀| := by
  have heq : Real.log (d₀ / d) - Real.log (1 / d) = Real.log d₀ := by
    rw [Real.log_div hd₀.ne' hd.ne', Real.log_div one_ne_zero hd.ne', Real.log_one]
    ring
  have hforward : Real.log (d₀ / d) ≤ Real.log (1 / d) + |Real.log d₀| := by
    have h := le_abs_self (Real.log d₀)
    linarith only [heq, h]
  have hback : Real.log (1 / d) ≤ Real.log (d₀ / d) + |Real.log d₀| := by
    have h := neg_le_abs (Real.log d₀)
    linarith only [heq, h]
  have hf := sqrt_le_sqrt_add_error (abs_nonneg (Real.log d₀)) hforward
  have hb := sqrt_le_sqrt_add_error (abs_nonneg (Real.log d₀)) hback
  unfold endpointX
  exact abs_le.mpr ⟨by linarith only [hb], by linarith only [hf]⟩

theorem endpointX_half_distance_le {d₀ d : ℝ} (hd₀ : 0 < d₀) (hd : 0 < d) :
    endpointX d₀ (d / 2) ≤ endpointX d₀ d + Real.sqrt (Real.log 2) := by
  have hratio : d₀ / (d / 2) = (d₀ / d) * 2 := by field_simp
  have heq : Real.log (d₀ / (d / 2)) = Real.log (d₀ / d) + Real.log 2 := by
    rw [hratio, Real.log_mul (div_pos hd₀ hd).ne' (by norm_num : (2 : ℝ) ≠ 0)]
  unfold endpointX
  exact sqrt_le_sqrt_add_error (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) heq.le

theorem continuousOn_endpointX_distance {D : ReferenceData} {d₀ : ℝ} (hd₀ : 0 < d₀) :
    ContinuousOn (fun r => endpointX d₀ (endpointDistance D r)) (Ioo D.a D.b) := by
  have hr : ContinuousOn (fun r => d₀ / endpointDistance D r) (Ioo D.a D.b) :=
    continuousOn_const.div (continuous_endpointDistance D).continuousOn
      (fun r hr => (endpointDistance_positive hr).ne')
  exact (hr.log (fun r hr => (div_pos hd₀ (endpointDistance_positive hr)).ne')).sqrt

theorem endpointX_closedInterval_le {D : ReferenceData} {d₀ l r B : ℝ}
    (hd₀ : 0 < d₀) (hl : D.a < l) (hlr : l < r) (hr : r < D.b)
    (hb : ∀ t ∈ Ioo l r, endpointX d₀ (endpointDistance D t) ≤ B) :
    ∀ t ∈ Icc l r, endpointX d₀ (endpointDistance D t) ≤ B := by
  have hclosure : closure (Ioo l r) = Icc l r := closure_Ioo hlr.ne
  have hc : ContinuousOn (fun t => endpointX d₀ (endpointDistance D t)) (closure (Ioo l r)) := by
    rw [hclosure]
    exact (continuousOn_endpointX_distance hd₀).mono
      (fun t ht => ⟨hl.trans_le ht.1, ht.2.trans_lt hr⟩)
  intro t ht
  exact le_on_closure hb hc continuousOn_const (hclosure.symm ▸ ht)

def endpointPlateauWidth (D : ReferenceData) (l r : ℝ) : ℝ :=
  min 1 (min (l - D.a) (D.b - r) / 2)

theorem endpointPlateauWidth_pos {D : ReferenceData} {l r : ℝ}
    (hl : D.a < l) (hr : r < D.b) : 0 < endpointPlateauWidth D l r :=
  lt_min zero_lt_one (div_pos (lt_min (sub_pos.mpr hl) (sub_pos.mpr hr)) (by norm_num))

theorem endpointPlateauWidth_le_one (D : ReferenceData) (l r : ℝ) :
    endpointPlateauWidth D l r ≤ 1 := min_le_left _ _

theorem endpointPlateau_support_subset {D : ReferenceData} {l r : ℝ}
    (hl : D.a < l) (hr : r < D.b) :
    Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r) ⊆
      Ioo D.a D.b := by
  have hw : endpointPlateauWidth D l r ≤ min (l - D.a) (D.b - r) / 2 := min_le_right _ _
  have hwl : endpointPlateauWidth D l r ≤ (l - D.a) / 2 :=
    hw.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hwr : endpointPlateauWidth D l r ≤ (D.b - r) / 2 :=
    hw.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  intro t ht
  constructor <;> linarith [ht.1, ht.2]

theorem endpointX_plateau_support_le {D : ReferenceData} {d₀ l r B : ℝ}
    (hd₀ : 0 < d₀) (hl : D.a < l) (hlr : l ≤ r) (hr : r < D.b)
    (hleft : endpointX d₀ (endpointDistance D l) ≤ B)
    (hright : endpointX d₀ (endpointDistance D r) ≤ B) :
    ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
      endpointX d₀ (endpointDistance D t) ≤ B + Real.sqrt (Real.log 2) := by
  let d : ℝ := min (l - D.a) (D.b - r)
  have hd : 0 < d := lt_min (sub_pos.mpr hl) (sub_pos.mpr hr)
  have hwidth : endpointPlateauWidth D l r ≤ d / 2 := min_le_right _ _
  have hbase : endpointX d₀ d ≤ B := by
    by_cases hside : l - D.a ≤ D.b - r
    · have hside' : l - D.a ≤ D.b - l := by linarith only [hside, hlr]
      simpa only [d, min_eq_left hside, endpointDistance, min_eq_left hside'] using hleft
    · have hside' : D.b - r ≤ l - D.a := le_of_not_ge hside
      have hside'' : D.b - r ≤ r - D.a := by linarith only [hside', hlr]
      simpa only [d, min_eq_right hside', endpointDistance, min_eq_right hside''] using hright
  intro t ht
  have hdist : d / 2 ≤ endpointDistance D t := by
    apply le_min
    · have hdleft : d ≤ l - D.a := min_le_left _ _
      linarith only [hdleft, hwidth, ht.1]
    · have hdright : d ≤ D.b - r := min_le_right _ _
      linarith only [hdright, hwidth, ht.2]
  exact (endpointX_antitone_positive hd₀ (by positivity : 0 < d / 2) hdist).trans
    ((endpointX_half_distance_le hd₀ hd).trans (add_le_add hbase le_rfl))

/-- The complete expanded support lies at most a fixed endpoint-coordinate
distance deeper than the sample of the cell containing the open component. -/
theorem materialCell_plateau_endpointX_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ L : ℝ, 0 < L ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
        endpointX 1 (endpointDistance D t) ≤
          endpointX 1 (endpointDistance D (T.sample j)) + L := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _, hcmp⟩ := hT
  obtain ⟨C, A, hC, _, hc⟩ := hcmp
  refine ⟨2 * C + Real.sqrt (Real.log 2),
    add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hC) (Real.sqrt_nonneg _), ?_⟩
  intro j l r hl hlr hr hcell t ht
  have hb : ∀ s ∈ Icc l r, endpointX 1 (endpointDistance D s) ≤ (D.cellIndex j : ℝ) + C := by
    apply endpointX_closedInterval_le zero_lt_one hl hlr hr
    intro s hs
    have h := (abs_le.mp (hc j s (hcell hs)).1).2
    linarith only [h]
  have hband := endpointX_plateau_support_le zero_lt_one hl hlr.le hr
    (hb l ⟨le_rfl, hlr.le⟩) (hb r ⟨hlr.le, le_rfl⟩) t ht
  have hsample := (abs_le.mp (hc j (T.sample j) (hsamp j)).1).1
  linarith only [hband, hsample]

theorem materialCell_plateau_scaled_endpointX_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    {d₀ : ℝ} (hd₀ : 0 < d₀) :
    ∃ L : ℝ, 0 < L ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
        endpointX d₀ (endpointDistance D t) ≤
          endpointX d₀ (endpointDistance D (T.sample j)) + L := by
  obtain ⟨L, hL, hb⟩ := materialCell_plateau_endpointX_bound hT
  have hsample : ∀ j, T.sample j ∈ Ioo D.a D.b := by
    obtain ⟨_, hbounds⟩ := hD
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _⟩ := hT
    exact fun j => hbounds.2.1.2.2.2.1 j (hsamp j)
  refine ⟨L + 2 * Real.sqrt |Real.log d₀|,
    add_pos_of_pos_of_nonneg hL (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)), ?_⟩
  intro j l r hl hlr hr hcell t ht
  have hband := hb j l r hl hlr hr hcell t ht
  have hscaleT := abs_le.mp (endpointX_scale_comparison hd₀
    (endpointDistance_positive (endpointPlateau_support_subset hl hr ht)))
  have hscaleS := abs_le.mp (endpointX_scale_comparison hd₀
    (endpointDistance_positive (hsample j)))
  linarith only [hband, hscaleT.2, hscaleS.1]

/-- The radial construction also gives a quantitative lower collar width;
only the actual cell containing the open interval is used. -/
theorem materialCell_plateau_width_lower {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (l r : ℝ),
      l < r → Ioo l r ⊆ D.cells j →
      min 1 ((C⁻¹ * Real.exp (-((D.cellIndex j : ℝ) + 1) ^ 2)) / 2) ≤
        endpointPlateauWidth D l r := by
  obtain ⟨A, _, _, hA, _, _, _, hdistance, _⟩ := hD
  refine ⟨A 0, hA 0, ?_⟩
  intro j l r hlr hcell
  let c : ℝ := (A 0)⁻¹ * Real.exp (-((D.cellIndex j : ℝ) + 1) ^ 2)
  have hb : ∀ s ∈ Icc l r, c ≤ endpointDistance D s := by
    intro s hs
    have hclosure : closure (Ioo l r) = Icc l r := closure_Ioo hlr.ne
    apply le_on_closure (fun x hx => (hdistance j x (hcell hx)).1)
      continuousOn_const (continuous_endpointDistance D).continuousOn
    exact hclosure.symm ▸ hs
  have hl := (hb l ⟨le_rfl, hlr.le⟩).trans (min_le_left _ _)
  have hr := (hb r ⟨hlr.le, le_rfl⟩).trans (min_le_right _ _)
  exact min_le_min le_rfl (div_le_div_of_nonneg_right (le_min hl hr) (by norm_num))

end ContinuousFlexibility.Statements
