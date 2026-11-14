module

public import ContinuousFlexibility.Analysis.MaterialSampleShift

/-!
# Endpoint models at every point of the actual material cells

The prescribed endpoint formulas give exact models near either end.
Only one compact middle interval is used to compare the remaining
positive weights. The resulting constants are chosen before every cell
and every physical evaluation point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

private theorem exists_upper_bound_of_endpoint_bound
    {a b η C : ℝ} {f : ℝ → ℝ} (hη : 0 < η)
    (hf : ContinuousOn f (Ioo a b))
    (hnear : ∀ r ∈ Ioo a b, min (r - a) (b - r) < η → f r ≤ C) :
    ∃ K : ℝ, C ≤ K ∧ ∀ r ∈ Ioo a b, f r ≤ K := by
  have hsub : Icc (a + η) (b - η) ⊆ Ioo a b := by
    intro r hr
    constructor <;> linarith only [hr.1, hr.2, hη]
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hf.mono hsub)
  refine ⟨max C B, le_max_left _ _, ?_⟩
  intro r hr
  by_cases hn : min (r - a) (b - r) < η
  · exact (hnear r hr hn).trans (le_max_left _ _)
  · have hd := le_min_iff.mp (le_of_not_gt hn)
    have hi : r ∈ Icc (a + η) (b - η) := by
      constructor <;> linarith only [hd.1, hd.2]
    exact (hB ⟨r, hi, rfl⟩).trans (le_max_right _ _)

private theorem exists_twoSided_mul_bound_of_endpoint_eq
    {a b η : ℝ} {f g : ℝ → ℝ} (hη : 0 < η)
    (hf : ContinuousOn f (Ioo a b)) (hg : ContinuousOn g (Ioo a b))
    (hfpos : ∀ r ∈ Ioo a b, 0 < f r)
    (hgpos : ∀ r ∈ Ioo a b, 0 < g r)
    (he : ∀ r ∈ Ioo a b, min (r - a) (b - r) < η → f r = g r) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ r ∈ Ioo a b,
      f r ≤ K * g r ∧ g r ≤ K * f r := by
  have hfg : ContinuousOn (fun r => f r / g r) (Ioo a b) :=
    hf.div hg (fun r hr => (hgpos r hr).ne')
  have hgf : ContinuousOn (fun r => g r / f r) (Ioo a b) :=
    hg.div hf (fun r hr => (hfpos r hr).ne')
  obtain ⟨Kf, hKf, hfb⟩ := exists_upper_bound_of_endpoint_bound hη hfg
    (C := 1) (fun r hr hn => by rw [he r hr hn, div_self (hgpos r hr).ne'])
  obtain ⟨Kg, hKg, hgb⟩ := exists_upper_bound_of_endpoint_bound hη hgf
    (C := 1) (fun r hr hn => by rw [he r hr hn, div_self (hgpos r hr).ne'])
  refine ⟨max Kf Kg, hKf.trans (le_max_left _ _), ?_⟩
  intro r hr
  exact ⟨(div_le_iff₀ (hgpos r hr)).mp
      ((hfb r hr).trans (le_max_left _ _)),
    (div_le_iff₀ (hfpos r hr)).mp
      ((hgb r hr).trans (le_max_right _ _))⟩

private theorem continuousOn_materialCellEndpointX
    {D : ReferenceData} {d0 : ℝ} (hd0 : 0 < d0) :
    ContinuousOn (fun r => endpointX d0 (endpointDistance D r)) (Ioo D.a D.b) := by
  have hd : Continuous (endpointDistance D) :=
    (continuous_id.sub continuous_const).min (continuous_const.sub continuous_id)
  have hp (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < endpointDistance D r :=
    lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  exact ((continuousOn_const.div hd.continuousOn
    (fun r hr => (hp r hr).ne')).log
      (fun r hr => (div_pos hd0 (hp r hr)).ne')).sqrt

/-- All three actual weights have the same endpoint coordinate and one
uniform coordinate-to-cell error, at every point of every actual cell. -/
theorem materialCell_global_endpoint_models
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ d0 L KH KE KM : ℝ,
      0 < d0 ∧ 0 ≤ L ∧ 1 ≤ KH ∧ 1 ≤ KE ∧ 1 ≤ KM ∧ ∀ m r,
      r ∈ D.cells m →
      let x := endpointX d0 (endpointDistance D r)
      0 ≤ x ∧ |x - (D.cellIndex m : ℝ)| ≤ L ∧
        T.H r ≤ KH * materialH x ∧ materialH x ≤ KH * T.H r ∧
        T.E0 r ≤ KE * materialE0 x ∧ materialE0 x ≤ KE * T.E0 r ∧
        T.M r ≤ KM * materialM x ∧ materialM x ≤ KM * T.M r := by
  have hdata := hT
  obtain ⟨hcont, hpos, _, _, _, _, _, _, _, _, hend, _, _, _, _, _, _, hcell⟩ := hdata
  obtain ⟨d0, δ, hd0, hδ, hδbound, hleft, hright⟩ := hend
  obtain ⟨C, A, hC, hA, hindex⟩ := hcell
  let X : ℝ → ℝ := fun r => endpointX d0 (endpointDistance D r)
  let X1 : ℝ → ℝ := fun r => endpointX 1 (endpointDistance D r)
  have hX : ContinuousOn X (Ioo D.a D.b) := continuousOn_materialCellEndpointX hd0
  have hX1 : ContinuousOn X1 (Ioo D.a D.b) := continuousOn_materialCellEndpointX zero_lt_one
  have hXpos (r : ℝ) : 0 ≤ X r := Real.sqrt_nonneg _
  have hcore (m : ℕ) {r : ℝ} (hr : r ∈ D.cells m) : r ∈ Ioo D.a D.b :=
    hRef.choose_spec.2.1.2.2.2.1 m hr
  have hmodels (r : ℝ) (hr : r ∈ Ioo D.a D.b)
      (hn : endpointDistance D r < δ) :
      T.H r = materialH (X r) ∧ T.E0 r = materialE0 (X r) ∧
        T.M r = materialM (X r) := by
    by_cases hs : r - D.a ≤ D.b - r
    · have hl : r - D.a < δ := by
        simpa only [endpointDistance, min_eq_left hs] using hn
      have h := hleft r ⟨hr.1, by linarith only [hl]⟩
      simpa only [X, endpointDistance, min_eq_left hs] using
        And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2)
    · have hs' : D.b - r ≤ r - D.a := le_of_not_ge hs
      have hr' : D.b - r < δ := by
        simpa only [endpointDistance, min_eq_right hs'] using hn
      have h := hright r ⟨by linarith only [hr'], hr.2⟩
      simpa only [X, endpointDistance, min_eq_right hs'] using
        And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2)
  have hHm : ContinuousOn (fun r => materialH (X r)) (Ioo D.a D.b) :=
    continuous_materialH.comp_continuousOn hX
  have hEm : ContinuousOn (fun r => materialE0 (X r)) (Ioo D.a D.b) :=
    continuousOn_materialE0.comp hX (fun r _ => hXpos r)
  have hMm : ContinuousOn (fun r => materialM (X r)) (Ioo D.a D.b) :=
    continuousOn_materialM.comp hX (fun r _ => hXpos r)
  obtain ⟨KH, hKH, hH⟩ := exists_twoSided_mul_bound_of_endpoint_eq hδ
    ((hcont T.H (by simp)).continuousOn) hHm
    (fun r hr => (hpos r hr).2.1) (fun r _ => materialH_pos (X r))
    (fun r hr hn => (hmodels r hr hn).1)
  obtain ⟨KE, hKE, hE⟩ := exists_twoSided_mul_bound_of_endpoint_eq hδ
    ((hcont T.E0 (by simp)).continuousOn) hEm
    (fun r hr => (hpos r hr).2.2.1) (fun r _ => materialE0_pos (X r))
    (fun r hr hn => (hmodels r hr hn).2.1)
  obtain ⟨KM, hKM, hM⟩ := exists_twoSided_mul_bound_of_endpoint_eq hδ
    ((hcont T.M (by simp)).continuousOn) hMm
    (fun r hr => zero_lt_one.trans_le (hpos r hr).2.2.2)
    (fun r _ => materialM_pos (X r)) (fun r hr hn => (hmodels r hr hn).2.2)
  let η := min δ 1
  have hη : 0 < η := lt_min hδ zero_lt_one
  obtain ⟨B, hB, hscale⟩ := exists_upper_bound_of_endpoint_bound hη (hX.sub hX1).abs
    (C := Real.sqrt |Real.log d0|) (fun r hr hn =>
      abs_endpointX_scale_sub_le hd0
        (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2))
        ((hn.trans_le (min_le_left _ _)).trans
          (hδbound.trans_le (min_le_left _ _)))
        (hn.trans_le (min_le_right _ _)))
  refine ⟨d0, B + C, KH, KE, KM, hd0,
    add_nonneg ((Real.sqrt_nonneg _).trans hB) hC.le, hKH, hKE, hKM, ?_⟩
  intro m r hr
  have hrcore := hcore m hr
  refine ⟨hXpos r, ?_, (hH r hrcore).1, (hH r hrcore).2,
    (hE r hrcore).1, (hE r hrcore).2, (hM r hrcore).1, (hM r hrcore).2⟩
  exact (abs_sub_le (X r) (X1 r) (D.cellIndex m : ℝ)).trans
    (add_le_add (hscale r hrcore) (hindex m r hr).1)

end ContinuousFlexibility.Statements
