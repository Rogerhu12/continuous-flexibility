module

public import ContinuousFlexibility.Analysis.MaterialPlateauGeometry

/-!
# The reverse endpoint band of an expanded plateau

The physical distance of the full expanded support is bounded above by
the containing cell's distance scale. Together with the previously
proved lower distance bound, this prevents an expanded cutoff from
reaching cells at arbitrarily different endpoint indices.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis (endpointX)

set_option backward.isDefEq.respectTransparency false

theorem endpointDistance_le_add_abs (D : ReferenceData) (r s : ℝ) :
    endpointDistance D r ≤ endpointDistance D s + |r - s| := by
  change min (r - D.a) (D.b - r) ≤ min (s - D.a) (D.b - s) + |r - s|
  by_cases hs : s - D.a ≤ D.b - s
  · rw [min_eq_left hs]
    apply (min_le_left (r - D.a) (D.b - r)).trans
    linarith only [le_abs_self (r - s)]
  · rw [min_eq_right (le_of_not_ge hs)]
    apply (min_le_right (r - D.a) (D.b - r)).trans
    linarith only [neg_le_abs (r - s)]

theorem endpointPlateau_distance_upper {D : ReferenceData} {l r U : ℝ}
    (hlr : l ≤ r) (hU0 : 0 ≤ U)
    (hU : ∀ t ∈ Icc l r, endpointDistance D t ≤ U) :
    ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
      endpointDistance D t ≤ (3 / 2 : ℝ) * U := by
  have hδ : endpointPlateauWidth D l r ≤ endpointDistance D l / 2 := by
    have hmin : min (l - D.a) (D.b - r) ≤ endpointDistance D l := by
      apply min_le_min le_rfl
      linarith only [hlr]
    exact (min_le_right _ _).trans (div_le_div_of_nonneg_right hmin (by norm_num))
  have hδU : endpointPlateauWidth D l r ≤ U / 2 :=
    hδ.trans (div_le_div_of_nonneg_right (hU l ⟨le_rfl, hlr⟩) (by norm_num))
  intro t ht
  by_cases htl : t < l
  · have hb := endpointDistance_le_add_abs D t l
    rw [abs_of_nonpos (sub_nonpos.mpr htl.le)] at hb
    have hl := hU l ⟨le_rfl, hlr⟩
    linarith only [hb, hl, ht.1, hδU]
  · by_cases hrt : r < t
    · have hb := endpointDistance_le_add_abs D t r
      rw [abs_of_nonneg (sub_nonneg.mpr hrt.le)] at hb
      have hr := hU r ⟨hlr, le_rfl⟩
      linarith only [hb, hr, ht.2, hδU]
    · have hb := hU t ⟨le_of_not_gt htl, le_of_not_gt hrt⟩
      nlinarith only [hb, hU0]

theorem materialCell_plateau_distance_upper {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (l r : ℝ),
      l < r → Ioo l r ⊆ D.cells j →
      ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
        endpointDistance D t ≤ C * Real.exp (-(D.cellIndex j : ℝ) ^ 2) := by
  obtain ⟨A, _, _, hA, _, _, _, hdistance, _⟩ := hD
  refine ⟨(3 / 2 : ℝ) * A 0, mul_pos (by norm_num) (hA 0), ?_⟩
  intro j l r hlr hcell t ht
  have hb : ∀ s ∈ Icc l r,
      endpointDistance D s ≤ A 0 * Real.exp (-(D.cellIndex j : ℝ) ^ 2) := by
    intro s hs
    have hclosure : closure (Ioo l r) = Icc l r := closure_Ioo hlr.ne
    apply le_on_closure (fun x hx => (hdistance j x (hcell hx)).2)
      (continuous_endpointDistance D).continuousOn continuousOn_const
    exact hclosure.symm ▸ hs
  exact (endpointPlateau_distance_upper hlr.le
    (mul_nonneg (hA 0).le (Real.exp_pos _).le) hb t ht).trans_eq (by ring)

theorem natCast_le_endpointX_of_distance_upper {d C : ℝ}
    (hd : 0 < d) (hC : 0 < C) (n : ℕ)
    (hb : d ≤ C * Real.exp (-(n : ℝ) ^ 2)) :
    (n : ℝ) ≤ endpointX 1 d + Real.sqrt |Real.log C| := by
  have hlog := Real.log_le_log hd hb
  rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hX : 0 ≤ endpointX 1 d := Real.sqrt_nonneg _
  have hXsq : -Real.log d ≤ endpointX 1 d ^ 2 := by
    unfold endpointX
    rw [Real.sq_sqrt', Real.log_div one_ne_zero hd.ne', Real.log_one, zero_sub]
    exact le_max_left _ _
  have hsqrt := Real.sq_sqrt (abs_nonneg (Real.log C))
  have hprod := mul_nonneg hX (Real.sqrt_nonneg |Real.log C|)
  have hsq : (n : ℝ) ^ 2 ≤ (endpointX 1 d + Real.sqrt |Real.log C|) ^ 2 := by
    nlinarith only [hlog, hXsq, hsqrt, hprod, le_abs_self (Real.log C)]
  exact (sq_le_sq₀ (Nat.cast_nonneg _) (add_nonneg hX (Real.sqrt_nonneg _))).mp hsq

/-- The actual containing cell index is controlled in the reverse
direction by every point of the full expanded support. -/
theorem materialCell_plateau_index_endpointX_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ B : ℝ, 0 < B ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ t ∈ Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r),
        (D.cellIndex j : ℝ) ≤ endpointX 1 (endpointDistance D t) + B := by
  obtain ⟨C, hC, hb⟩ := materialCell_plateau_distance_upper hD
  refine ⟨Real.sqrt |Real.log C| + 1, by positivity, ?_⟩
  intro j l r hl hlr hr hcell t ht
  have hd := endpointDistance_positive (endpointPlateau_support_subset hl hr ht)
  have h := natCast_le_endpointX_of_distance_upper hd hC (D.cellIndex j)
    (hb j l r hlr hcell t ht)
  linarith only [h]

end ContinuousFlexibility.Statements
