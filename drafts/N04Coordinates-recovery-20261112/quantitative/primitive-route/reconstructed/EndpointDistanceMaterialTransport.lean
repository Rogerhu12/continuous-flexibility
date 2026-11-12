import ContinuousFlexibility.Analysis.MaterialEndpointWeightRatios

/-!
# Material ratios inside a true endpoint-distance collar

Two points within half the ambient endpoint distance of the same
interior radius have endpoint distances comparable by a factor of three.
Their actual endpoint coordinates differ by at most two, even where the
logarithm in the total real square root is negative. The resulting
material constants are chosen before the centre and both points.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem endpointDistance_half_collar_bounds {D : ReferenceData} {c r : ℝ}
    (hc : c ∈ Ioo D.a D.b)
    (hr : |r - c| ≤ Statements.endpointDistance D c / 2) :
    r ∈ Ioo D.a D.b ∧ Statements.endpointDistance D c / 2 ≤ Statements.endpointDistance D r ∧
      Statements.endpointDistance D r ≤ 3 * Statements.endpointDistance D c / 2 := by
  let d := Statements.endpointDistance D c
  change r ∈ Ioo D.a D.b ∧ d / 2 ≤ Statements.endpointDistance D r ∧
    Statements.endpointDistance D r ≤ 3 * d / 2
  have hd : 0 < d := lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)
  have hdl : d ≤ c - D.a := min_le_left _ _
  have hdr : d ≤ D.b - c := min_le_right _ _
  have hlo : -(d / 2) ≤ r - c := (abs_le.mp hr).1
  have hhi : r - c ≤ d / 2 := (abs_le.mp hr).2
  refine ⟨⟨by linarith, by linarith⟩, le_min (by linarith) (by linarith), ?_⟩
  rcases le_total (c - D.a) (D.b - c) with h | h
  · have he : d = c - D.a := min_eq_left h
    exact (min_le_left (r - D.a) (D.b - r)).trans (by linarith)
  · have he : d = D.b - c := min_eq_right h
    exact (min_le_right (r - D.a) (D.b - r)).trans (by linarith)

private theorem abs_sqrt_sub_le_two_of_abs_sub_le_two {u v : ℝ}
    (h : |u - v| ≤ 2) : |Real.sqrt u - Real.sqrt v| ≤ 2 := by
  have hu : u ≤ (Real.sqrt u) ^ 2 := by rw [Real.sq_sqrt']; exact le_max_left _ _
  have hv : v ≤ (Real.sqrt v) ^ 2 := by rw [Real.sq_sqrt']; exact le_max_left _ _
  have hsu := Real.sqrt_nonneg u
  have hsv := Real.sqrt_nonneg v
  have hup : Real.sqrt u ≤ Real.sqrt v + 2 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith only [hv, hsv, (abs_le.mp h).2]⟩
  have hdown : Real.sqrt v ≤ Real.sqrt u + 2 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith only [hu, hsu, (abs_le.mp h).1]⟩
  exact abs_le.mpr ⟨by linarith only [hdown], by linarith only [hup]⟩

private theorem endpointX_one_shift_of_three_comparable {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 3 * b) (hba : b ≤ 3 * a) :
    |endpointX 1 a - endpointX 1 b| ≤ 2 := by
  have hab' : a / b ≤ 3 := (div_le_iff₀ hb).mpr hab
  have hba' : b / a ≤ 3 := (div_le_iff₀ ha).mpr hba
  have hlogab : Real.log a - Real.log b ≤ 2 := by
    rw [← Real.log_div ha.ne' hb.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
    linarith only [h, hab']
  have hlogba : Real.log b - Real.log a ≤ 2 := by
    rw [← Real.log_div hb.ne' ha.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
    linarith only [h, hba']
  change |Real.sqrt (Real.log (1 / a)) - Real.sqrt (Real.log (1 / b))| ≤ 2
  apply abs_sqrt_sub_le_two_of_abs_sub_le_two
  rw [Real.log_div one_ne_zero ha.ne', Real.log_div one_ne_zero hb.ne', Real.log_one]
  exact abs_le.mpr ⟨by linarith only [hlogab], by linarith only [hlogba]⟩

theorem endpointX_one_shift_on_half_distance_collar {D : ReferenceData} {c r s : ℝ}
    (hc : c ∈ Ioo D.a D.b)
    (hr : |r - c| ≤ Statements.endpointDistance D c / 2)
    (hs : |s - c| ≤ Statements.endpointDistance D c / 2) :
    |endpointX 1 (Statements.endpointDistance D r) - endpointX 1 (Statements.endpointDistance D s)| ≤ 2 := by
  have hbr := endpointDistance_half_collar_bounds hc hr
  have hbs := endpointDistance_half_collar_bounds hc hs
  have hdr : 0 < Statements.endpointDistance D r :=
    lt_min (sub_pos.mpr hbr.1.1) (sub_pos.mpr hbr.1.2)
  have hds : 0 < Statements.endpointDistance D s :=
    lt_min (sub_pos.mpr hbs.1.1) (sub_pos.mpr hbs.1.2)
  exact endpointX_one_shift_of_three_comparable hdr hds
    (by linarith only [hbr.2.2, hbs.2.1])
    (by linarith only [hbs.2.2, hbr.2.1])

/-- Neither point is required to lie in the same material cell as the
centre or as the other point. The material witness stays unchanged. -/
theorem material_H_M_ratios_on_endpointDistance_collar
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ c r s : ℝ,
      c ∈ Ioo D.a D.b →
      |r - c| ≤ Statements.endpointDistance D c / 2 →
      |s - c| ≤ Statements.endpointDistance D c / 2 →
      T.H r / T.H s ≤ K * T.E0 s ^ A ∧
        T.M r / T.M s ≤ K * T.E0 s ^ A := by
  obtain ⟨K, A, hK, hA, hratio⟩ :=
    material_H_M_ratios_of_bounded_endpointX_shift hT hRef (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨K, A, hK, hA, ?_⟩
  intro c r s hc hr hs
  exact hratio r s (endpointDistance_half_collar_bounds hc hr).1
    (endpointDistance_half_collar_bounds hc hs).1
    (endpointX_one_shift_on_half_distance_collar hc hr hs)

end ContinuousFlexibility.Analysis
