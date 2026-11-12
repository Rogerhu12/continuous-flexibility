import ContinuousFlexibility.Analysis.N04RealizationMaterialTransfer
import ContinuousFlexibility.Analysis.N04PositiveComponents
import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData

/-!
# Exact height decay at the retained positive-component sample

The material label is supplied by the existing construction. Its only
required property is that its cell contains the component midpoint. A
one-sided endpoint-coordinate estimate then transfers the full positive
height exponent to that same sample, including components which touch an
ambient endpoint. No cell or sample is selected in this module.

The elementary displacement proof is extracted from the already merged
recovery version of PositiveComponentMaterialCell.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

/-- Doubling a positive endpoint distance changes the truncated logarithmic
coordinate by at most one in the useful direction. -/
theorem n04Realization_endpointX_oneSided_of_distance_le_two_mul
    {d e : ℝ} (hd : 0 < d) (he : 0 < e) (hde : d ≤ 2 * e) :
    endpointX 1 e ≤ endpointX 1 d + 1 := by
  have hquot : d / e ≤ 2 := (div_le_iff₀ he).mpr hde
  have hlog : Real.log d - Real.log e ≤ 1 := by
    rw [← Real.log_div hd.ne' he.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hd he)
    linarith only [h, hquot]
  have hu : Real.log (1 / e) ≤ Real.log (1 / d) + 1 := by
    rw [Real.log_div one_ne_zero he.ne', Real.log_div one_ne_zero hd.ne', Real.log_one]
    linarith only [hlog]
  have hv : Real.log (1 / d) ≤ (Real.sqrt (Real.log (1 / d))) ^ 2 := by
    rw [Real.sq_sqrt']
    exact le_max_left _ _
  change Real.sqrt (Real.log (1 / e)) ≤ Real.sqrt (Real.log (1 / d)) + 1
  exact Real.sqrt_le_iff.mpr ⟨by positivity,
    by nlinarith only [hu, hv, Real.sqrt_nonneg (Real.log (1 / d))]⟩

/-- Every point of the closed component interval has endpoint distance at
most twice that of its midpoint; ambient endpoint equality is allowed. -/
theorem n04Realization_endpointDistance_le_twice_midpoint
    {D : ReferenceData} {l h r : ℝ}
    (hal : D.a ≤ l) (hhb : h ≤ D.b) (hr : r ∈ Icc l h) :
    Statements.endpointDistance D r ≤
      2 * Statements.endpointDistance D ((l + h) / 2) := by
  change min (r - D.a) (D.b - r) ≤
    2 * min ((l + h) / 2 - D.a) (D.b - (l + h) / 2)
  rcases le_total ((l + h) / 2 - D.a) (D.b - (l + h) / 2) with he | he
  · rw [min_eq_left he]
    exact (min_le_left (r - D.a) (D.b - r)).trans (by linarith only [hr.2, hal])
  · rw [min_eq_right he]
    exact (min_le_right (r - D.a) (D.b - r)).trans (by linarith only [hr.1, hhb])

/-- The displacement estimate applies to the supplied material labels.
The uniform constant depends only on the retained material data. -/
theorem n04Realization_positive_midpoint_cell_endpoint_shift
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (hcell : ∀ i, (n04PositiveLeft i + n04PositiveRight i) / 2 ∈ D.cells (cell i)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i r,
      r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) → r ∈ Ioo D.a D.b →
      endpointX 1 (Statements.endpointDistance D (T.sample (cell i))) ≤
        endpointX 1 (Statements.endpointDistance D r) + L := by
  have hf : Continuous (deriv D.w) :=
    hRef.choose_spec.1.2.2.1.1.continuous_deriv (by simp)
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _, hcompare⟩ := hdata
  obtain ⟨C, P, hC, _hP, hindex⟩ := hcompare
  refine ⟨2 * C + 1, by positivity, ?_⟩
  intro i r hr hrcore
  have hbounds := n04PositiveComponent_bounds hf i
  have hmcore : (n04PositiveLeft i + n04PositiveRight i) / 2 ∈ Ioo D.a D.b := by
    constructor <;> linarith only [hbounds.1, hbounds.2.1, hbounds.2.2]
  have hdist := n04Realization_endpointDistance_le_twice_midpoint
    hbounds.1 hbounds.2.2 hr
  have hmidX :
      endpointX 1 (Statements.endpointDistance D
        ((n04PositiveLeft i + n04PositiveRight i) / 2)) ≤
        endpointX 1 (Statements.endpointDistance D r) + 1 :=
    n04Realization_endpointX_oneSided_of_distance_le_two_mul
      (lt_min (sub_pos.mpr hrcore.1) (sub_pos.mpr hrcore.2))
      (lt_min (sub_pos.mpr hmcore.1) (sub_pos.mpr hmcore.2)) hdist
  have hsIndex := (hindex (cell i) (T.sample (cell i)) (hsamp (cell i))).1
  have hmIndex := (hindex (cell i)
    ((n04PositiveLeft i + n04PositiveRight i) / 2) (hcell i)).1
  linarith only [(abs_le.mp hsIndex).2, (abs_le.mp hmIndex).1, hmidX]

/-- The pointwise coefficient power is absorbed while retaining exactly
the same positive height exponent at the already chosen sample. -/
theorem n04Realization_positive_midpoint_cell_H_E0_rpow
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (hcell : ∀ i, (n04PositiveLeft i + n04PositiveRight i) / 2 ∈ D.cells (cell i))
    {γ R : ℝ} (hγ : 0 < γ) (hR : 0 ≤ R) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ i r,
      r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) → r ∈ Ioo D.a D.b →
      T.H r ^ γ * T.E0 r ^ R ≤
        B * T.H (T.sample (cell i)) ^ γ * T.E0 (T.sample (cell i)) ^ A := by
  obtain ⟨L, hL, hshift⟩ :=
    n04Realization_positive_midpoint_cell_endpoint_shift hT hRef cell hcell
  obtain ⟨B, A, hB, hA, hbound⟩ :=
    n04Realization_material_H_E0_rpow_oneSided hT hRef hγ hR hL
  refine ⟨B, A, hB, hA, ?_⟩
  intro i r hr hrcore
  exact hbound r (T.sample (cell i)) hrcore
    (materialSample_mem_radialCore hT hRef.choose_spec.2.1 (cell i))
    (hshift i r hr hrcore)

/-- The actual whole atlas retains the supplied cell on each positive
piece. Its moving-state presentation therefore uses the same sample and
the full three-quarter height gain. -/
theorem n04Realization_wholePositive_sample_height_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (hcell : ∀ i, (n04PositiveLeft i + n04PositiveRight i) / 2 ∈ D.cells (cell i))
    (F G : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (region : Set ℝ) {R : ℝ} (hR : 0 ≤ R) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q region
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ z m i, e m = .inr i →
      ∀ x, x ∈ physicalPieceOpen S W z m →
        T.H x.1 ^ (3 / 4 : ℝ) * T.E0 x.1 ^ R ≤
          B * T.H (T.sample (W.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (W.cell m)) ^ A := by
  obtain ⟨B, A, hB, hA, hbound⟩ :=
    n04Realization_positive_midpoint_cell_H_E0_rpow hT hRef cell hcell
      (γ := (3 / 4 : ℝ)) (by norm_num) hR
  have hf : Continuous (deriv D.w) :=
    hRef.choose_spec.1.2.2.1.1.continuous_deriv (by simp)
  refine ⟨B, A, hB, hA, ?_⟩
  intro z m i hi x hx
  have hfields := n04WholeCanonicalAtlasData_positive_fields C L K e cell F G Q region
    z m i hi
  have hx' : x ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) := by
    simpa only [hfields.2.2.2.2.1] using hx
  have hpoint := hbound i x.1 ⟨hx'.1.1.le, hx'.1.2.le⟩
    (n04PositiveComponent_interval_subset hf i hx'.1)
  simpa only [hfields.2.2.2.2.2.1] using hpoint

end ContinuousFlexibility.Analysis
