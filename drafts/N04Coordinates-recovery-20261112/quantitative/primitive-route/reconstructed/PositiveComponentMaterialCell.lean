import ContinuousFlexibility.Analysis.MaterialOneSidedEndpointComparison
import ContinuousFlexibility.Analysis.N04PositiveComponents

/-!
# A genuine material label for each whole positive component

The chosen cell contains the actual midpoint. The entire component need
not belong to that cell. Its midpoint is no closer to an ambient endpoint
than half the distance of any other component point. This one-sided fact
controls the actual height normalizer and sample coefficient powers.
It does not assert the reverse endpoint-to-sample bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

def n04PositiveMidpoint {a b : ℝ} {f : ℝ → ℝ}
    (i : N04PositiveComponent a b f) : ℝ :=
  (n04PositiveLeft i + n04PositiveRight i) / 2

theorem endpointDistance_le_twice_interval_midpoint
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

private theorem endpointX_oneSided_of_distance_le_two_mul
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

theorem n04PositiveMidpoint_mem_core
    {D : ReferenceData} (hf : Continuous (deriv D.w))
    (i : N04PositiveComponent D.a D.b (deriv D.w)) :
    n04PositiveMidpoint i ∈ Ioo D.a D.b := by
  have h := n04PositiveComponent_bounds hf i
  unfold n04PositiveMidpoint
  constructor <;> linarith only [h.1, h.2.1, h.2.2]

/-- The cell is chosen once from the actual partition, before every
order, point and state. Only the midpoint is required to be in it. -/
theorem exists_wholePositive_midpoint_material_cells
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ,
      (∀ i, n04PositiveMidpoint i ∈ D.cells (cell i)) ∧
      (∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ i r,
        r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) → r ∈ Ioo D.a D.b →
        T.H r / T.H (T.sample (cell i)) ≤ B * T.E0 r ^ A) ∧
      ∀ R : ℝ, 0 ≤ R → ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ i r,
        r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) → r ∈ Ioo D.a D.b →
        T.E0 (T.sample (cell i)) ^ R ≤ B * T.E0 r ^ A := by
  classical
  have hpart : RadialPartition D := hRef.choose_spec.2.1
  have hf : Continuous (deriv D.w) :=
    hRef.choose_spec.1.2.2.1.1.continuous_deriv (by simp)
  have hcover {r : ℝ} (hr : r ∈ Ioo D.a D.b) : ∃ m, r ∈ D.cells m := by
    have hex : ∃ m, D.localizer m r ≠ 0 := by
      by_contra hn
      push_neg at hn
      have hz : (∑' m, D.localizer m r) = 0 := by simp only [hn, tsum_zero]
      have ho := (hpart.2.2.2.2.1 r hr).2
      linarith only [hz, ho]
    obtain ⟨m, hm⟩ := hex
    exact ⟨m, hpart.2.2.1 m hm⟩
  have hmid : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∃ m, n04PositiveMidpoint i ∈ D.cells m :=
    fun i => hcover (n04PositiveMidpoint_mem_core hf i)
  choose cell hcell using hmid
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _, hcompare⟩ := hdata
  obtain ⟨C, P, hC, hP, hindex⟩ := hcompare
  have hL : 0 ≤ 2 * C + 1 := by positivity
  have hsample (i : N04PositiveComponent D.a D.b (deriv D.w)) :
      T.sample (cell i) ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hpart (cell i)
  have hshift (i : N04PositiveComponent D.a D.b (deriv D.w)) (r : ℝ)
      (hr : r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i))
      (hrcore : r ∈ Ioo D.a D.b) :
      endpointX 1 (Statements.endpointDistance D (T.sample (cell i))) ≤
        endpointX 1 (Statements.endpointDistance D r) + (2 * C + 1) := by
    have hmcore := n04PositiveMidpoint_mem_core hf i
    have hbounds := n04PositiveComponent_bounds hf i
    have hdist := endpointDistance_le_twice_interval_midpoint hbounds.1 hbounds.2.2 hr
    have hmidX :
        endpointX 1 (Statements.endpointDistance D (n04PositiveMidpoint i)) ≤
          endpointX 1 (Statements.endpointDistance D r) + 1 :=
      endpointX_oneSided_of_distance_le_two_mul
        (lt_min (sub_pos.mpr hrcore.1) (sub_pos.mpr hrcore.2))
        (lt_min (sub_pos.mpr hmcore.1) (sub_pos.mpr hmcore.2)) hdist
    have hsIndex := (hindex (cell i) (T.sample (cell i)) (hsamp (cell i))).1
    have hmIndex := (hindex (cell i) (n04PositiveMidpoint i) (hcell i)).1
    have hs := (abs_le.mp hsIndex).2
    have hm := (abs_le.mp hmIndex).1
    linarith only [hs, hm, hmidX]
  refine ⟨cell, hcell, ?_, ?_⟩
  · obtain ⟨B, A, K, Q, hB, hA, _, _, hbound⟩ :=
      material_oneSided_endpoint_comparison hT hRef (R := 0) (by norm_num) hL
    exact ⟨B, A, hB, hA, fun i r hr hrcore =>
      (hbound r (T.sample (cell i)) hrcore (hsample i) (hshift i r hr hrcore)).1⟩
  · intro R hR
    obtain ⟨K, Q, B, A, _, _, hB, hA, hbound⟩ :=
      material_oneSided_endpoint_comparison hT hRef hR hL
    exact ⟨B, A, hB, hA, fun i r hr hrcore =>
      (hbound r (T.sample (cell i)) hrcore (hsample i) (hshift i r hr hrcore)).2⟩

end ContinuousFlexibility.Analysis
