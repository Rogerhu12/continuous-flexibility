import ContinuousFlexibility.Analysis.MaterialLocalComparison
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Quantitative material windows for the circle trace

The physical sample windows supplied by `IsMaterialData` are converted to
pairwise disjoint material-coordinate windows of radius at most one. Every
inverse power of a window radius is bounded by one power of the weight `M`.
The windows are locally finite because the original cells are locally finite
away from the two endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The material scale is bounded on the entire open physical interval. -/
theorem spaces_material_ell_bounded {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ r ∈ Ioo D.a D.b, T.ell r ≤ L := by
  obtain ⟨hsmooth, _, _, _, _, _, _, _, _, _, hend, _⟩ := hT
  obtain ⟨d₀, δ, _, hδ, _, hleft, hright⟩ := hend
  have hsub : Icc (D.a + δ) (D.b - δ) ⊆ Ioo D.a D.b := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    ((hsmooth T.ell (by simp)).continuousOn.mono hsub)
  let L := max 1 (max δ B)
  have hδL : δ ≤ L := (le_max_left δ B).trans (le_max_right 1 _)
  have hBL : B ≤ L := (le_max_right δ B).trans (le_max_right 1 _)
  have hendpoint (d : ℝ) (hd : 0 ≤ d) :
      d / (1 + ContinuousFlexibility.Analysis.endpointX d₀ d) ≤ d := by
    have hx : 0 ≤ ContinuousFlexibility.Analysis.endpointX d₀ d := Real.sqrt_nonneg _
    exact div_le_self hd (by linarith)
  refine ⟨L, le_max_left _ _, fun r hr => ?_⟩
  by_cases hl : r < D.a + δ
  · rw [(hleft r ⟨hr.1, hl⟩).1]
    exact (hendpoint _ (sub_pos.mpr hr.1).le).trans ((by linarith : r - D.a ≤ δ).trans hδL)
  by_cases hh : D.b - δ < r
  · rw [(hright r ⟨hh, hr.2⟩).1]
    exact (hendpoint _ (sub_pos.mpr hr.2).le).trans ((by linarith : D.b - r ≤ δ).trans hδL)
  exact (hB ⟨r, ⟨le_of_not_gt hl, le_of_not_gt hh⟩, rfl⟩).trans hBL

/-- The inverse material coordinate has one global Lipschitz constant. -/
theorem spaces_material_radius_lipschitz {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ x y : ℝ, |T.radius x - T.radius y| ≤ L * |x - y| := by
  obtain ⟨L, hL, hell⟩ := spaces_material_ell_bounded hT
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _, hderiv, _⟩ := hT
  refine ⟨L, hL, fun x y => ?_⟩
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => (hderiv z).differentiableAt)
      (fun z _ => by
        rw [(hderiv z).deriv, Real.norm_eq_abs,
          abs_of_pos (hpos _ (hinside z).1).1]
        exact hell _ (hinside z).1)
      (mem_univ y) (mem_univ x)

/-- The center of the `m`-th trace window in material coordinates. -/
def spaces_trace_center (T : MaterialData) (m : ℕ) : ℝ := T.rho (T.sample m)

/-- The actual sample windows admit radii whose derivatives cost only one
weight order, independently of the requested derivative order. -/
theorem spaces_trace_windows {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    ∃ η : ℕ → ℝ,
      (∀ m, 0 < η m ∧ η m ≤ 1) ∧
      (∀ m x, |x - spaces_trace_center T m| ≤ η m → T.radius x ∈ D.cells m) ∧
      Pairwise (fun m n => Disjoint
        (Ioo (spaces_trace_center T m - η m) (spaces_trace_center T m + η m))
        (Ioo (spaces_trace_center T n - η n) (spaces_trace_center T n + η n))) ∧
      LocallyFinite (fun m =>
        Icc (spaces_trace_center T m - η m) (spaces_trace_center T m + η m)) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ m, (η m)⁻¹ ^ k ≤ C * T.M (T.sample m) := by
  obtain ⟨profileC, hprofile⟩ := hD
  obtain ⟨_, hpartition, _, _, _, hlocal, _⟩ := hprofile
  have hcells : ∀ m, D.cells m ⊆ Ioo D.a D.b := hpartition.2.2.2.1
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, hradius, hinside, hright, _, _, henv,
    _, _, _, hsample, hwidths, _⟩ := hdata
  obtain ⟨width, K, hK, hwidth, hdisj⟩ := hwidths
  obtain ⟨L, hL, hLip⟩ := spaces_material_radius_lipschitz hT
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hs (m : ℕ) : T.sample m ∈ Ioo D.a D.b := hcells m (hsample m)
  have hrcenter (m : ℕ) : T.radius (spaces_trace_center T m) = T.sample m :=
    hright _ (hs m)
  let η : ℕ → ℝ := fun m => min 1 (width m / L)
  have hηpos (m : ℕ) : 0 < η m := lt_min zero_lt_one (div_pos (hwidth m).1 hLp)
  have hηL (m : ℕ) : L * η m ≤ width m := by
    have h := (le_div_iff₀ hLp).mp (min_le_right 1 (width m / L))
    simpa only [mul_comm] using h
  have hclosed (m : ℕ) (x : ℝ) (hx : |x - spaces_trace_center T m| ≤ η m) :
      T.radius x ∈ D.cells m := by
    have hb := (hLip x (spaces_trace_center T m)).trans
      ((mul_le_mul_of_nonneg_left hx hLp.le).trans (hηL m))
    rw [hrcenter] at hb
    exact (hwidth m).2.2 ⟨by linarith [(abs_le.mp hb).1], by linarith [(abs_le.mp hb).2]⟩
  have hopen (m : ℕ) (x : ℝ)
      (hx : x ∈ Ioo (spaces_trace_center T m - η m) (spaces_trace_center T m + η m)) :
      T.radius x ∈ Ioo (T.sample m - width m) (T.sample m + width m) := by
    have hdist : |x - spaces_trace_center T m| < η m := abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hb := (hLip x (spaces_trace_center T m)).trans_lt
      ((mul_lt_mul_of_pos_left hdist hLp).trans_le (hηL m))
    rw [hrcenter] at hb
    exact ⟨by linarith [(abs_lt.mp hb).1], by linarith [(abs_lt.mp hb).2]⟩
  refine ⟨η, fun m => ⟨hηpos m, min_le_left _ _⟩, hclosed, ?_, ?_, ?_⟩
  · intro m n hmn
    apply Set.disjoint_left.mpr
    intro x hxm hxn
    exact Set.disjoint_left.mp (hdisj hmn) (hopen m x hxm) (hopen n x hxn)
  · intro x
    let J : Set ℝ := Icc (x - 1) (x + 1)
    let U : Set ℝ := Ioo (x - 1) (x + 1)
    have hcompact : IsCompact (T.radius '' J) := isCompact_Icc.image hradius.continuous
    have hsub : T.radius '' J ⊆ radialCore D := by
      rintro _ ⟨y, _, rfl⟩
      exact (hinside y).1
    refine ⟨U, Ioo_mem_nhds (by linarith) (by linarith),
      (hlocal _ hcompact hsub).subset ?_⟩
    rintro m ⟨y, hy, hyU⟩
    have hyabs : |y - spaces_trace_center T m| ≤ η m :=
      abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact ⟨T.radius y, hclosed m y hyabs, ⟨y, ⟨hyU.1.le, hyU.2.le⟩, rfl⟩⟩
  · intro k
    obtain ⟨B, hB, hbound⟩ := henv (K * k)
    let C := max 1 ((L * K) ^ k * B)
    have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨C, hC, fun m => ?_⟩
    have hM : 1 ≤ T.M (T.sample m) := (hpos _ (hs m)).2.2.2
    have hE : 0 < T.E0 (T.sample m) := (hpos _ (hs m)).2.2.1
    have hinv : (width m)⁻¹ ≤ K * T.E0 (T.sample m) ^ K := by
      have h := (inv_le_inv₀ (hwidth m).1
        (mul_pos (inv_pos.mpr hK) (Real.rpow_pos_of_pos hE _))).mpr (hwidth m).2.1
      simpa only [mul_inv_rev, inv_inv, Real.rpow_neg hE.le, inv_inv, mul_comm] using h
    by_cases hm : 1 ≤ width m / L
    · have he : η m = 1 := min_eq_left hm
      rw [he, inv_one, one_pow]
      exact hM.trans (le_mul_of_one_le_left (zero_lt_one.trans_le hM).le (le_max_left _ _))
    · have he : η m = width m / L := min_eq_right (le_of_not_ge hm)
      rw [he, inv_div]
      have hscale : L / width m ≤ (L * K) * T.E0 (T.sample m) ^ K := by
        simpa only [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left hinv hLp.le
      calc
        (L / width m) ^ k ≤ ((L * K) * T.E0 (T.sample m) ^ K) ^ k :=
          pow_le_pow_left₀ (div_pos hLp (hwidth m).1).le hscale k
        _ = (L * K) ^ k * T.E0 (T.sample m) ^ (K * k) := by
          rw [mul_pow, Real.rpow_mul_natCast hE.le K k]
        _ ≤ (L * K) ^ k * (B * T.M (T.sample m)) :=
          mul_le_mul_of_nonneg_left (hbound _ (hs m)) (pow_nonneg (mul_pos hLp hK).le _)
        _ ≤ C * T.M (T.sample m) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_lt_one.trans_le hM).le

/-- Disjoint physical sample intervals have summable radii because they all
lie in the same bounded physical interval. -/
theorem spaces_summable_disjoint_widths {a b : ℝ} {center width : ℕ → ℝ}
    (hwidth : ∀ m, 0 ≤ width m)
    (hsub : ∀ m, Ioo (center m - width m) (center m + width m) ⊆ Ioo a b)
    (hdisj : Pairwise (fun m n => Disjoint
      (Ioo (center m - width m) (center m + width m))
      (Ioo (center n - width n) (center n + width n)))) :
    Summable width := by
  have hsum : (∑' m, ENNReal.ofReal (width m)) < (∞ : ℝ≥0∞) := by
    calc
      (∑' m, ENNReal.ofReal (width m)) ≤
          ∑' m, volume (Ioo (center m - width m) (center m + width m)) := by
        apply ENNReal.tsum_le_tsum
        intro m
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_le_ofReal (by linarith [hwidth m])
      _ = volume (⋃ m, Ioo (center m - width m) (center m + width m)) :=
        (measure_iUnion hdisj (fun _ => measurableSet_Ioo)).symm
      _ ≤ volume (Ioo a b) := measure_mono (iUnion_subset hsub)
      _ < (∞ : ℝ≥0∞) := by simp only [Real.volume_Ioo, ENNReal.ofReal_lt_top]
  simpa only [ENNReal.toReal_ofReal (hwidth _)] using ENNReal.summable_toReal hsum.ne

/-- The sample weights provide an absolutely summable inverse sequence.
This follows from the original physical windows; no bound on the number of
cells at a given index is added. -/
theorem spaces_trace_sample_inv_summable {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    Summable (fun m => (T.M (T.sample m))⁻¹) := by
  obtain ⟨_, hprofile⟩ := hD
  have hcells : ∀ m, D.cells m ⊆ Ioo D.a D.b := hprofile.2.1.2.2.2.1
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, henv,
    _, _, _, hsample, hwidths, _⟩ := hT
  obtain ⟨width, K, hK, hwidth, hdisj⟩ := hwidths
  obtain ⟨B, hB, hbound⟩ := henv K
  have hs (m : ℕ) : T.sample m ∈ Ioo D.a D.b := hcells m (hsample m)
  have hsum : Summable width := spaces_summable_disjoint_widths
    (fun m => (hwidth m).1.le)
    (fun m => (Ioo_subset_Icc_self.trans (hwidth m).2.2).trans (hcells m)) hdisj
  apply Summable.of_nonneg_of_le
    (fun m => inv_nonneg.mpr (zero_lt_one.trans_le (hpos _ (hs m)).2.2.2).le)
    (fun m => ?_) (hsum.mul_left (K * B))
  have hE : 0 < T.E0 (T.sample m) := (hpos _ (hs m)).2.2.1
  have hM : 0 < T.M (T.sample m) := zero_lt_one.trans_le (hpos _ (hs m)).2.2.2
  have hw : (width m)⁻¹ ≤ K * T.E0 (T.sample m) ^ K := by
    have h := (inv_le_inv₀ (hwidth m).1
      (mul_pos (inv_pos.mpr hK) (Real.rpow_pos_of_pos hE _))).mpr (hwidth m).2.1
    simpa only [mul_inv_rev, inv_inv, Real.rpow_neg hE.le, inv_inv, mul_comm] using h
  have hw' : 1 / width m ≤ K * (B * T.M (T.sample m)) := by
    simpa only [one_div] using
      hw.trans (mul_le_mul_of_nonneg_left (hbound _ (hs m)) hK.le)
  have hp := (div_le_iff₀ (hwidth m).1).mp hw'
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hM).mpr
  nlinarith only [hp]

/-- The inverse sample weight is in `ℓ²`, the summation bound used by the
packet extension and by the trace estimate. -/
theorem spaces_trace_sample_inv_sq_summable {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    Summable (fun m => ((T.M (T.sample m))⁻¹) ^ 2) := by
  have hsum := spaces_trace_sample_inv_summable hD hT
  obtain ⟨_, hprofile⟩ := hD
  have hcells : ∀ m, D.cells m ⊆ Ioo D.a D.b := hprofile.2.1.2.2.2.1
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _⟩ := hT
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => ?_) hsum
  have hM : 1 ≤ T.M (T.sample m) := (hpos _ (hcells m (hsample m))).2.2.2
  have hi : 0 ≤ (T.M (T.sample m))⁻¹ := inv_nonneg.mpr (zero_le_one.trans hM)
  have hi1 : (T.M (T.sample m))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hM
  simpa only [pow_two, one_mul] using mul_le_mul_of_nonneg_right hi1 hi

end ContinuousFlexibility.Statements
