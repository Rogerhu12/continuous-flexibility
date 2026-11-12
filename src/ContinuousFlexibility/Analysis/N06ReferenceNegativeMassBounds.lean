import ContinuousFlexibility.Analysis.N06ReferenceNegativeMass
import ContinuousFlexibility.Analysis.N06ReferenceTravelBounds

/-!
# Reciprocal mass from the original physical cell certificate

The retained zero-order reciprocal-profile estimate bounds the actual
physical resistance integral.  The cell containing the original negative
component is provided by the original return margin.  Combining this
with the proved cut-travel estimate keeps one and the same physical cell
in both the cut-radius lower bound and the reciprocal-mass upper bound.
This physical index is not replaced by the canonical label `K.cell`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The original profile bound controls every actual cell-contained
physical interval, with constants independent of its location. -/
theorem n06_profileCell_reciprocal_integral_bound
    {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ∃ Q A : ℝ, 0 < Q ∧ 0 < A ∧ ∀ (j : ℕ) (l r : ℝ), l < r →
      Icc l r ⊆ radialCore D → Ioo l r ⊆ D.cells j →
      (∫ t in l..r, (D.w t)⁻¹) ≤ Q * radialE (D.cellIndex j) ^ A := by
  obtain ⟨caps, hcaps⟩ := hD
  rcases hcaps with ⟨hgeom, _, hpositive, _, _, _, _, _, _, hinv, _, _, _⟩
  let Q : ℝ := (D.b - D.a) * caps 0
  have hQ : 0 < Q := mul_pos (sub_pos.mpr hgeom.2.1) (hpositive 0)
  refine ⟨Q, caps 0, hQ, hpositive 0, fun j l r hlr hcore hcell => ?_⟩
  have hwpos (t : ℝ) (ht : t ∈ Icc l r) : 0 < D.w t :=
    hgeom.2.2.2.2.1 t (hcore ht)
  have hcont : ContinuousOn (fun t => (D.w t)⁻¹) (Icc l r) :=
    hgeom.2.2.1.1.continuous.continuousOn.inv₀ (fun t ht => (hwpos t ht).ne')
  have hbound (t : ℝ) (ht : t ∈ Ioo l r) :
      (D.w t)⁻¹ ≤ caps 0 * radialE (D.cellIndex j) ^ caps 0 := by
    have he := hinv j t (hcell ht) 0
    change |(D.w t)⁻¹| ≤ caps 0 * radialE (D.cellIndex j) ^ caps 0 at he
    exact (le_abs_self _).trans he
  have hi : IntervalIntegrable (fun t => (D.w t)⁻¹) volume l r :=
    hcont.intervalIntegrable_of_Icc hlr.le
  have hc : IntervalIntegrable
      (fun _ : ℝ => caps 0 * radialE (D.cellIndex j) ^ caps 0) volume l r :=
    intervalIntegrable_const
  have hint := intervalIntegral.integral_mono_on_of_le_Ioo hlr.le hi hc hbound
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hl := (hcore ⟨le_rfl, hlr.le⟩).1
  have hr := (hcore ⟨hlr.le, le_rfl⟩).2
  have hlength : r - l ≤ D.b - D.a := by linarith only [hl, hr]
  have hE : 0 < radialE (D.cellIndex j) := Real.exp_pos _
  calc
    (∫ t in l..r, (D.w t)⁻¹) ≤
        (r - l) * (caps 0 * radialE (D.cellIndex j) ^ caps 0) := hint
    _ ≤ (D.b - D.a) * (caps 0 * radialE (D.cellIndex j) ^ caps 0) :=
      mul_le_mul_of_nonneg_right hlength
        (mul_nonneg (hpositive 0).le (Real.rpow_pos_of_pos hE _).le)
    _ = Q * radialE (D.cellIndex j) ^ caps 0 := by dsimp only [Q]; ring

private theorem n06_cutHalf_open_subset_component
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) {i : ℕ} (hi : i = (K.cutPair m).1 ∨ i = (K.cutPair m).2) :
    K.positive i = false ∧
      Ioo (K.physicalLeft i) (K.physicalRight i) ⊆ Ioo (C.left m) (C.right m) := by
  rcases h.2.2.2.2 with ⟨_, _, _, hpieces, _, _, _, _, _, _, _, hcut, _⟩
  obtain ⟨hnegL, hnegR, hleft, hright, hmeet, _⟩ := hcut m
  have hlcut : C.left m < K.physicalRight (K.cutPair m).1 := by
    rw [← hleft]
    exact (hpieces (K.cutPair m).1).1
  have hcutr : K.physicalRight (K.cutPair m).1 < C.right m := by
    rw [hmeet, ← hright]
    exact (hpieces (K.cutPair m).2).1
  rcases hi with rfl | rfl
  · refine ⟨hnegL, fun t ht => ?_⟩
    exact ⟨by simpa only [hleft] using ht.1, ht.2.trans hcutr⟩
  · refine ⟨hnegR, fun t ht => ?_⟩
    exact ⟨hlcut.trans (by simpa only [hmeet] using ht.1),
      by simpa only [hright] using ht.2⟩

/-- The original return-margin cell simultaneously controls the true
canonical cut radius and the reciprocal mass for both negative halves. -/
theorem n06_referenceNegative_cut_mass_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    ∃ Q A : ℝ, 0 < Q ∧ 0 < A ∧ ∀ m, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      (1 / 2 : ℝ) * radialE (D.cellIndex j) ^ (-A) ≤ K.cutRadius m ∧
      ∀ i, i = (K.cutPair m).1 ∨ i = (K.cutPair m).2 →
        ∀ P : N06ReferenceNegativeInverseData C K i,
        ∀ a b : ℝ, a ≤ b → Icc a b ⊆ Icc (K.left i) (K.right i) →
          (∫ y in a..b, (P.reciprocalHeight y)⁻¹ ^ 2) ≤
            Q * radialE (D.cellIndex j) ^ A := by
  obtain ⟨Q, A0, hQ, hA0, hmass⟩ :=
    n06_profileCell_reciprocal_integral_bound h.1.1.1.1.1
  obtain ⟨_, A1, _, hA1, hcut⟩ := n06_reference_cut_physical_bounds hT hS h
  let A : ℝ := max A0 A1
  have hA : 0 < A := hA0.trans_le (le_max_left _ _)
  refine ⟨Q, A, hQ, hA, fun m => ?_⟩
  obtain ⟨j, hcell, _, _, _, hradius⟩ := hcut m
  have hE : 1 ≤ radialE (D.cellIndex j) :=
    Real.one_le_exp_iff.mpr (Radial.radialQ_nonneg _)
  refine ⟨j, hcell, ?_, fun i hi P a b hab hsub => ?_⟩
  · exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hE (neg_le_neg (le_max_right _ _)))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans hradius
  · obtain ⟨hineg, hisub⟩ := n06_cutHalf_open_subset_component h m hi
    have hphys := hmass j (K.physicalLeft i) (K.physicalRight i)
      (h.2.2.2.2.2.2.2.1 i).1 (n06_cutPiece_closed_subset h m hi) (hisub.trans hcell)
    exact (P.reciprocal_mass_le_physical hT hS h hineg hab hsub).trans
      (hphys.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hE (le_max_left _ _)) hQ.le))

end ContinuousFlexibility.Statements
