import ContinuousFlexibility.Analysis.N06ReferenceNegativeMassBounds
import ContinuousFlexibility.Analysis.N06ReferenceNegativeODE
import ContinuousFlexibility.Analysis.N06ShortODEQuantitative
import ContinuousFlexibility.Analysis.SpacesTraceRestriction

/-!
# Root curvature forced by the selected negative reference atlas

The actual negative reference height satisfies the ODE estimate supplied
by N04.  Its reciprocal mass and cut radius are controlled by the original
physical return-margin cell.  The explicit short-interval estimate then
bounds the reciprocal height at the root and hence the actual physical
root curvature.

Both indices are retained: the ODE coefficient uses `K.cell i`, while the
mass uses the physical cell containing the negative component.  No
identification or comparison between those labels is assumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

private theorem n06_cutHalf_canonical_interval
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) {i : ℕ} (hi : i = (K.cutPair m).1 ∨ i = (K.cutPair m).2) :
    K.positive i = false ∧ K.left i = 0 ∧ K.right i = K.cutRadius m := by
  have hcut := h.2.2.2.2.1.2.1.1.1
  obtain ⟨hnegL, hnegR, _, _, _, _, hlL, hlR, hrL, hrR⟩ := hcut m
  rcases hi with rfl | rfl
  · exact ⟨hnegL, hlL, hrL⟩
  · exact ⟨hnegR, hlR, hrR⟩

/-- The reciprocal root height has a polynomial lower bound for the
actual chosen atlas, using the two original cell labels separately. -/
theorem n06_referenceNegative_root_height_lower
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    ∃ B Q A M : ℝ, 1 ≤ B ∧ 0 < Q ∧ 0 < A ∧ 0 < M ∧
      ∀ m, ∃ j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
        ∀ i, i = (K.cutPair m).1 ∨ i = (K.cutPair m).2 →
          ∀ P : N06ReferenceNegativeInverseData C K i,
          (64 * B * Q * (1 + M * T.E0 (T.sample (K.cell i)) ^ M) ^ 2 *
            (radialE (D.cellIndex j) ^ A) ^ 3)⁻¹ ≤ P.reciprocalHeight 0 := by
  obtain ⟨B, hB, hupper⟩ := n06_referenceNegative_reciprocalHeight_upper hT hS h
  obtain ⟨Q, A, hQ, hA, hmass⟩ := n06_referenceNegative_cut_mass_bounds hT hS h
  obtain ⟨M, hM, hdd⟩ :=
    n06_referenceNegative_reciprocalHeight_secondDerivative_bound hT hS h
  refine ⟨B, Q, A, M, hB, hQ, hA, hM, fun m => ?_⟩
  obtain ⟨j, hcell, hradius, hmassm⟩ := hmass m
  refine ⟨j, hcell, fun i hi P => ?_⟩
  obtain ⟨hineg, hleft, hright⟩ := n06_cutHalf_canonical_interval h m hi
  have hEin : 1 ≤ radialE (D.cellIndex j) :=
    Real.one_le_exp_iff.mpr (Radial.radialQ_nonneg _)
  have hEpos : 0 < radialE (D.cellIndex j) := Real.exp_pos _
  have hE : 1 ≤ radialE (D.cellIndex j) ^ A := Real.one_le_rpow hEin hA.le
  have hE0 : 0 < T.E0 (T.sample (K.cell i)) :=
    (hT.2.1 _ (spaces_trace_sample_mem h.1.1.1.1.1 hT (K.cell i))).2.2.1
  have hcoef : 0 ≤ M * T.E0 (T.sample (K.cell i)) ^ M :=
    (mul_pos hM (Real.rpow_pos_of_pos hE0 _)).le
  have hrad : (1 / 2 : ℝ) * (radialE (D.cellIndex j) ^ A)⁻¹ ≤ K.cutRadius m := by
    simpa only [Real.rpow_neg hEpos.le] using hradius
  have hsub (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (K.cutRadius m)) :
      x ∈ Icc (K.left i) (K.right i) := by
    simpa only [hleft, hright] using hx
  apply n06_positive_closed_endpoint_polynomial_lower
    (zero_lt_one.trans_le hB) hQ hE hcoef hrad
  · intro x hx
    exact (P.reciprocalHeight_regular hT hS h hineg (hsub x hx)).1.of_le (by simp)
  · intro x hx
    exact (P.reciprocalHeight_regular hT hS h hineg (hsub x hx)).2
  · intro x hx
    exact hdd i hineg P x (hsub x hx)
  · intro x hx hxpos
    exact hupper i hineg P x (hsub x hx) hxpos
  · intro t ht htR
    exact hmassm i hi P 0 t ht (fun x hx => hsub x ⟨hx.1, hx.2.trans htR⟩)

/-- The true inverse sends the canonical root to the physical root, so
the already proved normalization gives this exact reciprocal-height form. -/
theorem N06ReferenceNegativeInverseData.reciprocalHeight_root_curvature
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (P : N06ReferenceNegativeInverseData C K i)
    {r : ℝ} (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i))
    (hroot : deriv D.w r = 0) :
    |deriv (deriv D.w) r| * D.w r ^ 2 = r * P.reciprocalHeight 0 ^ 6 := by
  have hYzero : n06ReferenceNegativeY C K i r = 0 :=
    n05_negative_reference_root_image hT hS h hi (x := (r, 0)) hr hroot
  have hinverse : P.inverse 0 = r := by
    simpa only [hYzero] using P.left_inverse r hr
  have hWzero : P.reciprocalHeight 0 = (n06ReferenceNegativeH C K i r)⁻¹ := by
    change (n06ReferenceNegativeH C K i (P.inverse 0))⁻¹ = _
    rw [hinverse]
  have hH : 0 < n06ReferenceNegativeH C K i r :=
    (n06_reference_negative_height_normalization hT hS h hi hr).2.2.1
  have hcurv := n06_reference_negative_root_curvature hT hS h hi hr hroot
  rw [hWzero]
  calc
    |deriv (deriv D.w) r| * D.w r ^ 2 =
        (|deriv (deriv D.w) r| * n06ReferenceNegativeH C K i r ^ 6 * D.w r ^ 2) *
          (n06ReferenceNegativeH C K i r)⁻¹ ^ 6 := by
      field_simp [hH.ne']
      <;> ring
    _ = r * (n06ReferenceNegativeH C K i r)⁻¹ ^ 6 := by rw [hcurv]

private theorem n06_scalar_curvature_lower
    {κ r w W a B d : ℝ}
    (ha : 0 < a) (hB : 0 < B) (hd : 0 < d) (har : a ≤ r)
    (hw : w ^ 2 ≤ B ^ 2) (hκ : 0 ≤ κ) (hW : d⁻¹ ≤ W)
    (hcurv : κ * w ^ 2 = r * W ^ 6) :
    a / (B ^ 2 * d ^ 6) ≤ κ := by
  have hpow : (d⁻¹) ^ 6 ≤ W ^ 6 := pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hW 6
  have hlow : a * (d⁻¹) ^ 6 ≤ κ * B ^ 2 := by
    calc
      a * (d⁻¹) ^ 6 ≤ r * W ^ 6 :=
        mul_le_mul har hpow (pow_nonneg (inv_nonneg.mpr hd.le) _) (ha.le.trans har)
      _ = κ * w ^ 2 := hcurv.symm
      _ ≤ κ * B ^ 2 := mul_le_mul_of_nonneg_left hw hκ
  have hcancel : (d⁻¹) ^ 6 * d ^ 6 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hd.ne', one_pow]
  apply (div_le_iff₀ (mul_pos (pow_pos hB _) (pow_pos hd _))).mpr
  calc
    a = (a * (d⁻¹) ^ 6) * d ^ 6 := by rw [mul_assoc, hcancel, mul_one]
    _ ≤ (κ * B ^ 2) * d ^ 6 :=
      mul_le_mul_of_nonneg_right hlow (pow_nonneg hd.le _)
    _ = κ * (B ^ 2 * d ^ 6) := by ring

private theorem n06_root_lower_denominator (a b q k e : ℝ) :
    (a / (b ^ 2 * q ^ 6)) / ((1 + k) ^ 12 * e ^ 18) =
      a / (b ^ 2 * (q * (1 + k) ^ 2 * e ^ 3) ^ 6) := by
  rw [div_div]
  congr 1
  simp only [mul_pow, ← pow_mul]
  <;> norm_num
  <;> ring

/-- Original N01--N04 data force a quantitative nonzero physical root
curvature.  The estimate retains its true physical and canonical weights;
it does not presume a relation between their cell indices. -/
theorem n06_referenceNegative_root_curvature_lower
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    ∃ c A M : ℝ, 0 < c ∧ 0 < A ∧ 0 < M ∧ ∀ m, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      ∀ i, i = (K.cutPair m).1 ∨ i = (K.cutPair m).2 →
        ∀ r ∈ Icc (K.physicalLeft i) (K.physicalRight i), deriv D.w r = 0 →
        c / ((1 + M * T.E0 (T.sample (K.cell i)) ^ M) ^ 12 *
          (radialE (D.cellIndex j) ^ A) ^ 18) ≤ |deriv (deriv D.w) r| := by
  obtain ⟨B, Q, A, M, hB, hQ, hA, hM, hheight⟩ :=
    n06_referenceNegative_root_height_lower hT hS h
  have hgeom : RadialProfileGeometry D := h.1.1.1.1.1.choose_spec.1
  obtain ⟨B0, hB0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hgeom.2.2.1.1.continuous.continuousOn : ContinuousOn D.w (Icc D.a D.b))
  let Bw : ℝ := max 1 B0
  have hBw : 0 < Bw := zero_lt_one.trans_le (le_max_left _ _)
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let q : ℝ := 64 * B * Q
  have hq : 0 < q := mul_pos (mul_pos (by norm_num) hBp) hQ
  let c : ℝ := D.a / (Bw ^ 2 * q ^ 6)
  have hc : 0 < c := div_pos hgeom.1 (mul_pos (pow_pos hBw _) (pow_pos hq _))
  refine ⟨c, A, M, hc, hA, hM, fun m => ?_⟩
  obtain ⟨j, hcell, hj⟩ := hheight m
  refine ⟨j, hcell, fun i hi r hr hroot => ?_⟩
  have hineg := (n06_cutHalf_canonical_interval h m hi).1
  obtain ⟨P⟩ := n06_referenceNegativeInverseData_nonempty hT hS h hineg
  have hcore : r ∈ radialCore D := n06_cutPiece_closed_subset h m hi hr
  have hwB0 : |D.w r| ≤ B0 := by
    simpa only [Real.norm_eq_abs] using hB0 r ⟨hcore.1.le, hcore.2.le⟩
  have hwB : |D.w r| ≤ Bw := hwB0.trans (le_max_right _ _)
  have hw2 : D.w r ^ 2 ≤ Bw ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (D.w r)) hwB 2
  have hE0 : 0 < T.E0 (T.sample (K.cell i)) :=
    (hT.2.1 _ (spaces_trace_sample_mem h.1.1.1.1.1 hT (K.cell i))).2.2.1
  let k : ℝ := M * T.E0 (T.sample (K.cell i)) ^ M
  let e : ℝ := radialE (D.cellIndex j) ^ A
  have hk : 0 < 1 + k := by
    have hkp : 0 < k := mul_pos hM (Real.rpow_pos_of_pos hE0 _)
    linarith only [hkp]
  have he : 0 < e := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hd : 0 < q * (1 + k) ^ 2 * e ^ 3 :=
    mul_pos (mul_pos hq (pow_pos hk _)) (pow_pos he _)
  have hW : (q * (1 + k) ^ 2 * e ^ 3)⁻¹ ≤ P.reciprocalHeight 0 := hj i hi P
  have hcurv := P.reciprocalHeight_root_curvature hT hS h hineg hr hroot
  have hbound := n06_scalar_curvature_lower hgeom.1 hBw hd hcore.1.le hw2
    (abs_nonneg _) hW hcurv
  calc
    c / ((1 + M * T.E0 (T.sample (K.cell i)) ^ M) ^ 12 *
        (radialE (D.cellIndex j) ^ A) ^ 18) =
        D.a / (Bw ^ 2 * (q * (1 + k) ^ 2 * e ^ 3) ^ 6) :=
      n06_root_lower_denominator D.a Bw q k e
    _ ≤ |deriv (deriv D.w) r| := hbound

end ContinuousFlexibility.Statements
