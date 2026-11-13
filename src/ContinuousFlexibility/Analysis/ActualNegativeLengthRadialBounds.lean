import ContinuousFlexibility.Analysis.N06ReferenceTravelBounds
import ContinuousFlexibility.Analysis.N04bActualTypedAtlas

/-!
# Length costs of the actual optical halves before N04

The original return margin supplies a true component host, a travel lower
bound and an optical-speed upper bound. The chosen reference cut bisects
that same travel. Both physical half-widths and the actual canonical root
radius therefore have polynomial costs at that host. No Through04 or
primitive certificate is used, and this host is not identified with the
cell stored by the typed atlas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements

private theorem actual_halfTravel_inverseWidth
    {M A E l r t : ℝ} {v : ℝ → ℝ}
    (hE : 0 < E) (hlr : l < r) (hv : ContinuousOn v (Icc l r))
    (hbound : ∀ x ∈ Icc l r, v x ≤ M * E ^ A)
    (htravel : (∫ x in l..r, v x) = t / 2)
    (hlower : E ^ (-A) ≤ t) :
    (r - l)⁻¹ ≤ 2 * M * E ^ (2 * A) := by
  have hi := hv.intervalIntegrable_of_Icc (μ := volume) hlr.le
  have hc : IntervalIntegrable (fun _ : ℝ => M * E ^ A) volume l r :=
    intervalIntegrable_const
  have hint := intervalIntegral.integral_mono_on hlr.le hi hc hbound
  rw [htravel, intervalIntegral.integral_const, smul_eq_mul] at hint
  have hbase : E ^ (-A) ≤ 2 * (r - l) * M * E ^ A := by
    nlinarith only [hlower, hint]
  have hcancel : E ^ (-A) * E ^ A = 1 := by
    rw [← Real.rpow_add hE, neg_add_cancel, Real.rpow_zero]
  rw [← one_div]
  apply (div_le_iff₀ (sub_pos.mpr hlr)).mpr
  calc
    1 = E ^ (-A) * E ^ A := hcancel.symm
    _ ≤ (2 * (r - l) * M * E ^ A) * E ^ A :=
      mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hE.le _)
    _ = (2 * M * E ^ (2 * A)) * (r - l) := by
      rw [show 2 * A = A + A by ring, Real.rpow_add hE]
      ring

private theorem actual_rootCutRadius_cost
    {E A t : ℝ} (hE : 1 ≤ E) (hA : 0 < A) (ht : 0 < t)
    (hlower : E ^ (-A) ≤ t) :
    n04bRootCutRadius t ≤ 1 + t ∧
      (n04bRootCutRadius t)⁻¹ ≤ 2 * E ^ A := by
  let R := n04bRootCutRadius t
  have hR : 0 < R := n04bRootCutRadius_pos ht
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hupper : R ≤ 1 + t := by
    change (3 * t / 4) ^ (2 / 3 : ℝ) ≤ 1 + t
    by_cases hsmall : 3 * t / 4 ≤ 1
    · exact (Real.rpow_le_one (by positivity) hsmall (by norm_num)).trans
        (le_add_of_nonneg_right ht.le)
    · have hpow := Real.rpow_le_self_of_one_le
        (le_of_lt (lt_of_not_ge hsmall)) (show (2 / 3 : ℝ) ≤ 1 by norm_num)
      linarith only [hpow, ht]
  have hlowerR : (1 / 2 : ℝ) * E ^ (-A) ≤ R := by
    by_cases hsmall : R ≤ 1
    · have hpow : R ^ (3 / 2 : ℝ) ≤ R :=
        Real.rpow_le_self_of_le_one hR.le hsmall (by norm_num)
      have htime : n04bRootTravel R ≤ R := by
        change (2 / 3 : ℝ) * R ^ (3 / 2 : ℝ) ≤ R
        nlinarith only [hpow, hR]
      have htime' : t / 2 ≤ R := by
        rw [← n04b_rootTravel_cut ht]
        exact htime
      linarith only [hlower, htime']
    · have hpow : E ^ (-A) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hE (neg_nonpos.mpr hA.le)
      linarith only [hpow, hsmall]
  have hpositive : 0 < (1 / 2 : ℝ) * E ^ (-A) := by positivity
  have hinverse := inv_anti₀ hpositive hlowerR
  have halgebra : ((1 / 2 : ℝ) * E ^ (-A))⁻¹ = 2 * E ^ A := by
    rw [mul_inv_rev, Real.rpow_neg hEpos.le, inv_inv]
    norm_num <;> ring
  exact ⟨hupper, hinverse.trans_eq halgebra⟩

/-- Four actual length costs on each original negative half, measured at
the genuine return-margin host. This statement uses only Through03. -/
theorem n04b_actual_negative_radial_length_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε) :
    let cut := n04bActualReferenceCut hN
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧ ∀ side : Bool,
        (n04bNegativeRight C cut (m, side) - n04bNegativeLeft C cut (m, side))⁻¹ ≤
          B * radialE (D.cellIndex j) ^ A ∧
        n04bNegativeRight C cut (m, side) - n04bNegativeLeft C cut (m, side) ≤
          B * radialE (D.cellIndex j) ^ A ∧
        (n04bRootCutRadius (C.travel m))⁻¹ ≤ B * radialE (D.cellIndex j) ^ A ∧
        n04bRootCutRadius (C.travel m) ≤ B * radialE (D.cellIndex j) ^ A := by
  dsimp only
  let cut := n04bActualReferenceCut hN
  have hD : RadialProfileGeometry D := n04b_profileGeometry_of_through03 hN
  have hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  obtain ⟨M, A, hM, hA, hbounds⟩ :=
    n06_return_component_travel_bounds hN.1.1.1.1 hN.1.1.1.2.2.1
  let V := D.b - D.a
  have hV : 0 < V := sub_pos.mpr hD.2.1
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hVM : 0 ≤ V * M := mul_nonneg hV.le hMpos.le
  let B := V + 2 * M + (1 + V * M) + 2
  have hB : 0 < B := by dsimp only [B]; positivity
  have hVB : V ≤ B := by dsimp only [B]; linarith only [hV, hMpos, hVM]
  have h2MB : 2 * M ≤ B := by dsimp only [B]; linarith only [hV, hMpos, hVM]
  have hRcoef : 1 + V * M ≤ B := by dsimp only [B]; linarith only [hV, hMpos]
  have h2B : (2 : ℝ) ≤ B := by dsimp only [B]; linarith only [hV, hMpos, hVM]
  refine ⟨B, 2 * A, hB, by positivity, ?_⟩
  intro m
  have hneg : NegativeRadialComponent D (C.left m) (C.right m) :=
    ⟨(hC.1 m).1, (hC.1 m).2.1, (hC.1 m).2.2,
      (hC.2.1 m).1, (hC.2.1 m).2.1, hC.2.2.2.1 m⟩
  obtain ⟨j, hj, htravel, hspeed⟩ := hbounds (C.left m) (C.right m) hneg
  let E := radialE (D.cellIndex j)
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (Radial.radialQ_nonneg _)
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hTpos : 0 < C.travel m := n04b_referenceTravel_pos hD hC m
  have hwhole : (∫ x in C.left m..C.right m, opticalSpeed D.w x) = C.travel m :=
    n04b_referenceTravel_right hC m
  have htlower : E ^ (-A) ≤ C.travel m := by
    change E ^ (-A) ≤ (∫ x in C.left m..C.right m, opticalSpeed D.w x) at htravel
    rwa [hwhole] at htravel
  have hcut := n04bReferenceTravelCut_spec hD hC m
  change cut m ∈ Ioo (C.left m) (C.right m) ∧
    opticalTravel D.w (C.left m) (cut m) = C.travel m / 2 at hcut
  have hv := n04b_referenceOpticalSpeed_continuousOn hD hC m
  have hvL := hv.mono (Icc_subset_Icc le_rfl hcut.1.2.le)
  have hvR := hv.mono (Icc_subset_Icc hcut.1.1.le le_rfl)
  have hil := hvL.intervalIntegrable_of_Icc (μ := volume) hcut.1.1.le
  have hir := hvR.intervalIntegrable_of_Icc (μ := volume) hcut.1.2.le
  have hleft : (∫ x in C.left m..cut m, opticalSpeed D.w x) = C.travel m / 2 := hcut.2
  have hright : (∫ x in cut m..C.right m, opticalSpeed D.w x) = C.travel m / 2 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals hil hir
    rw [hwhole, hleft] at hadd
    linarith only [hadd]
  have hleftInv := actual_halfTravel_inverseWidth hEpos hcut.1.1 hvL
    (fun x hx => hspeed x ⟨hx.1, hx.2.trans hcut.1.2.le⟩) hleft htlower
  have hrightInv := actual_halfTravel_inverseWidth hEpos hcut.1.2 hvR
    (fun x hx => hspeed x ⟨hcut.1.1.le.trans hx.1, hx.2⟩) hright htlower
  have hME : 0 ≤ M * E ^ A := mul_nonneg hMpos.le (Real.rpow_nonneg hEpos.le _)
  have hphysicalWidth : C.right m - C.left m ≤ V := by
    dsimp only [V]
    linarith only [(hC.1 m).1, (hC.1 m).2.2]
  have htravelUpper : C.travel m ≤ V * M * E ^ A := by
    have hc : IntervalIntegrable (fun _ : ℝ => M * E ^ A) volume (C.left m) (C.right m) :=
      intervalIntegrable_const
    have hint := intervalIntegral.integral_mono_on (hC.1 m).2.1.le
      (hv.intervalIntegrable_of_Icc (hC.1 m).2.1.le) hc hspeed
    rw [hwhole, intervalIntegral.integral_const, smul_eq_mul] at hint
    exact hint.trans ((mul_le_mul_of_nonneg_right hphysicalWidth hME).trans_eq (by ring))
  have hpower : E ^ A ≤ E ^ (2 * A) :=
    Real.rpow_le_rpow_of_exponent_le hE (by linarith only [hA])
  have hone : 1 ≤ E ^ (2 * A) := Real.one_le_rpow hE (by positivity)
  have hE2 : 0 ≤ E ^ (2 * A) := Real.rpow_nonneg hEpos.le _
  obtain ⟨hRupper, hRinverse⟩ := actual_rootCutRadius_cost hE hA hTpos htlower
  have hcanonical : n04bRootCutRadius (C.travel m) ≤ B * E ^ (2 * A) := by
    calc
      _ ≤ 1 + C.travel m := hRupper
      _ ≤ 1 + V * M * E ^ A := add_le_add le_rfl htravelUpper
      _ ≤ E ^ (2 * A) + V * M * E ^ (2 * A) :=
        add_le_add hone (mul_le_mul_of_nonneg_left hpower hVM)
      _ = (1 + V * M) * E ^ (2 * A) := by ring
      _ ≤ B * E ^ (2 * A) := mul_le_mul_of_nonneg_right hRcoef hE2
  have hcanonicalInv : (n04bRootCutRadius (C.travel m))⁻¹ ≤ B * E ^ (2 * A) :=
    hRinverse.trans ((mul_le_mul_of_nonneg_left hpower (by norm_num)).trans
      (mul_le_mul_of_nonneg_right h2B hE2))
  refine ⟨j, hj, ?_⟩
  intro side
  have hh := n04b_negativeHalf_bounds hC (n04bActualReferenceCut_mem hN) (m, side)
  have hwidth : n04bNegativeRight C cut (m, side) - n04bNegativeLeft C cut (m, side) ≤ V := by
    dsimp only [V]
    linarith only [hh.1, hh.2.2]
  have hinv :
      (n04bNegativeRight C cut (m, side) - n04bNegativeLeft C cut (m, side))⁻¹ ≤
        2 * M * E ^ (2 * A) := by
    cases side
    · simpa only [n04bNegativeLeft, n04bNegativeRight, Bool.false_eq_true, ite_false] using hleftInv
    · simpa only [n04bNegativeLeft, n04bNegativeRight, ite_true] using hrightInv
  refine ⟨hinv.trans (mul_le_mul_of_nonneg_right h2MB hE2), ?_, hcanonicalInv, hcanonical⟩
  exact hwidth.trans (hVB.trans ((mul_one B).symm.trans_le
    (mul_le_mul_of_nonneg_left hone hB.le)))

end ContinuousFlexibility.Analysis
