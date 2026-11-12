import ContinuousFlexibility.Analysis.ActualNegativeReferenceSourceSquares
import ContinuousFlexibility.Analysis.MaterialPointRadialPolynomial
import ContinuousFlexibility.Analysis.N01aOpticalProfile

/-!
# Uniform physical costs for the two differentiated reference sources

The exact cancellation of the actual negative source multipliers is
combined with the existing optical-radicand bound on their genuine host
cell. Both the speed and the total travel have a fixed radial coefficient
cost. Evaluating that cost at any physical point of the host preserves
the required E0 envelope, without an absolute optical-root lower bound.
The undifferentiated profile source is not covered by this result.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

private theorem actual_reference_optical_upper
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hRef : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ m j,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ r ∈ Icc (C.left m) (C.right m),
        opticalSpeed D.w r ≤ K * radialE (D.cellIndex j) ^ A) ∧
      C.travel m ≤ (D.b - D.a) * (K * radialE (D.cellIndex j) ^ A) := by
  obtain ⟨B, hB, hb⟩ := n01aOpticalRadicand_component_jets hRef 0
  refine ⟨B + 1, B, by linarith only [hB], hB, ?_⟩
  intro m j hhost
  have hcomp := controlGeometry_negativeRadialComponent hC m
  have hE : 1 ≤ radialE (D.cellIndex j) :=
    Real.one_le_exp_iff.mpr (ContinuousFlexibility.Radial.radialQ_nonneg _)
  have hEB : 1 ≤ radialE (D.cellIndex j) ^ B := Real.one_le_rpow hE hB.le
  have hspeed (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
      opticalSpeed D.w r ≤ (B + 1) * radialE (D.cellIndex j) ^ B := by
    have hq : n01aOpticalRadicand D.w r ≤ B * radialE (D.cellIndex j) ^ B :=
      (le_abs_self _).trans (by simpa only [iteratedDeriv_zero] using
        hb (C.left m) (C.right m) j hcomp hhost r hr)
    have hBE : 0 ≤ B * radialE (D.cellIndex j) ^ B :=
      mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans hE) _)
    have hsqrt : opticalSpeed D.w r ≤ 1 + B * radialE (D.cellIndex j) ^ B := by
      change Real.sqrt (n01aOpticalRadicand D.w r) ≤ _
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith only [hq, hBE, sq_nonneg (B * radialE (D.cellIndex j) ^ B)]
    exact hsqrt.trans (by nlinarith only [hEB])
  refine ⟨hspeed, ?_⟩
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := C.left m) (b := C.right m) (f := opticalSpeed D.w)
    (C := (B + 1) * radialE (D.cellIndex j) ^ B) (fun r hr => by
      rw [uIoc_of_le (hC.1 m).2.1.le] at hr
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
        hspeed r ⟨hr.1.le, hr.2⟩)
  have htravel : C.travel m ≤
      ((B + 1) * radialE (D.cellIndex j) ^ B) * (C.right m - C.left m) := by
    have hnorm : |opticalTravel D.w (C.left m) (C.right m)| ≤
        ((B + 1) * radialE (D.cellIndex j) ^ B) * (C.right m - C.left m) := by
      simpa only [opticalTravel, Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr (hC.1 m).2.1)] using hi
    rw [n04b_referenceTravel_right hC m] at hnorm
    exact (le_abs_self _).trans hnorm
  calc
    C.travel m ≤ _ := htravel
    _ ≤ ((B + 1) * radialE (D.cellIndex j) ^ B) * (D.b - D.a) :=
      mul_le_mul_of_nonneg_left (by linarith only [(hC.1 m).1, (hC.1 m).2.2])
        (mul_nonneg (by linarith only [hB]) (Real.rpow_nonneg (zero_le_one.trans hE) _))
    _ = _ := mul_comm _ _

private theorem abs_le_coefficient_of_square
    {x C E : ℝ} (hC : 0 ≤ C) (hE : 1 ≤ E) (hx : x ^ 2 ≤ C * E) :
    |x| ≤ (C + 1) * E := by
  have hnorm : |x| ≤ 1 + x ^ 2 := by
    nlinarith only [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
  calc
    |x| ≤ 1 + x ^ 2 := hnorm
    _ ≤ 1 + C * E := add_le_add_left hx 1
    _ ≤ (C + 1) * E := by nlinarith only [hE]

/-- The constants precede every actual negative component, host, chart
index and evaluation point. Both bounds use the original reference
height and original reference Jacobian of the actual typed atlas. -/
theorem n04Coordinates_actual_reference_derivativeSource_cell_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m j,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∀ k side, e k = .inl (m, side) →
      ∀ p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
        let a := K.height (C.referenceState, 0) k p /
          |planeJacobian (K.chart (C.referenceState, 0) k) p|
        |a * deriv D.w p.1| ≤ B * radialE (D.cellIndex j) ^ A ∧
          |a * (deriv D.w p.1 / p.1)| ≤ B * radialE (D.cellIndex j) ^ A := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hD : RadialProfileGeometry D := n04b_profileGeometry_of_through03 hN
  have hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  obtain ⟨V, A, hV, hA, hv⟩ := actual_reference_optical_upper hN.1.1.1.1 hC
  have hwcontinuous : ContinuousOn D.w (Icc D.a D.b) :=
    hD.2.2.1.1.continuous.continuousOn
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hwcontinuous
  let M := max M₀ 1
  have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
  have hwbound (r : ℝ) (hr : r ∈ Icc D.a D.b) : D.w r ≤ M :=
    (le_abs_self _).trans ((by simpa only [Real.norm_eq_abs] using hM₀ r hr).trans
      (le_max_left _ _))
  let B₀ := (3 / 2 : ℝ) * M * (D.b - D.a) * V ^ 2
  let B₁ := (1 + D.b ^ 2) * B₀
  have hB₀ : 0 < B₀ := mul_pos (mul_pos (mul_pos (by norm_num) hM)
    (sub_pos.mpr hD.2.1)) (sq_pos_of_pos hV)
  have hB₁ : 0 < B₁ := mul_pos (by positivity) hB₀
  refine ⟨B₁ + 1, 2 * A, by linarith only [hB₁], mul_pos (by norm_num) hA, ?_⟩
  intro m j hhost k side hi p hp
  let E := radialE (D.cellIndex j)
  let v := opticalSpeed D.w p.1
  let t := n04bTravelOrientation (C.travel m) side (opticalTravel D.w (C.left m) p.1)
  have hE : 1 ≤ E :=
    Real.one_le_exp_iff.mpr (ContinuousFlexibility.Radial.radialQ_nonneg _)
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hpD : p.1 ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hp.1.1, hp.1.2.trans (hC.1 m).2.2⟩
  have hw : 0 < D.w p.1 := hD.2.2.2.2.1 p.1 hpD
  have hvpos : 0 < v := n04b_referenceOpticalSpeed_pos hD hC m hp.1
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref : stateSector S C.referenceState := hN.1.1.2.2.1.stateSector
  have htime : opticalTravel D.w (C.left m) p.1 ∈ Ioo (0 : ℝ) (C.travel m) := by
    have hm := (n04b_actualTravelChart_bijOn hN hS hT hfield href hsref m).mapsTo hp
    simpa only [n04b_reference_actualTravelChart hN.1.1.2.2.1 hT hS hN hfield m
      ⟨hp.1.1.le, hp.1.2.le⟩ p.2] using hm.1
  have htpos : 0 < t := n04b_travelOrientation_pos_of_fullStrip side htime
  have htT : t ≤ C.travel m := by
    cases side <;> dsimp only [t, n04bTravelOrientation, Bool.false_eq_true, ↓reduceIte]
    · exact htime.2.le
    · linarith only [htime.1]
  have hvbound : v ≤ V * E ^ A := (hv m j hhost).1 p.1 (Ioo_subset_Icc_self hp.1)
  have htbound : t ≤ (D.b - D.a) * (V * E ^ A) := htT.trans (hv m j hhost).2
  have hEpow : 0 ≤ E ^ A := Real.rpow_nonneg hEpos.le _
  have hEsq : E ^ (2 * A) = (E ^ A) ^ 2 := by
    rw [show 2 * A = A + A by ring, Real.rpow_add hEpos, pow_two]
  have hcost : (3 / 2 : ℝ) * D.w p.1 * v * t ≤ B₀ * E ^ (2 * A) := by
    calc
      _ ≤ (3 / 2 : ℝ) * M * (V * E ^ A) * ((D.b - D.a) * (V * E ^ A)) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left (hwbound p.1 ⟨hpD.1.le, hpD.2.le⟩)
            (by norm_num)) hvbound hvpos.le (mul_nonneg (by norm_num) hM.le))
          htbound htpos.le (mul_nonneg (mul_nonneg (by norm_num) hM.le)
            (mul_nonneg hV.le hEpow))
      _ = _ := by rw [hEsq]; dsimp only [B₀]; ring
  have hB₀B₁ : B₀ ≤ B₁ := by
    dsimp only [B₁]
    nlinarith only [mul_nonneg (sq_nonneg D.b) hB₀.le]
  have hr : 0 < p.1 := hD.1.trans hpD.1
  have hrb : p.1 ^ 2 ≤ 1 + D.b ^ 2 :=
    (pow_le_pow_left₀ hr.le hpD.2.le 2).trans (by linarith)
  have hsquares := n04Coordinates_actual_reference_negative_source_squares
    hT hS hN hfield e k m side hi hp
  have hthirdsq :
      (K.height (C.referenceState, 0) k p /
        |planeJacobian (K.chart (C.referenceState, 0) k) p| *
        (deriv D.w p.1 / p.1)) ^ 2 ≤ B₁ * E ^ (2 * A) := by
    rw [hsquares.1]
    exact hcost.trans (mul_le_mul_of_nonneg_right hB₀B₁
      (Real.rpow_nonneg hEpos.le _))
  have hfirstsq :
      (K.height (C.referenceState, 0) k p /
        |planeJacobian (K.chart (C.referenceState, 0) k) p| * deriv D.w p.1) ^ 2 ≤
      B₁ * E ^ (2 * A) := by
    rw [hsquares.2]
    calc
      _ = p.1 ^ 2 * ((3 / 2 : ℝ) * D.w p.1 * v * t) := by ring
      _ ≤ (1 + D.b ^ 2) * (B₀ * E ^ (2 * A)) :=
        mul_le_mul hrb hcost
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hw.le) hvpos.le) htpos.le)
          (by positivity)
      _ = _ := by dsimp only [B₁]; ring
  have hElarge : 1 ≤ E ^ (2 * A) := Real.one_le_rpow hE (by positivity)
  exact ⟨abs_le_coefficient_of_square hB₁.le hElarge hfirstsq,
    abs_le_coefficient_of_square hB₁.le hElarge hthirdsq⟩

/-- The radial loss is evaluated at an arbitrary genuine physical point
of the host. This is the point used by the final material estimate, not
an imposed replacement by the host's sample. -/
theorem n04Coordinates_actual_reference_derivativeSource_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ B P : ℝ, 0 < B ∧ 0 ≤ P ∧ ∀ m j,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∀ k side, e k = .inl (m, side) →
      ∀ p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ), ∀ r ∈ D.cells j,
        let a := K.height (C.referenceState, 0) k p /
          |planeJacobian (K.chart (C.referenceState, 0) k) p|
        |a * deriv D.w p.1| ≤ B * T.E0 r ^ P ∧
          |a * (deriv D.w p.1 / p.1)| ≤ B * T.E0 r ^ P := by
  obtain ⟨B, A, hB, hA, hb⟩ :=
    n04Coordinates_actual_reference_derivativeSource_cell_bound hT hS hN hfield e
  obtain ⟨V, P, hV, hP, hv⟩ := materialCell_radialE_power_bound hT hN.1.1.1.1 hA.le
  refine ⟨B * V, P, mul_pos hB hV, hP, ?_⟩
  intro m j hhost k side hi p hp r hr
  have hcost : B * radialE (D.cellIndex j) ^ A ≤ (B * V) * T.E0 r ^ P :=
    (mul_le_mul_of_nonneg_left (hv j r hr) hB.le).trans_eq (by ring)
  exact ⟨((hb m j hhost k side hi p hp).1).trans hcost,
    ((hb m j hhost k side hi p hp).2).trans hcost⟩

end ContinuousFlexibility.Analysis
