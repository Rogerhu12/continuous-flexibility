import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Radial.RadialHeight
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The actual nonlinear return at the radial reference

The reference profile and height are evaluated from the frozen state formulas.
Their actual scalar coefficients determine the ordinary characteristic speed.
The fundamental theorem of calculus then identifies the return map and proves
that the return residual vanishes.  The correction operator consequently agrees
with the original operator on every height-space test.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

theorem n05_referenceState_mem (hε : 0 < ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
  change stateGrading S base (C.referenceState - C.referenceState) < ε ∧
    |(0 : ℝ)| < ε
  constructor
  · calc
      stateGrading S base (C.referenceState - C.referenceState) =
          stateGrading S base (0 : AnnularState S) :=
        congrArg (fun x : AnnularState S => stateGrading S base x)
          (sub_self C.referenceState)
      _ = 0 := (stateGrading S base).map_zero'
      _ < ε := hε
  · exact lt_of_eq_of_lt (abs_zero : |(0 : ℝ)| = 0) hε

theorem n05_referenceState_sector (hC : referenceStateConditions D S C) :
    stateSector S C.referenceState := by
  rcases hC with ⟨_, _, _, hκ, hα, _⟩
  simp [stateSector, hκ, hα]

theorem n05_stateProfile_reference (hC : referenceStateConditions D S C) :
    stateProfile D S C C.referenceState = D.w := by
  rcases hC with ⟨_, _, hμ, hκ, _, _⟩
  funext r
  simp [stateProfile, stateKappa, angularMean, hμ, hκ]

theorem n05_stateLeftChart_reference (hC : referenceStateConditions D S C)
    (m : ℕ) (θ : ℝ) :
    stateLeftChart S C.referenceState m θ = θ := by
  rcases hC with ⟨_, _, _, _, hα, _⟩
  simp [stateLeftChart, hα]

theorem n05_stateHeight_reference (hC : referenceStateConditions D S C) :
    stateHeight D S C (C.referenceState, 0) =
      Radial.radialHeightField (fun r => ∫ t in D.b..r, D.w t) := by
  funext p
  simp only [stateHeight, stateRadialHeight, n05_stateProfile_reference hC,
    zero_mul, add_zero, Radial.radialHeightField]

/-- These are the coefficients of the actual scalar operator, obtained by
differentiating the reference primitive rather than postulated radial jets. -/
theorem n05_originalCoefficients_reference (hD : IsAccumulatingProfile D)
    (hC : referenceStateConditions D S C) (p : PolarPoint) :
    (originalCoefficients D S C (C.referenceState, 0)).a p = D.w p.1 ∧
      (originalCoefficients D S C (C.referenceState, 0)).b p = 0 ∧
      (originalCoefficients D S C (C.referenceState, 0)).c p =
        deriv D.w p.1 / p.1 := by
  obtain ⟨B, hB⟩ := hD
  have hw : ContDiff ℝ ∞ D.w := hB.1.2.2.1.1
  let h : ℝ → ℝ := fun r => ∫ t in D.b..r, D.w t
  have hhw (r : ℝ) : HasDerivAt h (D.w r) r :=
    (hw.continuous.integral_hasStrictDerivAt D.b r).hasDerivAt
  have hprofile := n05_stateProfile_reference hC
  have hheight : stateHeight D S C (C.referenceState, 0) =
      Radial.radialHeightField h := n05_stateHeight_reference hC
  have hscale : polarScale D.w (Radial.radialHeightField h) p = 1 := by
    rw [polarScale, Radial.polarDiscriminant_radialHeightField hhw,
      inverseDThreeHalves_one]
  have hr := Radial.heightRadial_radialHeightField hhw
  have hθ := Radial.heightAngular_radialHeightField hhw
  have hdw := hw.differentiable (by simp) p.1
  constructor
  · change polarLinearA _ _ p = _
    rw [hprofile, hheight]
    simp only [polarLinearA, hr, hθ, angularPartial_const, hscale,
      linearRadial, heightQ, Radial.radialHeightField, mul_zero, add_zero, mul_one]
  constructor
  · change polarLinearB _ _ p = _
    rw [hprofile, hheight]
    simp only [polarLinearB, hθ, radialPartial_const, linearMixed, mul_zero, zero_mul]
  · change polarCorrectedC _ _ p = _
    rw [hprofile, hheight, polarCorrectedC_eq_residual_correction,
      Radial.polarCoordinateResidual_radialHeightField hhw hdw]
    simp only [mul_zero, zero_div, sub_zero]
    rw [polarLinearC, hr, Radial.radialPartial_radialHeightField hdw,
      radialPartial_profileEnergy hdw, hscale]
    change linearAngular p.1 (radialEnergy (D.w p.1)) (2 * D.w p.1 * deriv D.w p.1)
      (D.w p.1) (deriv D.w p.1) 1 = deriv D.w p.1 / p.1
    simpa only [heightDiscriminant_radial, inverseDThreeHalves_one] using
      (radial_linear_coefficients p.1 (D.w p.1) (deriv D.w p.1)).2.2

/-- The reference characteristic speed is independent of the angle. -/
theorem n05_minusCharacteristicSpeed_reference (hD : IsAccumulatingProfile D)
    (hC : referenceStateConditions D S C) {p : PolarPoint}
    (hp : p ∈ annularOpen D) :
    minusCharacteristicSpeed (originalCoefficients D S C (C.referenceState, 0)) p =
      -Real.sqrt (-deriv D.w p.1 / (p.1 * D.w p.1)) := by
  obtain ⟨B, hB⟩ := hD
  have hr : 0 < p.1 := hB.1.1.trans hp.1.1
  have hw : 0 < D.w p.1 := hB.1.2.2.2.2.1 p.1 hp.1
  obtain ⟨ha, hb, hc⟩ := n05_originalCoefficients_reference ⟨B, hB⟩ hC p
  have hratio : (0 - D.w p.1 * (deriv D.w p.1 / p.1)) / D.w p.1 ^ 2 =
      -deriv D.w p.1 / (p.1 * D.w p.1) := by
    field_simp [hw.ne', hr.ne']
    <;> ring
  have hsqrt : Real.sqrt (0 - D.w p.1 * (deriv D.w p.1 / p.1)) / D.w p.1 =
      Real.sqrt (-deriv D.w p.1 / (p.1 * D.w p.1)) := by
    calc
      _ = Real.sqrt ((0 - D.w p.1 * (deriv D.w p.1 / p.1)) / D.w p.1 ^ 2) := by
        rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hw.le]
      _ = _ := congrArg Real.sqrt hratio
  simp only [minusCharacteristicSpeed, ha, hb, hc, zero_div, pow_two, mul_zero]
  rw [hsqrt]
  ring

/-- Integrating the ordinary reference flow gives its actual return. -/
theorem n05_minusFlow_reference_return
    (h01 : N01Properties D T S C base loss ε) (m : ℕ) (θ : ℝ) :
    C.minusFlow (C.referenceState, 0) m (C.right m) θ = θ - C.travel m := by
  rcases h01 with ⟨hD, hε, hC, hgeom, _, _, hflow, _⟩
  rcases hgeom with ⟨hinterval, _, _, _, _, _, _, htravel, _⟩
  obtain ⟨B, hB⟩ := hD.1
  have hw : ContDiff ℝ ∞ D.w := hB.1.2.2.1.1
  have hcore (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
      r ∈ radialCore D :=
    ⟨(hinterval m).1.trans_le hr.1, hr.2.trans_lt (hinterval m).2.2⟩
  have hden (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
      r * D.w r ≠ 0 :=
    (mul_pos (hB.1.1.trans (hcore r hr).1)
      (hB.1.2.2.2.2.1 r (hcore r hr))).ne'
  have hspeed : ContinuousOn (fun r : ℝ =>
      -Real.sqrt (-deriv D.w r / (r * D.w r))) (Icc (C.left m) (C.right m)) :=
    (Real.continuous_sqrt.comp_continuousOn
      (((hw.continuous_deriv (by simp)).neg.continuousOn).div
        (continuous_id.mul hw.continuous).continuousOn hden)).neg
  have hint : IntervalIntegrable (fun r : ℝ =>
      -Real.sqrt (-deriv D.w r / (r * D.w r))) volume (C.left m) (C.right m) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (hinterval m).2.1.le] using hspeed
  obtain ⟨hstart, hcont, hderiv, _⟩ :=
    hflow (C.referenceState, 0) (n05_referenceState_mem hε) m θ
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (hinterval m).2.1.le hcont
    (fun r hr => (hderiv r hr).congr_deriv
      (n05_minusCharacteristicSpeed_reference ⟨B, hB⟩ hC
        (show (r, C.minusFlow (C.referenceState, 0) m r θ) ∈ annularOpen D from
          ⟨hcore r ⟨hr.1.le, hr.2.le⟩, Set.mem_univ _⟩))) hint
  rw [intervalIntegral.integral_neg, ← htravel m, hstart] at heq
  linarith only [heq]

theorem n05_minusReturnInverse_reference
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε) (m : ℕ) (θ : ℝ) :
    C.minusReturnInverse (C.referenceState, 0) m θ = θ + C.travel m := by
  have hε := h01.2.1
  have hC := h01.2.2.1
  have hi := (h02.1 (C.referenceState, 0) (n05_referenceState_mem hε)
    (n05_referenceState_sector hC) m θ).1
  rw [n05_minusFlow_reference_return h01] at hi
  linarith only [hi]

theorem n05_rightChart_reference
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε) (m : ℕ) (θ : ℝ) :
    rightChartCandidate S C (C.referenceState, 0) m θ = θ := by
  simp only [rightChartCandidate, oddPart, n05_stateLeftChart_reference h01.2.2.1,
    n05_minusReturnInverse_reference h01 h02, add_sub_cancel_right]
  ring

/-- The zero return residual is forced by N01 and N02 at the actual reference. -/
theorem n05_returnResidual_reference_zero
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε) :
    R.residual (C.referenceState, 0) = 0 := by
  apply (h02.2.2.1 (C.referenceState, 0) (n05_referenceState_mem h01.2.1)
    (n05_referenceState_sector h01.2.2.1)).2
  intro m θ
  constructor
  · simp only [n05_rightChart_reference h01 h02,
      n05_minusFlow_reference_return h01, n05_stateLeftChart_reference h01.2.2.1]
  · simp only [n05_rightChart_reference h01 h02,
      n05_minusFlow_reference_return h01, n05_stateLeftChart_reference h01.2.2.1]
    ring

/-- The bilinear error vanishes at any state with zero return residual. -/
theorem n05_correctionOperator_of_residual_zero
    (h03 : N03Properties D T S C R L base ε) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hres : R.residual z = 0) (η : HeightPair S) {p : PolarPoint}
    (hp : p ∈ annularOpen D) :
    divergenceOperator (originalCoefficients D S C z) (heightPairField S η) p =
      divergenceOperator (L.coefficients z) (heightPairField S η) p := by
  have h := h03.2.2.2.2.2.1 z hz hs η p hp
  apply sub_eq_zero.mp
  simpa [hres] using h

/-- The actual corrected reference operator agrees with the actual original
operator on every height-pair test, with no added reference normalization. -/
theorem n05_reference_correctionOperator_eq
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (η : HeightPair S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (originalCoefficients D S C (C.referenceState, 0))
        (heightPairField S η) p =
      divergenceOperator (L.coefficients (C.referenceState, 0))
        (heightPairField S η) p :=
  n05_correctionOperator_of_residual_zero h.2
    (n05_referenceState_mem h.1.1.2.1)
    (n05_referenceState_sector h.1.1.2.2.1)
    (n05_returnResidual_reference_zero h.1.1 h.1.2) η hp

end ContinuousFlexibility.Statements

