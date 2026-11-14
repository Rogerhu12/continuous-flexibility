module

public import ContinuousFlexibility.Scalar.Linearization
public import ContinuousFlexibility.Scalar.Normalization

/-!
# Actual coefficients with fixed type-change set

The determinant identity is applied to the real spatial jets of the height
and profile. The correction's sign changes exactly with the profile slope.
The divergence comparison below is a real derivative identity; its stated
differentiability premises must be supplied on the eventual PDE domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def polarTypeB (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  profileEnergy w x /
    (x.1 * heightQ (profileEnergy w x) (heightRadial z x) (angularPartial (heightAngular z) x))

def polarCorrectedC (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  correctedAngular x.1 (profileEnergy w x) (radialPartial (profileEnergy w) x)
    (heightRadial z x) (heightAngular z x) (radialPartial (heightRadial z) x)
    (radialPartial (heightAngular z) x) (angularPartial (heightAngular z) x) (polarScale w z x)

def heightCorrectedDivergence (w : ℝ → ℝ) (z η : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  radialPartial (fun y => polarLinearA w z y * radialPartial η y +
      polarLinearB w z y * angularPartial η y) x +
    angularPartial (fun y => polarLinearB w z y * radialPartial η y +
      polarCorrectedC w z y * angularPartial η y) x

theorem polarCorrectedC_eq_residual_correction
    (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) :
    polarCorrectedC w z x = polarLinearC w z x -
      profileEnergy w x * polarCoordinateResidual w z x /
        heightQ (profileEnergy w x) (heightRadial z x) (angularPartial (heightAngular z) x) := rfl

theorem polarCorrectedC_eq_typeB
    (w : ℝ → ℝ) (z : PolarPoint → ℝ) {x : PolarPoint}
    (hr : x.1 ≠ 0)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    polarCorrectedC w z x = polarLinearC w z x -
      polarTypeB w z x * x.1 * polarCoordinateResidual w z x := by
  rw [polarCorrectedC_eq_residual_correction]
  unfold polarTypeB
  field_simp [hr, hQ]

theorem polarCorrectedC_eq_typeB_total
    (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) :
    polarCorrectedC w z x = polarLinearC w z x -
      polarTypeB w z x * x.1 * polarCoordinateResidual w z x := by
  by_cases hr : x.1 = 0
  · simp [polarCorrectedC_eq_residual_correction, polarTypeB, polarCoordinateResidual, hr]
  by_cases hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) = 0
  · simp [polarCorrectedC_eq_residual_correction, polarTypeB, hQ]
  exact polarCorrectedC_eq_typeB w z hr hQ

theorem polar_corrected_determinant
    {w : ℝ → ℝ} (z : PolarPoint → ℝ) {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    polarLinearA w z x * polarCorrectedC w z x - polarLinearB w z x ^ 2 =
      (w x.1 * deriv w x.1 / x.1) / polarDiscriminant w z x ^ 2 := by
  unfold polarLinearA polarCorrectedC polarLinearB polarScale
  rw [radialPartial_profileEnergy hw]
  exact corrected_determinant x.1 (profileEnergy w x) (w x.1) (deriv w x.1)
    (heightRadial z x) (heightAngular z x) (radialPartial (heightRadial z) x)
    (radialPartial (heightAngular z) x) (angularPartial (heightAngular z) x) hr hD hQ

/-- The determinant's vanishing set is exactly `w' = 0` while `w > 0`.
The height and its residual do not move this set. -/
theorem polar_corrected_determinant_zero_iff
    {w : ℝ → ℝ} (z : PolarPoint → ℝ) {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hr : x.1 ≠ 0) (hwp : 0 < w x.1)
    (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    polarLinearA w z x * polarCorrectedC w z x - polarLinearB w z x ^ 2 = 0 ↔
      deriv w x.1 = 0 := by
  rw [polar_corrected_determinant z hw hr hD hQ]
  simp [div_eq_zero_iff, mul_eq_zero, hwp.ne', hr, hD.ne']

theorem polar_corrected_determinant_pos_iff
    {w : ℝ → ℝ} (z : PolarPoint → ℝ) {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hr : 0 < x.1) (hwp : 0 < w x.1)
    (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    0 < polarLinearA w z x * polarCorrectedC w z x - polarLinearB w z x ^ 2 ↔
      0 < deriv w x.1 := by
  rw [polar_corrected_determinant z hw hr.ne' hD hQ]
  rw [div_pos_iff_of_pos_right (sq_pos_of_pos hD), div_pos_iff_of_pos_right hr,
    mul_pos_iff_of_pos_left hwp]

theorem polar_corrected_determinant_neg_iff
    {w : ℝ → ℝ} (z : PolarPoint → ℝ) {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hr : 0 < x.1) (hwp : 0 < w x.1)
    (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    polarLinearA w z x * polarCorrectedC w z x - polarLinearB w z x ^ 2 < 0 ↔
      deriv w x.1 < 0 := by
  rw [polar_corrected_determinant z hw hr.ne' hD hQ]
  rw [div_lt_iff₀ (sq_pos_of_pos hD), zero_mul, div_lt_iff₀ hr, zero_mul]
  simp [mul_neg_iff, hwp, not_lt_of_ge hwp.le]

/-- Both operators kill constants as genuine functions, without any
differentiability or nonvanishing assumptions on the coefficients. -/
theorem heightCorrectedDivergence_const
    (w : ℝ → ℝ) (z : PolarPoint → ℝ) (c : ℝ) (x : PolarPoint) :
    heightCorrectedDivergence w z (fun _ => c) x = 0 := by
  simp [heightCorrectedDivergence]

/-- Comparison of actual divergences. The radial flux is literally the
same function; only the angular flux contributes an error. -/
theorem heightLinearizedDivergence_eq_corrected
    (w : ℝ → ℝ) (z η : PolarPoint → ℝ) {x : PolarPoint}
    (hflux : DifferentiableAt ℝ (fun y =>
      polarLinearB w z y * radialPartial η y +
        polarCorrectedC w z y * angularPartial η y) x)
    (herr : DifferentiableAt ℝ (fun y =>
      polarTypeB w z y * y.1 * polarCoordinateResidual w z y * angularPartial η y) x) :
    heightLinearizedDivergence w z η x = heightCorrectedDivergence w z η x +
      angularPartial (fun y => polarTypeB w z y * y.1 *
        polarCoordinateResidual w z y * angularPartial η y) x := by
  have heq : (fun y => polarLinearB w z y * radialPartial η y +
      polarLinearC w z y * angularPartial η y) =
      (fun y => (polarLinearB w z y * radialPartial η y +
        polarCorrectedC w z y * angularPartial η y) +
          polarTypeB w z y * y.1 * polarCoordinateResidual w z y * angularPartial η y) := by
    funext y
    rw [polarCorrectedC_eq_typeB_total]
    ring
  unfold heightLinearizedDivergence heightCorrectedDivergence
  rw [heq, angularPartial_add hflux herr]
  ring

/-- Actual coefficient regularity supplies the differentiability required
by the divergence comparison on its geometric admissible domain. -/
theorem contDiffAt_heightLinearCoefficients
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiffAt ℝ ∞ w x.1) (hz : ContDiffAt ℝ ∞ z x) (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    ContDiffAt ℝ ∞ (polarLinearA w z) x ∧
      ContDiffAt ℝ ∞ (polarLinearB w z) x ∧
      ContDiffAt ℝ ∞ (polarLinearC w z) x ∧
      ContDiffAt ℝ ∞ (polarCorrectedC w z) x ∧
      ContDiffAt ℝ ∞ (polarTypeB w z) x ∧
      ContDiffAt ℝ ∞ (polarCoordinateResidual w z) x := by
  have hE : ContDiffAt ℝ ∞ (profileEnergy w) x :=
    contDiffAt_const.add ((hw.comp x contDiffAt_fst).pow 2)
  have hEr := contDiffAt_radialPartial hE (m := ∞) (by simp)
  have hk := contDiffAt_heightRadial hz (m := ∞) (by simp)
  have hp := contDiffAt_heightAngular hz (m := ∞) (by simp) hr
  have hkr := contDiffAt_radialPartial hk (m := ∞) (by simp)
  have hpr := contDiffAt_radialPartial hp (m := ∞) (by simp)
  have hpt := contDiffAt_angularPartial hp (m := ∞) (by simp)
  have hc : ContDiffAt ℝ ∞ (fun y => 1 - heightAngular z y ^ 2) x :=
    contDiffAt_const.sub (hp.pow 2)
  have hd : ContDiffAt ℝ ∞ (polarDiscriminant w z) x :=
    (hE.mul hc).sub (hk.pow 2)
  have ht : ContDiffAt ℝ ∞ (polarScale w z) x :=
    contDiffAt_const.div (hd.mul (hd.sqrt hD.ne'))
      (mul_ne_zero hD.ne' (Real.sqrt_pos.mpr hD).ne')
  have hq : ContDiffAt ℝ ∞ (fun y =>
      heightQ (profileEnergy w y) (heightRadial z y) (angularPartial (heightAngular z) y)) x :=
    hk.add (hE.mul hpt)
  have hN : ContDiffAt ℝ ∞ (polarCurvatureNumerator w z) x :=
    ((hq.mul hkr).sub ((hE.mul contDiffAt_fst).mul (hpr.pow 2))).sub
      ((hEr.div_const 2).mul (hc.add (hk.mul hpt)))
  have hR : ContDiffAt ℝ ∞ (polarCoordinateResidual w z) x :=
    (hN.mul ht).div contDiffAt_fst hr
  have hA : ContDiffAt ℝ ∞ (polarLinearA w z) x := hq.mul ht
  have hB : ContDiffAt ℝ ∞ (polarLinearB w z) x := (hE.neg.mul hpr).mul ht
  have hC : ContDiffAt ℝ ∞ (polarLinearC w z) x :=
    (((hE.mul hkr).sub ((hEr.mul hk).div_const 2)).mul ht).div contDiffAt_fst hr
  have hCb : ContDiffAt ℝ ∞ (polarCorrectedC w z) x :=
    hC.sub ((hE.mul hR).div hq hQ)
  have hType : ContDiffAt ℝ ∞ (polarTypeB w z) x :=
    hE.div (contDiffAt_fst.mul hq) (mul_ne_zero hr hQ)
  exact ⟨hA, hB, hC, hCb, hType, hR⟩

theorem heightLinearizedDivergence_eq_corrected_of_smooth
    {w : ℝ → ℝ} {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiffAt ℝ ∞ w x.1) (hz : ContDiffAt ℝ ∞ z x)
    (hη : ContDiffAt ℝ ∞ η x) (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    heightLinearizedDivergence w z η x = heightCorrectedDivergence w z η x +
      angularPartial (fun y => polarTypeB w z y * y.1 *
        polarCoordinateResidual w z y * angularPartial η y) x := by
  obtain ⟨_, hB, _, hCb, hType, hR⟩ := contDiffAt_heightLinearCoefficients hw hz hr hD hQ
  have hηr := contDiffAt_radialPartial hη (m := ∞) (by simp)
  have hηt := contDiffAt_angularPartial hη (m := ∞) (by simp)
  apply heightLinearizedDivergence_eq_corrected w z η
  · exact ((hB.mul hηr).add (hCb.mul hηt)).differentiableAt (by simp)
  · exact (((hType.mul contDiffAt_fst).mul hR).mul hηt).differentiableAt (by simp)

theorem hasDerivAt_radialScaledResidual_corrected
    {w : ℝ → ℝ} {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    HasDerivAt (fun t => x.1 * polarCoordinateResidual w (heightFamily z η t) x)
      (heightCorrectedDivergence w z η x +
        angularPartial (fun y => polarTypeB w z y * y.1 *
          polarCoordinateResidual w z y * angularPartial η y) x) 0 :=
  (hasDerivAt_radialScaledResidual_divergence hw hz hη hr hD).congr_deriv
    (heightLinearizedDivergence_eq_corrected_of_smooth hw.contDiffAt hz.contDiffAt
      hη.contDiffAt hr hD hQ)

theorem parameter_mul_normalizedHeightResidual
    (w : ℝ → ℝ) (z u : PolarPoint → ℝ) (q : ℝ) (x : PolarPoint)
    (hzero : polarCoordinateResidual w z x = 0) :
    q * normalizedHeightResidual w z u q x =
      x.1 * polarCoordinateResidual w (heightFamily z u q) x := by
  by_cases hq : q = 0
  · simp [hq, hzero]
  · rw [normalizedHeightResidual_of_ne_zero w z u x hq]
    field_simp [hq]

/-- The normalized source is the actual source at the same height. This
is the manuscript's exact `q ∂θ(B A ηθ)` operator error. -/
theorem heightLinearizedDivergence_eq_corrected_normalized
    (w : ℝ → ℝ) (z u η : PolarPoint → ℝ) (q : ℝ) {x : PolarPoint}
    (hzero : ∀ y, polarCoordinateResidual w z y = 0)
    (hflux : DifferentiableAt ℝ (fun y =>
      polarLinearB w (heightFamily z u q) y * radialPartial η y +
        polarCorrectedC w (heightFamily z u q) y * angularPartial η y) x)
    (herr : DifferentiableAt ℝ (fun y =>
      polarTypeB w (heightFamily z u q) y * normalizedHeightResidual w z u q y *
        angularPartial η y) x) :
    heightLinearizedDivergence w (heightFamily z u q) η x =
      heightCorrectedDivergence w (heightFamily z u q) η x +
        q * angularPartial (fun y => polarTypeB w (heightFamily z u q) y *
          normalizedHeightResidual w z u q y * angularPartial η y) x := by
  have heq : (fun y => polarTypeB w (heightFamily z u q) y * y.1 *
      polarCoordinateResidual w (heightFamily z u q) y * angularPartial η y) =
      (fun y => q * (polarTypeB w (heightFamily z u q) y *
        normalizedHeightResidual w z u q y * angularPartial η y)) := by
    funext y
    have hnorm := parameter_mul_normalizedHeightResidual w z u q y (hzero y)
    calc
      _ = polarTypeB w (heightFamily z u q) y *
          (y.1 * polarCoordinateResidual w (heightFamily z u q) y) * angularPartial η y := by ring
      _ = _ := by rw [← hnorm]; ring
  have hdiff : DifferentiableAt ℝ (fun y => polarTypeB w (heightFamily z u q) y * y.1 *
      polarCoordinateResidual w (heightFamily z u q) y * angularPartial η y) x := by
    rw [heq]
    exact herr.const_mul q
  rw [heightLinearizedDivergence_eq_corrected w (heightFamily z u q) η hflux hdiff,
    heq, angularPartial_mul (differentiableAt_const q) herr,
    angularPartial_const, zero_mul, zero_add]

end ContinuousFlexibility
