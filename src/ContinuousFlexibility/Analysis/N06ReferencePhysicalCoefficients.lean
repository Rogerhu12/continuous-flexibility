import ContinuousFlexibility.Analysis.NeighborhoodStateBounds
import ContinuousFlexibility.Analysis.CanonicalPrincipalCoefficients

/-!
# The actual physical coefficients at the reference state

The profile controls and the perturbation parameter vanish at the selected
reference state. The height is therefore the actual radial primitive of w.
Its genuine derivatives identify the corrected physical coefficients with
w, zero, and w'/r. The N03 correction agrees with those germs on every
actual positive piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

theorem n06_stateProfile_reference
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) :
    stateProfile D S C C.referenceState = D.w := by
  obtain ⟨_, _, hτ, hκ, _, _⟩ := href
  funext r
  simp only [stateProfile, stateKappa, hτ, hκ, map_zero, Pi.zero_apply,
    angularMean, intervalIntegral.integral_zero, mul_zero, zero_mul, tsum_zero,
    zero_add, Real.exp_zero, mul_one]

/-- The pointwise reference calculation uses actual height derivatives,
including the cancellation in the corrected angular coefficient. -/
theorem n06_radial_physical_coefficients
    {w h : ℝ → ℝ} (hhw : ∀ r, HasDerivAt h (w r) r)
    {p : PolarPoint} (hw : DifferentiableAt ℝ w p.1) :
    polarLinearA w (Radial.radialHeightField h) p = w p.1 ∧
      polarLinearB w (Radial.radialHeightField h) p = 0 ∧
      polarCorrectedC w (Radial.radialHeightField h) p = deriv w p.1 / p.1 := by
  have hC : polarCorrectedC w (Radial.radialHeightField h) p =
      polarLinearC w (Radial.radialHeightField h) p := by
    rw [polarCorrectedC_eq_residual_correction,
      Radial.polarCoordinateResidual_radialHeightField hhw hw,
      mul_zero, zero_div, sub_zero]
  rw [hC]
  simpa only [polarLinearA, polarLinearB, polarLinearC, polarScale,
    Radial.heightRadial_radialHeightField hhw,
    Radial.heightAngular_radialHeightField hhw,
    Radial.polarDiscriminant_radialHeightField hhw,
    Radial.radialPartial_radialHeightField hw,
    radialPartial_const, angularPartial_const, radialPartial_profileEnergy hw,
    profileEnergy, Radial.radialHeightField, heightDiscriminant_radial,
    inverseDThreeHalves_one] using
    radial_linear_coefficients p.1 (w p.1) (deriv w p.1)

theorem n06_originalCoefficients_reference
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hw : ContDiff ℝ ∞ D.w) (href : referenceStateConditions D S C)
    (p : PolarPoint) :
    (originalCoefficients D S C (C.referenceState, 0)).a p = D.w p.1 ∧
      (originalCoefficients D S C (C.referenceState, 0)).b p = 0 ∧
      (originalCoefficients D S C (C.referenceState, 0)).c p = deriv D.w p.1 / p.1 := by
  have hprofile := n06_stateProfile_reference href
  have hwstate : ContDiff ℝ ∞ (stateProfile D S C C.referenceState) := by
    rw [hprofile]
    exact hw
  have hprimitive (r : ℝ) :
      HasDerivAt (stateRadialHeight D S C C.referenceState) (D.w r) r := by
    simpa only [hprofile] using stateRadialHeight_hasDerivAt_of_contDiff hwstate r
  have hheight : stateHeight D S C (C.referenceState, 0) =
      Radial.radialHeightField (stateRadialHeight D S C C.referenceState) := by
    funext q
    simp only [stateHeight, Radial.radialHeightField, zero_mul, add_zero]
  simpa only [originalCoefficients, hprofile, hheight] using
    n06_radial_physical_coefficients hprimitive (hw.differentiable (by simp) p.1)

/-- On a positive physical point N03 preserves the full coefficient germs,
not merely their point values. -/
theorem n06_correctedReference_coefficients_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hN03 : N03Properties D T S C R L base ε)
    (hw : ContDiff ℝ ∞ D.w) (href : referenceStateConditions D S C)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState)
    {p : PolarPoint} (hp : p ∈ annularOpen D) (hpos : 0 < deriv D.w p.1) :
    (L.coefficients (C.referenceState, 0)).a =ᶠ[𝓝 p] (fun q => D.w q.1) ∧
      (L.coefficients (C.referenceState, 0)).b =ᶠ[𝓝 p] (fun _ => 0) ∧
      (L.coefficients (C.referenceState, 0)).c =ᶠ[𝓝 p]
        (fun q => deriv D.w q.1 / q.1) := by
  have hbc := hN03.2.1 (C.referenceState, 0) hz hs p hp hpos
  refine ⟨Filter.Eventually.of_forall (fun q => ?_), ?_, ?_⟩
  · exact (hN03.1 (C.referenceState, 0) hz hs q).trans
      (n06_originalCoefficients_reference hw href q).1
  · filter_upwards [hbc.1] with q hq
    exact hq.trans (n06_originalCoefficients_reference hw href q).2.1
  · filter_upwards [hbc.2] with q hq
    exact hq.trans (n06_originalCoefficients_reference hw href q).2.2

/-- The positive-piece geometry in N04 supplies both the physical annulus
membership and the positive reference slope used by the preceding result. -/
theorem n06_correctedReference_positivePiece_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε)
    (hw : ContDiff ℝ ∞ D.w) (href : referenceStateConditions D S C)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState)
    (m : ℕ) (hm : K.positive m = true)
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    (L.coefficients (C.referenceState, 0)).a =ᶠ[𝓝 p] (fun q => D.w q.1) ∧
      (L.coefficients (C.referenceState, 0)).b =ᶠ[𝓝 p] (fun _ => 0) ∧
      (L.coefficients (C.referenceState, 0)).c =ᶠ[𝓝 p]
        (fun q => deriv D.w q.1 / q.1) := by
  apply n06_correctedReference_coefficients_germ hN03 hw href hz hs
  · exact ⟨(hA.2.2.2.1 m).2.2 hp.1, mem_univ _⟩
  · exact hA.2.2.2.2.1 m hm p.1 hp.1

end ContinuousFlexibility.Analysis
