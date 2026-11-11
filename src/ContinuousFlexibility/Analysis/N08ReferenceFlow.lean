import ContinuousFlexibility.Analysis.N08ReferenceResidual
import ContinuousFlexibility.Analysis.OpticalTravelVariation
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# The actual characteristic flow at the reference state

The original corrected coefficients specialize to the radial Jacobi
coefficients.  Integrating the ordinary characteristic equation supplied by
N01 identifies its reference flow on the whole closed component.  The existing
inverse identities then prove that the genuine return residual vanishes.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_stateHeight_zero_parameter (x : AnnularState S) :
    stateHeight D S C (x, 0) =
      Radial.radialHeightField (stateRadialHeight D S C x) := by
  funext p
  simp only [stateHeight, Radial.radialHeightField, zero_mul, add_zero]

/-- The three actual, corrected coefficients of a radial primitive. -/
theorem n08_radialHeight_coefficients {w h : ℝ → ℝ}
    (hhw : ∀ r, HasDerivAt h (w r) r) {p : PolarPoint}
    (hw : DifferentiableAt ℝ w p.1) :
    polarLinearA w (Radial.radialHeightField h) p = w p.1 ∧
      polarLinearB w (Radial.radialHeightField h) p = 0 ∧
      polarCorrectedC w (Radial.radialHeightField h) p = deriv w p.1 / p.1 := by
  have hcoeff := radial_linear_coefficients p.1 (w p.1) (deriv w p.1)
  dsimp only at hcoeff
  rw [polarCorrectedC_eq_residual_correction,
    Radial.polarCoordinateResidual_radialHeightField hhw hw]
  simpa only [polarLinearA, polarLinearB, polarLinearC, polarScale,
    Radial.polarDiscriminant_radialHeightField hhw,
    Radial.heightRadial_radialHeightField hhw,
    Radial.heightAngular_radialHeightField hhw,
    Radial.radialPartial_radialHeightField hw, radialPartial_profileEnergy hw,
    radialPartial_const, angularPartial_const, profileEnergy,
    Radial.radialHeightField, heightDiscriminant_radial, inverseDThreeHalves_one,
    mul_zero, zero_div, sub_zero] using hcoeff

theorem n08_originalCoefficients_reference
    (hD : RadialProfileGeometry D) (href : referenceStateConditions D S C)
    (p : PolarPoint) :
    (originalCoefficients D S C (C.referenceState, 0)).a p = D.w p.1 ∧
      (originalCoefficients D S C (C.referenceState, 0)).b p = 0 ∧
      (originalCoefficients D S C (C.referenceState, 0)).c p = deriv D.w p.1 / p.1 := by
  change polarLinearA (stateProfile D S C C.referenceState)
      (stateHeight D S C (C.referenceState, 0)) p = D.w p.1 ∧
    polarLinearB (stateProfile D S C C.referenceState)
      (stateHeight D S C (C.referenceState, 0)) p = 0 ∧
    polarCorrectedC (stateProfile D S C C.referenceState)
      (stateHeight D S C (C.referenceState, 0)) p = deriv D.w p.1 / p.1
  rw [n08_stateProfile_reference href, n08_stateHeight_zero_parameter]
  exact n08_radialHeight_coefficients
    (n08_stateRadialHeight_reference_hasDerivAt hD href)
    (hD.2.2.1.1.differentiable (by simp) p.1)

/-- The signed ordinary speed is the negative optical speed, including
the type-change endpoints whenever they lie in the radial core. -/
theorem n08_minusCharacteristicSpeed_reference
    (hD : RadialProfileGeometry D) (href : referenceStateConditions D S C)
    (r θ : ℝ) (hr : r ∈ radialCore D) :
    minusCharacteristicSpeed (originalCoefficients D S C (C.referenceState, 0))
      (r, θ) = -opticalSpeed D.w r := by
  have hrpos : 0 < r := hD.1.trans hr.1
  have hwpos : 0 < D.w r := hD.2.2.2.2.1 r hr
  have hrad : -(D.w r * (deriv D.w r / r)) / D.w r ^ 2 =
      -deriv D.w r / (r * D.w r) := by
    field_simp [hrpos.ne', hwpos.ne']
    <;> ring
  have hsqrt : Real.sqrt (-(D.w r * (deriv D.w r / r))) / D.w r =
      opticalSpeed D.w r := by
    calc
      _ = Real.sqrt (-(D.w r * (deriv D.w r / r))) /
          Real.sqrt (D.w r ^ 2) := by rw [Real.sqrt_sq hwpos.le]
      _ = Real.sqrt (-(D.w r * (deriv D.w r / r)) / D.w r ^ 2) :=
        (Real.sqrt_div' _ (sq_nonneg _)).symm
      _ = _ := congrArg Real.sqrt hrad
  have hcoeff := n08_originalCoefficients_reference hD href (r, θ)
  simpa only [minusCharacteristicSpeed, hcoeff.1, hcoeff.2.1, hcoeff.2.2,
    zero_div, zero_pow, zero_sub] using congrArg (fun t : ℝ => -t) hsqrt

private theorem reference_mem_stateNeighborhood (hε : 0 < ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
  constructor
  · simpa only [sub_self, map_zero] using hε
  · simpa only [abs_zero] using hε

/-- N01's actual ordinary flow is determined on the entire closed
component by its differential equation and its left endpoint value. -/
theorem n08_minusFlow_reference_rotation
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (θ r : ℝ)
    (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (C.referenceState, 0) m r θ =
      θ - ∫ s in C.left m..r, opticalSpeed D.w s := by
  obtain ⟨hD, hε, href, hcontrol, _, _, hflow, _⟩ := hN
  obtain ⟨bounds, hbounds⟩ := hD.1
  have hg : RadialProfileGeometry D := hbounds.1
  have hw : ContDiff ℝ ∞ D.w := hg.2.2.1.1
  have hwd : Continuous (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hinter := hcontrol.1 m
  have hcore : ∀ s ∈ Icc (C.left m) (C.right m), s ∈ radialCore D := by
    intro s hs
    exact ⟨hinter.1.trans_le hs.1, hs.2.trans_lt hinter.2.2⟩
  have hv : ContinuousOn (opticalSpeed D.w) (Icc (C.left m) (C.right m)) := by
    exact (hwd.neg.continuousOn.div
      (continuous_id.mul hw.continuous).continuousOn
      (fun s hs => mul_ne_zero (hg.1.trans (hcore s hs).1).ne'
        (hg.2.2.2.2.1 s (hcore s hs)).ne')).sqrt
  have hf := hflow (C.referenceState, 0) (reference_mem_stateNeighborhood hε) m θ
  have hsub : Icc (C.left m) r ⊆ Icc (C.left m) (C.right m) :=
    Icc_subset_Icc le_rfl hr.2
  have hderiv : ∀ s ∈ Ioo (C.left m) r,
      HasDerivAt (fun t => C.minusFlow (C.referenceState, 0) m t θ)
        (-opticalSpeed D.w s) s := by
    intro s hs
    have hs' : s ∈ Ioo (C.left m) (C.right m) := ⟨hs.1, hs.2.trans_le hr.2⟩
    exact (hf.2.2.1 s hs').congr_deriv
      (n08_minusCharacteristicSpeed_reference hg href s _
        (hcore s (Ioo_subset_Icc_self hs')))
  have hint : IntervalIntegrable (fun s => -opticalSpeed D.w s) volume (C.left m) r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1 (hv.neg.mono hsub)
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1
    (hf.2.1.mono hsub) hderiv hint
  rw [intervalIntegral.integral_neg, hf.1] at ht
  linarith only [ht]

theorem n08_minusFlow_reference_return
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (θ : ℝ) :
    C.minusFlow (C.referenceState, 0) m (C.right m) θ = θ - C.travel m := by
  have hcontrol := hN.2.2.2.1
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hcontrol.1 m).2.1.le, le_rfl⟩
  have hf := n08_minusFlow_reference_rotation hN m θ (C.right m) hr
  obtain ⟨_, _, _, _, _, _, _, htravel, _⟩ := hcontrol
  simpa only [opticalSpeed, ← htravel m] using hf

theorem n08_minusReturnInverse_reference
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (θ : ℝ) :
    C.minusReturnInverse (C.referenceState, 0) m θ = θ + C.travel m := by
  have hi : C.minusFlow (C.referenceState, 0) m (C.right m)
      (C.minusReturnInverse (C.referenceState, 0) m θ) = θ := by
    obtain ⟨_, hε, href, _, _, _, _, _, hinverse, _⟩ := hN
    exact (hinverse (C.referenceState, 0) (reference_mem_stateNeighborhood hε)
      href.stateSector m θ).1
  have hf := n08_minusFlow_reference_return hN m
    (C.minusReturnInverse (C.referenceState, 0) m θ)
  linarith only [hi, hf]

theorem n08_stateLeftChart_reference
    (href : referenceStateConditions D S C) (m : ℕ) (θ : ℝ) :
    stateLeftChart S C.referenceState m θ = θ := by
  simp only [stateLeftChart, href.2.2.2.2.1, map_zero, Pi.zero_apply, add_zero]

/-- The inverse and phase used here are those fixed by N01.  No extra
normalization of the flow or of its right chart is assumed. -/
theorem n08_returnResidualField_reference_zero
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (θ : ℝ) :
    returnResidualField S C (C.referenceState, 0) m θ = 0 := by
  simp only [returnResidualField, evenPart,
    n08_stateLeftChart_reference hN.2.2.1, n08_minusReturnInverse_reference hN]
  ring

/-- Decoder injectivity transfers the actual reference return identity
to the circle-space residual supplied by N02. -/
theorem n08_returnResidual_reference_zero {R : ReturnEquationData S}
    (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) :
    R.residual (C.referenceState, 0) = 0 := by
  apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext m θ
  calc
    _ = returnResidualField S C (C.referenceState, 0) m θ :=
      hR.2.1 (C.referenceState, 0) (reference_mem_stateNeighborhood hN.2.1)
        hN.2.2.1.stateSector m θ
    _ = 0 := n08_returnResidualField_reference_zero hN m θ
    _ = _ := by simp only [map_zero, Pi.zero_apply]

/-- The two actual realization identities, together with the preceding
geometric stages, give the required zero of the same joint residual. -/
theorem n08_jointResidual_reference_zero {R : ReturnEquationData S}
    {P : ResidualData S} (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    (hscalar : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ p ∈ annularOpen D,
        (S.height (3 / 4 : ℝ)).decode (P.scalar z).val p = scalarResidualField D S C z p)
    (hcircle : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      (P.circle z).val = R.residual z) :
    jointResidual S P (C.referenceState, 0) = 0 := by
  have hz := reference_mem_stateNeighborhood (C := C) (base := base) hN.2.1
  have hs := hN.2.2.1.stateSector
  apply Prod.ext
  · change P.scalar (C.referenceState, 0) = 0
    exact n08_source_reference_zero hS hN.1 hN.2.2.1 _
      (hscalar (C.referenceState, 0) hz hs)
  · change P.circle (C.referenceState, 0) = 0
    apply Subtype.ext
    change (P.circle (C.referenceState, 0)).val = 0
    exact (hcircle (C.referenceState, 0) hz hs).trans
      (n08_returnResidual_reference_zero hS hN hR)

end ContinuousFlexibility.Statements
