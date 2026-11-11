import ContinuousFlexibility.Scalar.WeightedStateJetFormulas
import ContinuousFlexibility.Scalar.WeightedStateFlatness

/-!
# Finite-jet formulas for the removable weighted scalar residual

The quadratic numerator expansion removes division by the construction
parameter. The resulting formula uses only the profile mean, its first
derivative, and spatial height jets of order at most two. At parameter zero
the actual frozen residual agrees with the radial PDE on the whole plane.
-/

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

/-- The height-quadratic numerator written in actual spatial jets. -/
theorem polarCurvatureNumeratorQuadratic_eq_jets
    {w : ℝ → ℝ} (η : PolarPoint → ℝ) {p : PolarPoint}
    (hw : DifferentiableAt ℝ w p.1) :
    polarCurvatureNumeratorQuadratic w η p =
      (radialPartial η p + (1 + w p.1 ^ 2) * angularPartial (heightAngular η) p) *
          radialPartial (radialPartial η) p -
        (1 + w p.1 ^ 2) * p.1 * radialPartial (heightAngular η) p ^ 2 +
        w p.1 * deriv w p.1 *
          (heightAngular η p ^ 2 - radialPartial η p * angularPartial (heightAngular η) p) := by
  unfold polarCurvatureNumeratorQuadratic polarCurvatureNumerator
  simp only [radialPartial_profileEnergy hw, darbouxNumerator, heightQ, profileEnergy,
    radialEnergy, heightRadial]
  ring

namespace Statements

/-- An explicit formula in reference coefficients and finite height jets.
There is no division by the construction parameter, including at zero. -/
def scalarResidualFiniteFormula (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (p : PolarPoint) : ℝ :=
  let m := scalarStateProfileMean S x p.1
  let m' := deriv (scalarStateProfileMean S x) p.1
  let w := D.w p.1 * (1 + m)
  let w' := deriv D.w p.1 * (1 + m) + D.w p.1 * m'
  let a := radialPartial (scalarStateIncrement S x) p
  let b := radialPartial (radialPartial (scalarStateIncrement S x)) p
  let c := heightAngular (scalarStateIncrement S x) p
  let d := radialPartial (heightAngular (scalarStateIncrement S x)) p
  let e := angularPartial (heightAngular (scalarStateIncrement S x)) p
  (w' * (a + e) + w * b +
    x.2 * ((a + (1 + w ^ 2) * e) * b - (1 + w ^ 2) * p.1 * d ^ 2 +
      w * w' * (c ^ 2 - a * e))) *
        inverseDThreeHalves (1 + scalarStateDDefect D S x p)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- The actual radial base has zero numerator, so the factored expression
holds also at the removable parameter value. -/
theorem scalarStateResidual_eq_factored
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) {p : PolarPoint} (hr : p.1 ≠ 0) :
    scalarStateResidual D S x p =
      (Radial.radialPDE (scalarStateProfile D S x)
          (fun r θ => scalarStateIncrement S x (r, θ)) p.1 p.2 +
        x.2 * polarCurvatureNumeratorQuadratic (scalarStateProfile D S x)
          (scalarStateIncrement S x) p) *
            inverseDThreeHalves (1 + scalarStateDDefect D S x p) := by
  have hw := (scalarStateProfile_contDiff hD hT hS x).differentiable (by simp) p.1
  have hu := scalarStateIncrement_contDiff hT hS x
  have hprim := scalarStatePrimitive_hasDerivAt hD hT hS x
  have hzero := Radial.polarCurvatureNumerator_radialHeightField (x := p) hprim hw
  change normalizedHeightResidual _ _ _ x.2 p = _
  rw [normalizedHeightResidual_eq_factored _
    (Radial.contDiff_radialHeightField (scalarStatePrimitive_contDiff hD hT hS x))
    hu hr hzero x.2,
    Radial.polarCurvatureNumeratorVariation_radialHeightField hprim hw hu hr]
  change _ * inverseDThreeHalves
    (polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p) = _
  rw [scalarState_discriminant_eq_one_add_defect hD hT hS x p]

/-- The numerator uses only first and second spatial jets of the increment. -/
theorem scalarStateResidual_eq_jets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) {p : PolarPoint} (hr : p.1 ≠ 0) :
    scalarStateResidual D S x p =
      (deriv (scalarStateProfile D S x) p.1 *
          (radialPartial (scalarStateIncrement S x) p +
            angularPartial (heightAngular (scalarStateIncrement S x)) p) +
        scalarStateProfile D S x p.1 *
          radialPartial (radialPartial (scalarStateIncrement S x)) p +
        x.2 *
          ((radialPartial (scalarStateIncrement S x) p +
              (1 + scalarStateProfile D S x p.1 ^ 2) *
                angularPartial (heightAngular (scalarStateIncrement S x)) p) *
              radialPartial (radialPartial (scalarStateIncrement S x)) p -
            (1 + scalarStateProfile D S x p.1 ^ 2) * p.1 *
              radialPartial (heightAngular (scalarStateIncrement S x)) p ^ 2 +
            scalarStateProfile D S x p.1 * deriv (scalarStateProfile D S x) p.1 *
              (heightAngular (scalarStateIncrement S x) p ^ 2 -
                radialPartial (scalarStateIncrement S x) p *
                  angularPartial (heightAngular (scalarStateIncrement S x)) p))) *
        inverseDThreeHalves (1 + scalarStateDDefect D S x p) := by
  have hw := (scalarStateProfile_contDiff hD hT hS x).differentiable (by simp) p.1
  have hu := scalarStateIncrement_contDiff hT hS x
  rw [scalarStateResidual_eq_factored hD hT hS x hr,
    polarCurvatureNumeratorQuadratic_eq_jets _ hw,
    Radial.radialPDE_eq_polar_jets hw hu]
  simp only [Radial.angularPartial_heightAngular_eq hu hr]
  ring

/-- Reference-profile factorization of the same actual frozen residual. -/
theorem scalarStateResidual_eq_finiteFormula
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) {p : PolarPoint} (hr : p.1 ≠ 0) :
    scalarStateResidual D S x p = scalarResidualFiniteFormula D S x p := by
  rw [scalarStateResidual_eq_jets hD hT hS x hr]
  simp only [scalarResidualFiniteFormula, scalarStateProfile_eq_mean,
    scalarStateProfile_deriv_expansion hD hT hS]

/-- The explicit radial factor in the frozen residual determines its value
at the origin, regardless of the construction parameter. -/
theorem scalarStateResidual_eq_zero_at_origin
    (x : ScalarWeightedState S) {p : PolarPoint} (hr : p.1 = 0) :
    scalarStateResidual D S x p = 0 := by
  change normalizedHeightResidual _ _ _ x.2 p = 0
  unfold normalizedHeightResidual
  split_ifs <;> simp only [hr, zero_mul, zero_div]

/-- The zero-parameter identity is global, as required by the frozen
weighted statement; support of the profile also handles the origin. -/
theorem scalarStateResidual_zero_parameter_eq_radialPDE
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (hq : x.2 = 0) (p : PolarPoint) :
    scalarStateResidual D S x p =
      Radial.radialPDE (scalarStateProfile D S x)
        (fun r θ => scalarStateIncrement S x (r, θ)) p.1 p.2 := by
  have hw := (scalarStateProfile_contDiff hD hT hS x).differentiable (by simp) p.1
  have hu := scalarStateIncrement_contDiff hT hS x
  by_cases hr : p.1 = 0
  · have ha : 0 ≤ D.a := by
      obtain ⟨C, hC⟩ := hD
      exact hC.1.1.le
    have hwzero := scalarStateProfile_eq_zero_outside (S := S) hD x (Or.inl ha)
    have hdwzero : deriv (scalarStateProfile D S x) 0 = 0 := by
      simpa only [iteratedDeriv_one] using
        ((scalarStateProfile_endpointFlat hD hT hS x).iteratedDeriv 1).2 0 (Or.inl ha)
    rw [scalarStateResidual_eq_zero_at_origin x hr, Radial.radialPDE_eq_polar_jets hw hu]
    simp only [hr, hwzero, hdwzero, zero_mul, zero_div, zero_add]
  · change normalizedHeightResidual _ _ _ x.2 p = _
    rw [hq]
    exact Radial.normalizedHeightResidual_radialHeightField_zero
      (scalarStatePrimitive_hasDerivAt hD hT hS x) hw hu hr

end Statements

end ContinuousFlexibility
