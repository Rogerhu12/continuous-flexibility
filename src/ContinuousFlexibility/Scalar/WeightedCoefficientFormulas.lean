module

public import ContinuousFlexibility.Statements.ScalarWeighted

/-!
# Reduced formulas for the actual corrected scalar coefficient

The residual correction cancels the radial second derivative of the height.
The remaining expression separates the reference profile from the normalized
denominators. These are identities of the coefficients in the frozen scalar
statement, obtained from their actual definitions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

/-- The corrected angular coefficient no longer depends on the jet `kr`. -/
theorem correctedAngular_eq_reduced
    (r E Er k p kr pr pθ t : ℝ) (hr : r ≠ 0) (hQ : heightQ E k pθ ≠ 0) :
    correctedAngular r E Er k p kr pr pθ t =
      (E ^ 2 * pr ^ 2 + Er * heightDiscriminant E k p / (2 * r)) * t /
        heightQ E k pθ := by
  dsimp only [heightQ] at hQ
  unfold correctedAngular linearAngular scaledCoordinateResidual darbouxNumerator
    heightQ heightDiscriminant
  field_simp [hr, hQ]
  <;> ring

/-- The actual type-corrected coefficient is a quadratic mixed-jet term plus
one reference-slope term; the pure radial second height jet has cancelled. -/
theorem polarCorrectedC_eq_reduced
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    polarCorrectedC w z x =
      (profileEnergy w x) ^ 2 * (radialPartial (heightAngular z) x) ^ 2 /
        (heightQ (profileEnergy w x) (heightRadial z x)
          (angularPartial (heightAngular z) x) * polarDiscriminant w z x *
            Real.sqrt (polarDiscriminant w z x)) +
      w x.1 * deriv w x.1 /
        (x.1 * heightQ (profileEnergy w x) (heightRadial z x)
          (angularPartial (heightAngular z) x) * Real.sqrt (polarDiscriminant w z x)) := by
  rw [polarCorrectedC, correctedAngular_eq_reduced _ _ _ _ _ _ _ _ _ hr hQ,
    radialPartial_profileEnergy hw]
  change
    ((profileEnergy w x) ^ 2 * (radialPartial (heightAngular z) x) ^ 2 +
      (2 * w x.1 * deriv w x.1) * polarDiscriminant w z x / (2 * x.1)) *
      inverseDThreeHalves (polarDiscriminant w z x) /
        heightQ (profileEnergy w x) (heightRadial z x)
          (angularPartial (heightAngular z) x) = _
  unfold inverseDThreeHalves
  field_simp [hr, hQ, hD.ne', (Real.sqrt_pos.mpr hD).ne']
  <;> ring

/-- Only `Q/w` and the discriminant are inverted after the reference factor
`w` has been separated. This is the form used by the weighted estimates. -/
theorem polarCorrectedC_eq_normalized_profile
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hr : x.1 ≠ 0) (hwp : w x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    polarCorrectedC w z x =
      ((profileEnergy w x) ^ 2 / w x.1) * (radialPartial (heightAngular z) x) ^ 2 *
        (heightQ (profileEnergy w x) (heightRadial z x)
          (angularPartial (heightAngular z) x) / w x.1)⁻¹ *
            inverseDThreeHalves (polarDiscriminant w z x) +
      (deriv w x.1 / x.1) *
        (heightQ (profileEnergy w x) (heightRadial z x)
          (angularPartial (heightAngular z) x) / w x.1)⁻¹ *
            (Real.sqrt (polarDiscriminant w z x))⁻¹ := by
  rw [polarCorrectedC_eq_reduced hw hr hD hQ]
  unfold inverseDThreeHalves
  field_simp [hr, hwp, hQ, hD.ne', (Real.sqrt_pos.mpr hD).ne']
  <;> ring

/-- The coefficient difference consists of a profile-slope difference, a
smooth normalized-denominator difference, and a quadratic mixed jet. -/
theorem polarCorrectedC_sub_reference
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hr : x.1 ≠ 0) (hwp : w x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) (referenceSlope : ℝ) :
    polarCorrectedC w z x - referenceSlope / x.1 =
      (deriv w x.1 - referenceSlope) / x.1 +
      (deriv w x.1 / x.1) *
        ((heightQ (profileEnergy w x) (heightRadial z x)
          (angularPartial (heightAngular z) x) / w x.1)⁻¹ *
            (Real.sqrt (polarDiscriminant w z x))⁻¹ - 1) +
      ((profileEnergy w x) ^ 2 / w x.1) * (radialPartial (heightAngular z) x) ^ 2 *
        (heightQ (profileEnergy w x) (heightRadial z x)
          (angularPartial (heightAngular z) x) / w x.1)⁻¹ *
            inverseDThreeHalves (polarDiscriminant w z x) := by
  rw [polarCorrectedC_eq_normalized_profile hw hr hwp hD hQ, sub_div]
  ring

namespace Statements

/-- The reduced expression applies to every actual geometric weighted state. -/
theorem scalarStateCorrectedC_eq_reduced
    {D : ReferenceData} {S : PhysicalSpacesData} {x : ScalarWeightedState S}
    (hg : ScalarStateGeometry D S x) {p : PolarPoint}
    (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0) :
    scalarStateCorrectedC D S x p =
      (profileEnergy (scalarStateProfile D S x) p) ^ 2 *
        (radialPartial (heightAngular (scalarStateHeight D S x)) p) ^ 2 /
        (heightQ (profileEnergy (scalarStateProfile D S x) p)
          (heightRadial (scalarStateHeight D S x) p)
          (angularPartial (heightAngular (scalarStateHeight D S x)) p) *
          polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p *
          Real.sqrt (polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p)) +
      scalarStateProfile D S x p.1 * deriv (scalarStateProfile D S x) p.1 /
        (p.1 * heightQ (profileEnergy (scalarStateProfile D S x) p)
          (heightRadial (scalarStateHeight D S x) p)
          (angularPartial (heightAngular (scalarStateHeight D S x)) p) *
          Real.sqrt (polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p)) := by
  rcases hg with ⟨hw, _, _, _, _, _, _, _, _, hpos⟩
  have h := hpos p.1 hp.1
  apply polarCorrectedC_eq_reduced (hw.differentiable (by simp) p.1) hr
  · exact lt_of_lt_of_le (by norm_num) (h.2 p.2).1
  · exact (lt_of_lt_of_le (mul_pos (by norm_num) h.1) (h.2 p.2).2).ne'

end Statements

end ContinuousFlexibility
