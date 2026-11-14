module

public import ContinuousFlexibility.Analysis.ReturnCorrectionAlgebra
public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Tactic.FieldSimp

/-!
# The return correction as the actual symmetric coefficient object

These lemmas connect the scalar construction of `ReturnCorrectionAlgebra`
to the `SymmetricCoefficients` and characteristic speeds used by N03.
The radial coefficient is preserved by construction. The compatibility
integral is automatic once an error has actually been realized in
`PhysicalSpacesData.Source`; this does not replace that realization step.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter
open scoped Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- Reconstruct the actual symmetric coefficients from the unchanged
radial coefficient, the drift, and the characteristic speed. -/
def returnCorrectionCoefficients (a d v : PolarPoint → ℝ) : SymmetricCoefficients where
  a := a
  b := fun p => a p * d p
  c := fun p => a p * (d p ^ 2 - v p ^ 2)

theorem returnCorrectionCoefficients_a (a d v : PolarPoint → ℝ) :
    (returnCorrectionCoefficients a d v).a = a := rfl

theorem returnCorrectionCoefficients_b_apply (a d v : PolarPoint → ℝ) (p : PolarPoint) :
    (returnCorrectionCoefficients a d v).b p = a p * d p := rfl

theorem returnCorrectionCoefficients_c_apply (a d v : PolarPoint → ℝ) (p : PolarPoint) :
    (returnCorrectionCoefficients a d v).c p = a p * (d p ^ 2 - v p ^ 2) := rfl

/-- The reconstructed coefficients have exactly the asserted two
characteristic slopes. -/
theorem returnCorrectionCoefficients_characteristicSpeeds
    (a d v : PolarPoint → ℝ) (p : PolarPoint) (ha : 0 < a p) (hv : 0 ≤ v p) :
    minusCharacteristicSpeed (returnCorrectionCoefficients a d v) p = d p - v p ∧
    plusCharacteristicSpeed (returnCorrectionCoefficients a d v) p = d p + v p := by
  simpa only [minusCharacteristicSpeed, plusCharacteristicSpeed,
    returnCorrectionCoefficients_a, returnCorrectionCoefficients_b_apply,
    returnCorrectionCoefficients_c_apply] using
      returnCorrection_characteristic_slopes (d p) ha hv

/-- Reconstruction directly from an ordered pair of slopes, with the
same function `a` in the resulting coefficient object. -/
theorem returnCorrectionCoefficients_of_slopes
    (a minus plus : PolarPoint → ℝ) (p : PolarPoint)
    (ha : 0 < a p) (horder : minus p ≤ plus p) :
    minusCharacteristicSpeed
      (returnCorrectionCoefficients a (fun q => (plus q + minus q) / 2)
        (fun q => (plus q - minus q) / 2)) p = minus p ∧
    plusCharacteristicSpeed
      (returnCorrectionCoefficients a (fun q => (plus q + minus q) / 2)
        (fun q => (plus q - minus q) / 2)) p = plus p := by
  have h := returnCorrectionCoefficients_characteristicSpeeds a
    (fun q => (plus q + minus q) / 2) (fun q => (plus q - minus q) / 2) p ha
      (div_nonneg (sub_nonneg.mpr horder) (by norm_num))
  have hs := returnCorrection_drift_speed (minus p) (plus p)
  exact ⟨h.1.trans hs.1, h.2.trans hs.2⟩

/-- Parity of all three actual coefficients, in the form used in N03. -/
theorem returnCorrectionCoefficients_parity
    (a d v : PolarPoint → ℝ)
    (ha : ∀ r θ, a (r, -θ) = a (r, θ))
    (hd : ∀ r θ, d (r, -θ) = -d (r, θ))
    (hv : ∀ r θ, v (r, -θ) = v (r, θ)) (r θ : ℝ) :
    (returnCorrectionCoefficients a d v).a (r, -θ) =
        (returnCorrectionCoefficients a d v).a (r, θ) ∧
    (returnCorrectionCoefficients a d v).b (r, -θ) =
        -(returnCorrectionCoefficients a d v).b (r, θ) ∧
    (returnCorrectionCoefficients a d v).c (r, -θ) =
        (returnCorrectionCoefficients a d v).c (r, θ) := by
  refine ⟨ha r θ, ?_⟩
  simpa only [returnCorrectionCoefficients_b_apply, returnCorrectionCoefficients_c_apply] using
    returnCorrection_coefficients_parity (fun t => a (r, t))
      (fun t => d (r, t)) (fun t => v (r, t)) (ha r) (hd r) (hv r) θ

/-- Vanishing increments on a neighborhood give equality of the
actual coefficients on that same neighborhood. This is the form
needed on positive components and at the turning points. -/
theorem returnCorrectionCoefficients_eventuallyEq
    (a d v D V : PolarPoint → ℝ) (p : PolarPoint)
    (hD : ∀ᶠ q in 𝓝 p, D q = 0) (hV : ∀ᶠ q in 𝓝 p, V q = 0) :
    (returnCorrectionCoefficients a (fun q => d q + D q) (fun q => v q + V q)).b
      =ᶠ[𝓝 p] (returnCorrectionCoefficients a d v).b ∧
    (returnCorrectionCoefficients a (fun q => d q + D q) (fun q => v q + V q)).c
      =ᶠ[𝓝 p] (returnCorrectionCoefficients a d v).c := by
  constructor
  · filter_upwards [hD] with q hq
    simp only [returnCorrectionCoefficients_b_apply, hq, add_zero]
  · filter_upwards [hD, hV] with q hDq hVq
    simp only [returnCorrectionCoefficients_c_apply, hDq, hVq, add_zero]

/-- Recover the original coefficient values from their drift and
square-root speed whenever the discriminant is nonnegative. -/
theorem returnCorrectionCoefficients_recover (L : SymmetricCoefficients)
    (p : PolarPoint) (ha : L.a p ≠ 0) (hdisc : 0 ≤ L.b p ^ 2 - L.a p * L.c p) :
    (returnCorrectionCoefficients L.a (fun q => L.b q / L.a q)
      (fun q => Real.sqrt (L.b q ^ 2 - L.a q * L.c q) / L.a q)).b p = L.b p ∧
    (returnCorrectionCoefficients L.a (fun q => L.b q / L.a q)
      (fun q => Real.sqrt (L.b q ^ 2 - L.a q * L.c q) / L.a q)).c p = L.c p := by
  constructor
  · rw [returnCorrectionCoefficients_b_apply]
    exact mul_div_cancel₀ _ ha
  · rw [returnCorrectionCoefficients_c_apply, div_pow, div_pow, Real.sq_sqrt hdisc]
    field_simp [ha] <;> ring

section Error

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- The independent residual coefficient map specializes to the
exact difference of the two `SymmetricCoefficients` objects. -/
theorem returnCorrectionCoefficients_error_at_residual
    (a d v : PolarPoint → ℝ) (D V : PolarPoint → E →ₗ[ℝ] ℝ) (e : E) (p : PolarPoint) :
    returnCoefficientError (a p) (d p) (v p) (D p) (V p) e e =
      ((returnCorrectionCoefficients a d v).b p -
          (returnCorrectionCoefficients a (fun q => d q + D q e)
            (fun q => v q + V q e)).b p,
        (returnCorrectionCoefficients a d v).c p -
          (returnCorrectionCoefficients a (fun q => d q + D q e)
            (fun q => v q + V q e)).c p) := by
  simpa only [returnCorrectionCoefficients_b_apply, returnCorrectionCoefficients_c_apply] using
    returnCoefficientError_at_residual (a p) (d p) (v p) (D p) (V p) e

end Error

/-- Every actual source vector has zero physical source integral.
The assertion uses the physical compatibility functional supplied
by `IsPhysicalSpaces`, not an unproved integration-by-parts argument. -/
theorem physicalSourceIntegral_decode_source_eq_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (f : S.Source) :
    physicalSourceIntegral D ((S.height (3 / 4 : ℝ)).decode f.val) = 0 := by
  rcases hS with ⟨_, _, _, _, _, _, _, hQ, _⟩
  exact (hQ f.val).symm.trans (LinearMap.mem_ker.mp f.property)

/-- This is the physical-integral clause of N03, once the correction
has been constructed with its stated codomain `S.Source`. -/
theorem returnCorrection_error_sourceIntegral_eq_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) (r : CircleSpace S) (η : HeightPair S) :
    physicalSourceIntegral D
      ((S.height (3 / 4 : ℝ)).decode ((L.error z r η).val)) = 0 :=
  physicalSourceIntegral_decode_source_eq_zero hS (L.error z r η)

end ContinuousFlexibility.Statements
