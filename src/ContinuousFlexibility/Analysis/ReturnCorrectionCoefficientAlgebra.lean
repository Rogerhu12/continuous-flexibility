import ContinuousFlexibility.Analysis.ReturnCorrectionResidualPeriodicity

/-!
# Polynomial form of the actual coefficient error

The radial coefficient cancels both denominators in the reconstruction.
Thus the actual independent-residual error uses only the original radial
and mixed coefficients, the square root of the original discriminant,
and the reflected velocity increments. This form keeps the spatial and
parameter derivative budgets visible without introducing a reciprocal
coefficient into the error formula.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

theorem returnCoefficientError_cancel_denominators
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a b q : ℝ) (D V : E →ₗ[ℝ] ℝ) (e ρ : E) (ha : a ≠ 0) :
    returnCoefficientError a (b / a) (q / a) D V e ρ =
      (-a * D ρ,
        -2 * b * D ρ - a * D e * D ρ +
          2 * q * V ρ + a * V e * V ρ) := by
  rw [returnCoefficientError_apply]
  apply Prod.ext
  · rfl
  · dsimp only
    field_simp [ha]
    <;> ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

theorem returnCorrectionLocalCoefficientError_cancel_denominators
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) (ρ : CircleSpace S)
    (ha : (originalCoefficients D S C z).a p ≠ 0) :
    returnCorrectionLocalCoefficientError D S C R χ z m p ρ =
      (-(originalCoefficients D S C z).a p *
          returnCorrectionDriftLinear D S C χ z m p ρ,
        -2 * (originalCoefficients D S C z).b p *
            returnCorrectionDriftLinear D S C χ z m p ρ -
          (originalCoefficients D S C z).a p *
            returnCorrectionDriftLinear D S C χ z m p (R.residual z) *
            returnCorrectionDriftLinear D S C χ z m p ρ +
          2 * Real.sqrt ((originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) *
            returnCorrectionSpeedLinear D S C χ z m p ρ +
          (originalCoefficients D S C z).a p *
            returnCorrectionSpeedLinear D S C χ z m p (R.residual z) *
            returnCorrectionSpeedLinear D S C χ z m p ρ) :=
  returnCoefficientError_cancel_denominators _ _ _ _ _ _ _ ha

end ContinuousFlexibility.Statements
