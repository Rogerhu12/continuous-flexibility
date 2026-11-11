import ContinuousFlexibility.Analysis.ReturnCoefficientParity
import ContinuousFlexibility.Analysis.N01ReturnChartC1
import Mathlib.Analysis.Calculus.DSlope

/-!
# The actual correction as a linear function of an independent residual

The state and its actual return residual are frozen. The removable
divided difference of the actual inverse coordinate is then multiplied
by an independent decoded circle residual. This gives the exact initial
displacement, velocity increment, drift increment, and speed increment.
The divided difference equals the manuscript's derivative integral,
including at zero residual, by the actual N01 inverse regularity.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem returnCorrection_dslope_integral {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (x d : ℝ) :
    dslope F x (x + d) = ∫ t in (0 : ℝ)..1, deriv F (x + t * d) := by
  by_cases hd : d = 0
  · subst d
    simp only [zero_mul, mul_zero, add_zero, dslope_same,
      intervalIntegral.integral_const, sub_zero, one_smul]
  · apply mul_left_cancel₀ hd
    calc
      d * dslope F x (x + d) = F (x + d) - F x := by
        simpa only [add_sub_cancel_left, smul_eq_mul] using sub_smul_dslope F x (x + d)
      _ = _ := returnCorrection_difference_integral hF x d

/-- The independent residual is evaluated through the existing circle
decoder. The divided difference is frozen at the actual return residual. -/
def returnCorrectionDisplacementLinear (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (m : ℕ) (θ : ℝ) : CircleSpace S →ₗ[ℝ] ℝ :=
  let y := rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ)
  let G : ℝ → ℝ := fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)
  dslope G y (y + returnResidualField S C z m y) •
    ((LinearMap.proj y).comp ((LinearMap.proj m).comp (S.circle (3 / 4 : ℝ)).decode))

theorem returnCorrectionDisplacementLinear_apply
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (m : ℕ) (θ : ℝ) (ρ : CircleSpace S) :
    let y := rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ)
    let G : ℝ → ℝ := fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)
    returnCorrectionDisplacementLinear S C z m θ ρ =
      dslope G y (y + returnResidualField S C z m y) *
        (S.circle (3 / 4 : ℝ)).decode ρ m y := by
  simp only [returnCorrectionDisplacementLinear, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul]

theorem N01Properties.returnCorrectionDisplacementLinear_integral
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (θ : ℝ) (ρ : CircleSpace S) :
    let y := rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ)
    returnCorrectionDisplacementLinear S C z m θ ρ =
      (S.circle (3 / 4 : ℝ)).decode ρ m y *
        ∫ t in (0 : ℝ)..1,
          deriv (fun s => C.minusReturnInverse z m (C.rightChartInverse z m s))
            (y + t * returnResidualField S C z m y) := by
  rw [returnCorrectionDisplacementLinear_apply,
    returnCorrection_dslope_integral
      (hN01.returnTransportInverse_contDiff_one hS hT hz hsector m)]
  ring

theorem returnCorrectionDisplacementLinear_at_actual
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    returnCorrectionDisplacementLinear S C z m θ (R.residual z) =
      returnCorrectionInitialMap S C z m θ - θ := by
  let y := rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ)
  let G : ℝ → ℝ := fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)
  have hI := N01Properties.return_inverse_and_positive S C z m hN01 hz hsector
  have hInv : G y = θ := by
    dsimp only [G, y]
    rw [(hI (C.minusFlow z m (C.right m) θ)).2.2.2.1, (hI θ).2.1]
  have hK : returnCorrectionInitialMap S C z m θ =
      G (y + returnResidualField S C z m y) :=
    hN01.returnCorrectionInitialMap_conjugation hz hsector m θ
  rw [returnCorrectionDisplacementLinear_apply]
  change dslope G y (y + returnResidualField S C z m y) *
    (S.circle (3 / 4 : ℝ)).decode (R.residual z) m y =
      returnCorrectionInitialMap S C z m θ - θ
  rw [hN02.2.1 z hz hsector m y, hK]
  have h := sub_smul_dslope G y (y + returnResidualField S C z m y)
  rw [hInv] at h
  simpa only [add_sub_cancel_left, smul_eq_mul, mul_comm] using h

/-- The actual velocity factor from the corrected flow, linear in the
new residual argument while all inverse coordinates remain frozen. -/
def returnCorrectionVelocityLinear (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) : CircleSpace S →ₗ[ℝ] ℝ :=
  let α := Function.invFun (C.minusFlow z m p.1) p.2
  let θ := Function.invFun
    (returnInterpolation (χ m p.1) (returnCorrectionInitialMap S C z m)) α
  (deriv (C.minusFlow z m p.1) α * deriv (χ m) p.1) •
    returnCorrectionDisplacementLinear S C z m θ

theorem returnCorrectionVelocityLinear_at_actual
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (χ : ℕ → ℝ → ℝ) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (m : ℕ) (p : PolarPoint) :
    returnCorrectionVelocityLinear D S C χ z m p (R.residual z) =
      returnCorrectedMinusSpeed D S C χ z m p -
        minusCharacteristicSpeed (originalCoefficients D S C z) p := by
  simp only [returnCorrectionVelocityLinear, LinearMap.smul_apply, smul_eq_mul,
    returnCorrectionDisplacementLinear_at_actual hN01 hN02 hz hsector,
    returnCorrectedMinusSpeed]
  ring

def returnCorrectionDriftLinear (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) : CircleSpace S →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • (returnCorrectionVelocityLinear D S C χ z m p -
    returnCorrectionVelocityLinear D S C χ z m (p.1, -p.2))

def returnCorrectionSpeedLinear (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) : CircleSpace S →ₗ[ℝ] ℝ :=
  (-1 / 2 : ℝ) • (returnCorrectionVelocityLinear D S C χ z m (p.1, -p.2) +
    returnCorrectionVelocityLinear D S C χ z m p)

theorem returnCorrectionDriftLinear_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) (ρ : CircleSpace S) :
    returnCorrectionDriftLinear D S C χ z m p ρ =
      (returnCorrectionVelocityLinear D S C χ z m p ρ -
        returnCorrectionVelocityLinear D S C χ z m (p.1, -p.2) ρ) / 2 := by
  simp only [returnCorrectionDriftLinear, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
  ring

theorem returnCorrectionSpeedLinear_apply
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) (ρ : CircleSpace S) :
    returnCorrectionSpeedLinear D S C χ z m p ρ =
      (-returnCorrectionVelocityLinear D S C χ z m (p.1, -p.2) ρ -
        returnCorrectionVelocityLinear D S C χ z m p ρ) / 2 := by
  simp only [returnCorrectionSpeedLinear, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  ring

theorem returnCorrectionDriftSpeedLinear_at_actual
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε) (hS : IsPhysicalSpaces D T S)
    (χ : ℕ → ℝ → ℝ) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (m : ℕ) (p : PolarPoint) :
    (originalCoefficients D S C z).b p / (originalCoefficients D S C z).a p +
        returnCorrectionDriftLinear D S C χ z m p (R.residual z) =
      (-returnCorrectedMinusSpeed D S C χ z m (p.1, -p.2) +
        returnCorrectedMinusSpeed D S C χ z m p) / 2 ∧
    Real.sqrt ((originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) /
        (originalCoefficients D S C z).a p +
        returnCorrectionSpeedLinear D S C χ z m p (R.residual z) =
      (-returnCorrectedMinusSpeed D S C χ z m (p.1, -p.2) -
        returnCorrectedMinusSpeed D S C χ z m p) / 2 := by
  have hpar := originalCoefficients_parity_of_physical hS C z p.1 p.2
  have href := minusCharacteristicSpeed_reflection (originalCoefficients D S C z)
    p.1 p.2 hpar.1 hpar.2.1 hpar.2.2
  simp only [returnCorrectionDriftLinear_apply, returnCorrectionSpeedLinear_apply,
    returnCorrectionVelocityLinear_at_actual hN01 hN02 χ hz hsector, href,
    minusCharacteristicSpeed, plusCharacteristicSpeed]
  constructor <;> ring

end ContinuousFlexibility.Statements
