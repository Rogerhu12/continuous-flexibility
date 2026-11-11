import ContinuousFlexibility.Analysis.ReturnCorrectionResidualLinear
import ContinuousFlexibility.Analysis.ReturnCorrectionDivergence
import ContinuousFlexibility.Analysis.ReturnCorrectionSource

/-!
# The actual frozen residual coefficient error

The coefficient error is a linear map on the existing circle space.
Evaluating it at the actual return residual gives the exact difference
between the original and globally patched symmetric coefficients.
The radial coefficient positivity is derived directly from N01.
The nonnegative discriminant needed to reconstruct the old coefficients
is stated only where the correction is active.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem N01Properties.originalRadialCoefficient_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    0 < (originalCoefficients D S C z).a p := by
  obtain ⟨bounds, hbounds⟩ := hN01.1.1
  have hw : 0 < D.w p.1 := hbounds.1.2.2.2.2.1 p.1 hp.1
  have hstatew : 0 < stateProfile D S C z.1 p.1 := by
    change 0 < D.w p.1 * Real.exp _
    exact mul_pos hw (Real.exp_pos _)
  rcases hN01 with ⟨_, _, _, _, _, _, _, _, _, hcoeff, _⟩
  have hb := hcoeff z hz hsector p hp
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) :=
    (div_pos_iff_of_pos_right hstatew).mp
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hb.2.2.1)
  have hDisc : 0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb.2.2.2.2.1
  change 0 < polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) p
  unfold polarLinearA linearRadial polarScale inverseDThreeHalves
  exact mul_pos hQ (one_div_pos.mpr (mul_pos hDisc (Real.sqrt_pos.mpr hDisc)))

/-- The two actual coefficient errors on one component, frozen at the
actual state and its actual return residual. -/
def returnCorrectionLocalCoefficientError (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) :
    CircleSpace S →ₗ[ℝ] ℝ × ℝ :=
  returnCoefficientError
    ((originalCoefficients D S C z).a p)
    ((originalCoefficients D S C z).b p / (originalCoefficients D S C z).a p)
    (Real.sqrt ((originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) /
        (originalCoefficients D S C z).a p)
    (returnCorrectionDriftLinear D S C χ z m p)
    (returnCorrectionSpeedLinear D S C χ z m p) (R.residual z)

theorem returnCorrectionLocalCoefficientError_at_actual
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε) (hS : IsPhysicalSpaces D T S)
    (χ : ℕ → ℝ → ℝ) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (m : ℕ) (p : PolarPoint)
    (ha : (originalCoefficients D S C z).a p ≠ 0)
    (hdisc : 0 ≤ (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    returnCorrectionLocalCoefficientError D S C R χ z m p (R.residual z) =
      ((originalCoefficients D S C z).b p -
          (returnCorrectedComponentCoefficients D S C χ z m).b p,
        (originalCoefficients D S C z).c p -
          (returnCorrectedComponentCoefficients D S C χ z m).c p) := by
  let a := (originalCoefficients D S C z).a p
  let d := (originalCoefficients D S C z).b p / a
  let v := Real.sqrt ((originalCoefficients D S C z).b p ^ 2 -
    a * (originalCoefficients D S C z).c p) / a
  have hb : a * d = (originalCoefficients D S C z).b p := mul_div_cancel₀ _ ha
  have hc : a * (d ^ 2 - v ^ 2) = (originalCoefficients D S C z).c p := by
    simpa only [returnCorrectionCoefficients_c_apply] using
      (returnCorrectionCoefficients_recover (originalCoefficients D S C z) p ha hdisc).2
  have hs := returnCorrectionDriftSpeedLinear_at_actual hN01 hN02 hS χ hz hsector m p
  change returnCoefficientError a d v
    (returnCorrectionDriftLinear D S C χ z m p)
    (returnCorrectionSpeedLinear D S C χ z m p) (R.residual z) (R.residual z) = _
  rw [returnCoefficientError_at_residual, hs.1, hs.2, hb, hc]
  rfl

/-- The same component selector as the actual coefficient patch,
with zero error wherever that patch is inactive. -/
def returnCorrectionCoefficientError (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (p : PolarPoint) : CircleSpace S →ₗ[ℝ] ℝ × ℝ := by
  classical
  exact if h : ∃ m, p.1 ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) p.1 ≠ 0 then
    returnCorrectionLocalCoefficientError D S C R χ z (Classical.choose h) p else 0

theorem returnCorrectionCoefficientError_at_actual
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε) (hS : IsPhysicalSpaces D T S)
    (χ : ℕ → ℝ → ℝ) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (p : PolarPoint) (hp : p ∈ annularOpen D)
    (hdisc : ∀ m, p.1 ∈ Ioo (C.left m) (C.right m) → deriv (χ m) p.1 ≠ 0 →
      0 ≤ (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    returnCorrectionCoefficientError D S C R χ z p (R.residual z) =
      ((originalCoefficients D S C z).b p - (returnCorrectedCoefficients D S C χ z).b p,
        (originalCoefficients D S C z).c p - (returnCorrectedCoefficients D S C χ z).c p) := by
  by_cases hex : ∃ m, p.1 ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) p.1 ≠ 0
  · have hm := Classical.choose_spec hex
    have hlocal := returnCorrectionLocalCoefficientError_at_actual hN01 hN02 hS χ
      hz hsector (Classical.choose hex) p
      (hN01.originalRadialCoefficient_pos hz hsector hp).ne'
      (hdisc _ hm.1 hm.2)
    simpa only [returnCorrectionCoefficientError, returnCorrectedCoefficients, dif_pos hex]
      using hlocal
  · have heq := returnCorrectedCoefficients_eq_original_at_of_inactive D S C χ z p hex
    simp only [returnCorrectionCoefficientError, dif_neg hex, LinearMap.zero_apply,
      heq.1, heq.2, sub_self]

/-- The actual scalar differential error. The global source decoder
requires zero outside the open annulus, so that extension is explicit. -/
def returnCorrectionResidualErrorField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (ρ : CircleSpace S) (η : HeightPair S) (p : PolarPoint) : ℝ := by
  classical
  exact if p ∈ annularOpen D then
    radialPartial (fun q =>
      (returnCorrectionCoefficientError D S C R χ z q ρ).1 *
        angularPartial (heightPairField S η) q) p +
    angularPartial (fun q =>
      (returnCorrectionCoefficientError D S C R χ z q ρ).1 *
        radialPartial (heightPairField S η) q +
      (returnCorrectionCoefficientError D S C R χ z q ρ).2 *
        angularPartial (heightPairField S η) q) p
    else 0

theorem returnCorrectionResidualErrorField_zero_outside
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (ρ : CircleSpace S) (η : HeightPair S) (p : PolarPoint)
    (hp : p ∉ annularOpen D) :
    returnCorrectionResidualErrorField D S C R χ z ρ η p = 0 := by
  simp only [returnCorrectionResidualErrorField, if_neg hp]

end ContinuousFlexibility.Statements
