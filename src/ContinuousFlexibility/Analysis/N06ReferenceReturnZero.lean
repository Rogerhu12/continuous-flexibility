module

public import ContinuousFlexibility.Analysis.N01RadialFlow
public import ContinuousFlexibility.Analysis.N06ReferencePhysicalCoefficients
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# The actual reference return residual is zero

The existing radial-flow theorem integrates the genuine ordinary-flow ODE.
At the reference state its actual profile is the reference profile, and its
endpoint travel is the travel stored in N01. The real return inverse is
therefore the opposite translation. The reference chart is the identity,
so the actual even return residual vanishes. Injectivity of the original
circle model then eliminates the N03 error by linearity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n06_referenceReturn_seminorm_center
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) {ε : ℝ} (hε : 0 < ε) : p (x - x) < ε := by
  simpa only [sub_self, map_zero] using hε

private theorem n06_referenceReturn_neighborhood
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (base : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
  constructor
  · exact n06_referenceReturn_seminorm_center (stateGrading S base) C.referenceState hε
  · simpa only [abs_zero] using hε

theorem n06_stateLeftChart_reference
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) (m : ℕ) (θ : ℝ) :
    stateLeftChart S C.referenceState m θ = θ := by
  simp only [stateLeftChart, href.2.2.2.2.1, map_zero, Pi.zero_apply, add_zero]

/-- The true ordinary reference trajectory is the initial angle minus
the actual partial optical travel, including the closed endpoints. -/
theorem n06_minusFlow_reference_eq_opticalTravel
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (θ : ℝ) {r : ℝ}
    (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (C.referenceState, 0) m r θ =
      θ - opticalTravel D.w (C.left m) r := by
  have hflow := hN01.minusFlow_zero_eq_opticalTravel hS hT
    (n06_referenceReturn_neighborhood C base hN01.2.1) m θ hr
  simpa only [n06_stateProfile_reference hN01.2.2.1] using hflow

/-- The stored travel in N01 is the travel of this very same reference
profile, so its actual return map is exactly the prescribed translation. -/
theorem n06_minusFlow_reference_right
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (θ : ℝ) :
    C.minusFlow (C.referenceState, 0) m (C.right m) θ = θ - C.travel m := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  have htravel : C.travel m = opticalTravel D.w (C.left m) (C.right m) :=
    hC.2.2.2.2.2.2.2.1 m
  rw [htravel]
  exact n06_minusFlow_reference_eq_opticalTravel hN01 hS hT m θ
    ⟨(hC.1 m).2.1.le, le_rfl⟩

/-- The genuine inverse identity determines the stored return inverse;
there is no choice of an unrelated inverse representative. -/
theorem n06_minusReturnInverse_reference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (θ : ℝ) :
    C.minusReturnInverse (C.referenceState, 0) m θ = θ + C.travel m := by
  have hinverse := (hN02.1 (C.referenceState, 0)
    (n06_referenceReturn_neighborhood C base hN01.2.1)
    hN01.2.2.1.stateSector m θ).1
  rw [n06_minusFlow_reference_right hN01 hS hT] at hinverse
  linarith only [hinverse]

private theorem n06_referenceReturn_argument
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (θ : ℝ) :
    stateLeftChart S C.referenceState m
        (C.minusReturnInverse (C.referenceState, 0) m θ) - C.travel m = θ := by
  rw [n06_stateLeftChart_reference hN01.2.2.1,
    n06_minusReturnInverse_reference hN01 hN02 hS hT]
  exact add_sub_cancel_right θ (C.travel m)

theorem n06_rightChartCandidate_reference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (θ : ℝ) :
    rightChartCandidate S C (C.referenceState, 0) m θ = θ := by
  simp only [rightChartCandidate, oddPart,
    n06_referenceReturn_argument hN01 hN02 hS hT]
  ring

theorem n06_rightChartInverse_reference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (θ : ℝ) :
    C.rightChartInverse (C.referenceState, 0) m θ = θ := by
  have hi := (hN02.1 (C.referenceState, 0)
    (n06_referenceReturn_neighborhood C base hN01.2.1)
    hN01.2.2.1.stateSector m θ).2.2.1
  simpa only [n06_rightChartCandidate_reference hN01 hN02 hS hT] using hi

theorem n06_returnResidualField_reference_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (θ : ℝ) :
    returnResidualField S C (C.referenceState, 0) m θ = 0 := by
  simp only [returnResidualField, evenPart,
    n06_referenceReturn_argument hN01 hN02 hS hT]
  ring

/-- The zero physical return residual is zero in the original circle
space, by that model's actual injective decode. -/
theorem n06_returnResidual_reference_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    R.residual (C.referenceState, 0) = 0 := by
  have hinjective : Function.Injective (S.circle (3 / 4 : ℝ)).decode :=
    (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  apply hinjective
  funext m θ
  have hdecode := hN02.2.1 (C.referenceState, 0)
    (n06_referenceReturn_neighborhood C base hN01.2.1)
    hN01.2.2.1.stateSector m θ
  have hzero := hdecode.trans (n06_returnResidualField_reference_zero hN01 hN02 hS hT m θ)
  simpa only [map_zero, Pi.zero_apply] using hzero

/-- The exact N03 error term vanishes when its actual residual argument
is zero. This is a consequence of the retained bilinear error, not an
extra equality imposed on the corrected coefficient fields. -/
theorem n06_correctedDivergence_eq_original_of_returnResidual_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hN03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (hzero : R.residual z = 0)
    (η : HeightPair S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (L.coefficients z) (heightPairField S η) p =
      divergenceOperator (originalCoefficients D S C z) (heightPairField S η) p := by
  have he := hN03.2.2.2.2.2.1 z hz hs η p hp
  rw [hzero] at he
  simp only [map_zero, LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at he
  exact (sub_eq_zero.mp he).symm

/-- At the reference state the actual corrected divergence agrees with
the original one on every member of the original physical height space. -/
theorem n06_correctedDivergence_reference_eq_original
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (η : HeightPair S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (L.coefficients (C.referenceState, 0)) (heightPairField S η) p =
      divergenceOperator (originalCoefficients D S C (C.referenceState, 0))
        (heightPairField S η) p :=
  n06_correctedDivergence_eq_original_of_returnResidual_zero hN03
    (n06_referenceReturn_neighborhood C base hN01.2.1) hN01.2.2.1.stateSector
    (n06_returnResidual_reference_zero hN01 hN02 hS hT) η hp

end ContinuousFlexibility.Statements
