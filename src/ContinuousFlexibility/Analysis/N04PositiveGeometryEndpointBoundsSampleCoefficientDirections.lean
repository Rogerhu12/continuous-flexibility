module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsFactored

/-!
# Genuine joint towers of the original root coefficients

The inward drift is the fixed oriented projection of the actual physical
root fields. The factored speed uses its original genuine trace tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff

def n04PositiveGeometry_rootRawCoefficient (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (g : ℝ → ℝ) (r σ : ℝ) (speed : Bool)
    (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  if speed then factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ
  else orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) r σ

theorem n04PositiveGeometry_orientedDrift_eq_projection
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (r σ : ℝ) :
    orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) r σ =
      (fun p => (σ • ContinuousLinearMap.fst ℝ ℝ ℝ)
        (n06PhysicalRootFields D S C z (rootProfileShift r σ p))) := by
  funext p
  simp only [smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
    n06PhysicalRootFields, orientedCharacteristicDrift]

theorem n04PositiveGeometry_rootDrift_projection_norm {σ : ℝ} (hσ : |σ| ≤ 1) :
    ‖σ • ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul hσ (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
    (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

local instance n04PositiveSampleCoefficientDirectionsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

def n04PositiveGeometry_rootRawCoefficientTrace_joint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (σ : ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : 0 < g 0)
    (speed : Bool) (a : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun y => radialBoundaryJet (n04PositiveGeometry_rootRawCoefficient
        D S C g r σ speed (liftSectorParameter S C y.1)) 0 a y.2) := by
  cases speed with
  | false =>
      apply (n04Realization_orientedRootFieldTrace_joint hT hS hN hε hr hroot σ
        (σ • ContinuousLinearMap.fst ℝ ℝ ℝ) a).congr
      intro y _
      exact congrArg (fun f : PolarPoint → ℝ => radialBoundaryJet f 0 a y.2)
        (n04PositiveGeometry_orientedDrift_eq_projection D S C
          (liftSectorParameter S C y.1) r σ).symm
  | true =>
      exact n04Realization_factoredRootSpeedTrace_joint
        hT hS hN hε hr hroot σ g hg hg0 a

end ContinuousFlexibility.Analysis
