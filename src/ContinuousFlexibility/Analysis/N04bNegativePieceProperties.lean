module

public import ContinuousFlexibility.Analysis.N04bActualClosedTravel
public import ContinuousFlexibility.Analysis.N04bRootLiteralGerms
public import ContinuousFlexibility.Analysis.N04bInverseGermCongruence

/-!
# Named output properties of one genuinely constructed negative piece

The domain and both comparison formulas are the actual travel
constructions of the same cumulative N03 witness. This interface records
the consequences proved for the literal pasted functions; it supplies no
additional hypothesis to the upstream field construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

def n04bActualNegativeDomain (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (z : AnnularState S × ℝ) (m : ℕ) (side : Bool) :
    Set PolarPoint :=
  n04bTravelHalfDomain (Ioo (C.left m) (C.right m) ×ˢ univ)
    (n04bActualTravelChart S C L z m) (C.travel m) side

structure N04bNegativePieceProperties
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) (m : ℕ) (side : Bool)
    (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ)
    (J : PolarPoint → PolarPoint) : Prop where
  closed_chart_eq : EqOn F
    (n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side)
    (closure (n04bActualNegativeDomain S C L z m side))
  closed_inverse_eq : EqOn J
    (n04bRootPhysicalInverse (n04bActualClosedTravelInverse S C L z m) (C.travel m) side)
    (Icc (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ univ)
  chart_physical_germ : ∀ p : PolarPoint,
    0 < (n04bRootAffine (if side then C.right m else C.left m) side p).1 →
      F =ᶠ[𝓝 p] n04bRootPhysicalChart
        (n04bActualTravelChart S C L z m) (C.travel m) side
  height_physical_germ : ∀ p : PolarPoint,
    0 < (n04bRootAffine (if side then C.right m else C.left m) side p).1 →
      h =ᶠ[𝓝 p] n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) side
  inverse_physical_germ : ∀ q : PolarPoint, 0 < q.1 →
    J =ᶠ[𝓝 q] n04bRootPhysicalInverse
      (n04bActualTravelInverse S C L z m) (C.travel m) side
  closed_regular : ∀ p ∈ closure (n04bActualNegativeDomain S C L z m side),
    ContDiffAt ℝ ∞ F p ∧ ContDiffAt ℝ ∞ h p ∧ planeJacobian F p ≠ 0 ∧ 0 < h p
  inverse_regular : ∀ q ∈ Icc (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ),
    ContDiffAt ℝ ∞ J q
  boundary_inverse : ∀ p ∈ closure (n04bActualNegativeDomain S C L z m side),
    CanonicalBoundaryInverseGerm F J p

end ContinuousFlexibility.Analysis
