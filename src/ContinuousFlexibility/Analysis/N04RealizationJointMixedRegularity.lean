import ContinuousFlexibility.Analysis.JointMixedTransportCalculus
import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
import ContinuousFlexibility.Analysis.N04RealizationJointMixedSlotBounds

/-!
# Actual mixed towers on the original product domain

The existing radial and angular tower constructors differentiate the
same scalar field. Freezing the spatial point therefore gives genuine
parameter towers of every mixed derivative, with no new neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint} {f : E × PolarPoint → ℝ}

/-- The genuine joint tower of each actual mixed spatial derivative. -/
def n04Realization_jointMixedTower
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (a b : ℕ) :
    SmoothDirections (U ×ˢ V)
      (fun z => mixedDerivative a b (fun p => f (z.1, p)) z.2) := by
  induction a with
  | zero =>
      induction b with
      | zero => exact J.congrOn (fun _ _ => by simp only [mixedDerivative, iteratedDeriv_zero])
      | succ b ih =>
          exact (ih.spatialAngularTower hV hc).congrOn (fun z hz =>
            angularPartial_mixedDerivative_of_contDiffOn hV
              (J.spatial_value_contDiffOn hV z.1 hz.1) 0 b hz.2)
  | succ a ih =>
      exact (ih.spatialRadialTower hV hc).congrOn (fun z hz =>
        radialPartial_mixedDerivative_of_contDiffOn hV
          (J.spatial_value_contDiffOn hV z.1 hz.1) a b hz.2)

theorem n04Realization_jointMixedTower_apply
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (a b n : ℕ) (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ V)
    (v : Fin n → E × PolarPoint) :
    (n04Realization_jointMixedTower J hV hc a b).D n (x, q) v =
      mixedDerivative a b (fun p => J.D n (x, p) v) q := by
  induction a generalizing n with
  | zero =>
      induction b generalizing n with
      | zero =>
          change J.D n (x, q) v = _
          simp only [mixedDerivative, iteratedDeriv_zero]
      | succ b ih =>
          change ((n04Realization_jointMixedTower J hV hc 0 b).fixedLast
            (0, (0, 1))).D n (x, q) v = _
          rw [SmoothDirections.fixedLast_apply, ih]
          simpa only [SmoothDirections.fixedLast_apply] using
            (J.jointJet_mixed_angular_step hV hc 0 b n x hx v hq).symm
  | succ a ih =>
      change ((n04Realization_jointMixedTower J hV hc a b).fixedLast
        (0, (1, 0))).D n (x, q) v = _
      rw [SmoothDirections.fixedLast_apply, ih]
      simpa only [SmoothDirections.fixedLast_apply] using
        (J.jointJet_mixed_radial_step hV hc a b n x hx v hq).symm

/-- Every actual mixed spatial derivative has its parameter tower on U. -/
def n04Realization_jointMixedRegularity
    (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V)) :
    MixedJetRegularity U V (fun x q => f (x, q)) where
  spatial x hx := J.spatial_value_contDiffOn hV x hx
  parameter a b q hq :=
    (n04Realization_jointMixedTower J hV hc a b).freezeSpatial hU q hq

/-- Uniqueness identifies any supplied actual mixed parameter tower with
the mixed spatial derivative of the same joint tower. -/
theorem n04Realization_mixedParameter_eq_joint
    (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (a b n : ℕ) (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ V)
    (Q : SmoothDirections U
      (fun z => mixedDerivative a b (fun p => f (z, p)) q))
    (v : Fin n → E) :
    Q.D n x v = mixedDerivative a b (fun p => J.D n (x, p) (fun i => (v i, 0))) q := by
  rw [Q.unique ((n04Realization_jointMixedTower J hV hc a b).freezeSpatial hU q hq)
    n x hx, SmoothDirections.freezeSpatial_apply]
  exact n04Realization_jointMixedTower_apply J hV hc a b n x hx q hq (fun i => (v i, 0))

end ContinuousFlexibility.Analysis
