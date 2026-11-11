import ContinuousFlexibility.Scalar.WeightedCompositionGerm
import ContinuousFlexibility.Scalar.WeightedHeightAlgebra
import ContinuousFlexibility.Scalar.WeightedPowerExtension

/-!
# Actual weighted scalar power perturbations

The canonical composition lift is globally defined. On the fixed scalar
interval its decoder is the literal power minus its constant background.
Every state germ vanishing at its center inherits the same genuine uniform
tame-germ property.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def scalarHeightPower (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (α : ℝ) (u : ScalarHeightSpace S) : ScalarHeightSpace S :=
  SobolevModelData.weightedCompositionMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos
    (scalarPowerPerturbation_contDiff α) (scalarPowerPerturbation_zero α) u

theorem decode_scalarHeightPower
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (α : ℝ) (u : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarHeightPower hT hS α u) p =
      scalarPowerPerturbation α ((S.height scalarBeta).decode u p) :=
  congrFun (SobolevModelData.decode_weightedCompositionMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos
    (scalarPowerPerturbation_contDiff α) (scalarPowerPerturbation_zero α) u) p

theorem scalarHeightPower_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (α : ℝ) :
    scalarHeightPower hT hS α 0 = 0 :=
  SobolevModelData.weightedCompositionMap_zero hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos
    (scalarPowerPerturbation_contDiff α) (scalarPowerPerturbation_zero α)

theorem decode_scalarHeightPower_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (α : ℝ) (u : ScalarHeightSpace S) {p : PolarPoint}
    (hp : |(S.height scalarBeta).decode u p| ≤ 1 / 2) :
    (S.height scalarBeta).decode (scalarHeightPower hT hS α u) p =
      (1 + (S.height scalarBeta).decode u p) ^ α - 1 := by
  rw [decode_scalarHeightPower]
  exact scalarPowerPerturbation_eq α hp

theorem decode_scalarHeightPower_half
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) {p : PolarPoint}
    (hp : |(S.height scalarBeta).decode u p| ≤ 1 / 2) :
    (S.height scalarBeta).decode (scalarHeightPower hT hS (1 / 2 : ℝ) u) p =
      Real.sqrt (1 + (S.height scalarBeta).decode u p) - 1 := by
  rw [decode_scalarHeightPower]
  exact scalarPowerPerturbation_half_eq hp

theorem decode_scalarHeightPower_neg_one
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) {p : PolarPoint}
    (hp : |(S.height scalarBeta).decode u p| ≤ 1 / 2) :
    (S.height scalarBeta).decode (scalarHeightPower hT hS (-1 : ℝ) u) p =
      (1 + (S.height scalarBeta).decode u p)⁻¹ - 1 := by
  rw [decode_scalarHeightPower]
  exact scalarPowerPerturbation_neg_one_eq hp

theorem decode_scalarHeightPower_neg_half
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) {p : PolarPoint}
    (hp : |(S.height scalarBeta).decode u p| ≤ 1 / 2) :
    (S.height scalarBeta).decode (scalarHeightPower hT hS (-(1 / 2) : ℝ) u) p =
      (Real.sqrt (1 + (S.height scalarBeta).decode u p))⁻¹ - 1 := by
  rw [decode_scalarHeightPower]
  exact scalarPowerPerturbation_neg_half_eq hp

theorem decode_scalarHeightPower_neg_three_halves
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) {p : PolarPoint}
    (hp : |(S.height scalarBeta).decode u p| ≤ 1 / 2) :
    (S.height scalarBeta).decode (scalarHeightPower hT hS (-(3 / 2) : ℝ) u) p =
      inverseDThreeHalves (1 + (S.height scalarBeta).decode u p) - 1 := by
  rw [decode_scalarHeightPower]
  exact scalarPowerPerturbation_neg_three_halves_eq hp

theorem UniformTameGerm.scalarHeightPower
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {p : ℕ → Seminorm ℝ X} {x0 : X} {f : X → ScalarHeightSpace S}
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f) (hf0 : f x0 = 0)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (α : ℝ)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarHeightPower hT hS α (f x)) :=
  hf.weightedComposition hf0 hT hS scalarBeta_pos
    (scalarPowerPerturbation_contDiff α) (scalarPowerPerturbation_zero α) hp ht

end ContinuousFlexibility.Statements
