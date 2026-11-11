import ContinuousFlexibility.Scalar.WeightedOddProductMap
import ContinuousFlexibility.Scalar.WeightedAngularJetProductBounds
import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations

/-!
# Actual uniform tame germs for the two angular product operations

The continuous bilinear maps and their one-high-factor estimates give one
common neighborhood for the entire genuine tower. Both operations can then
be composed with the finite state ingredients.
-/

noncomputable section

namespace ContinuousFlexibility.Statements.SobolevModelData

open ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

theorem oddProductPrimitiveMap_oneHigh_pair
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : A.Space,
      A.grading s (oddProductPrimitiveMap hT hA hinterp hγ ![x, y]) ≤
        C * (A.grading (s + loss) x * A.grading base y +
          A.grading base x * A.grading (s + loss) y) := by
  classical
  obtain ⟨base, loss, hbase, hbound⟩ := oddProductPrimitiveMap_oneHigh hT hA hinterp hγ
  refine ⟨base, loss, hbase, ?_⟩
  intro s
  obtain ⟨C, hC, hCu⟩ := hbound s
  refine ⟨C, hC, fun x y => ?_⟩
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simpa only [Fin.sum_univ_two, h0, h1, Finset.prod_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm] using hCu ![x, y]

theorem oddProductPrimitiveMap_uniformTameGerm
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) (z0 : A.Space × A.Space) :
    UniformTameGerm (pairGrading A.grading A.grading) A.grading z0
      (fun z : A.Space × A.Space => oddProductPrimitiveMap hT hA hinterp hγ ![z.1, z.2]) := by
  obtain ⟨base, loss, _, hbound⟩ := oddProductPrimitiveMap_oneHigh_pair hT hA hinterp hγ
  exact uniformTameGerm_bilinearMultilinear (oddProductPrimitiveMap hT hA hinterp hγ)
    (fun s _ => hbound s)
    (withSeminorms_graded (fun n => A.level n) A.bond) z0

theorem angularJetProductMap_uniformTameGerm
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) (z0 : A.Space × A.Space) :
    UniformTameGerm (pairGrading A.grading A.grading) A.grading z0
      (fun z : A.Space × A.Space => angularJetProductMap hT hA hinterp hγ ![z.1, z.2]) := by
  obtain ⟨base, loss, _, hbound⟩ := angularJetProductMap_oneHigh hT hA hinterp hγ
  exact uniformTameGerm_bilinearMultilinear (angularJetProductMap hT hA hinterp hγ)
    (fun s _ => hbound s)
    (withSeminorms_graded (fun n => A.level n) A.bond) z0

end ContinuousFlexibility.Statements.SobolevModelData
