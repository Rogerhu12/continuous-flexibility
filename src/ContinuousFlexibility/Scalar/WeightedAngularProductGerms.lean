module

public import ContinuousFlexibility.Scalar.WeightedOddProductMap
public import ContinuousFlexibility.Scalar.WeightedAngularJetProductBounds
public import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations

/-!
# Actual uniform tame germs for the two angular product operations

The continuous bilinear maps and their one-high-factor estimates give one
common neighborhood for the entire genuine tower. Both operations can then
be composed with the finite state ingredients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements.SobolevModelData

open ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

private theorem oneHigh_pair_of_fin_two
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (M : (Fin 2 → E) → E) {base loss : ℕ}
    (hM : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin 2 → E,
      p s (M u) ≤ C * ∑ i, p (s + loss) (u i) *
        ∏ j ∈ Finset.univ.erase i, p base (u j)) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : E,
      p s (M ![x, y]) ≤
        C * (p (s + loss) x * p base y + p base x * p (s + loss) y) := by
  intro s
  obtain ⟨C, hC, hCu⟩ := hM s
  refine ⟨C, hC, fun x y => ?_⟩
  rw [← oneHigh_fin_two (p base) (p (s + loss)) x y]
  exact hCu ![x, y]

theorem oddProductPrimitiveMap_oneHigh_pair
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : A.Space,
      A.grading s (oddProductPrimitiveMap hT hA hinterp hγ ![x, y]) ≤
        C * (A.grading (s + loss) x * A.grading base y +
          A.grading base x * A.grading (s + loss) y) := by
  obtain ⟨base, loss, hbase, hbound⟩ := oddProductPrimitiveMap_oneHigh hT hA hinterp hγ
  exact ⟨base, loss, hbase, oneHigh_pair_of_fin_two A.grading
    (oddProductPrimitiveMap hT hA hinterp hγ) hbound⟩

theorem oddProductPrimitiveMap_uniformTameGerm
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) (z0 : A.Space × A.Space) :
    UniformTameGerm (pairGrading A.grading A.grading) A.grading z0
      (fun z : A.Space × A.Space => oddProductPrimitiveMap hT hA hinterp hγ ![z.1, z.2]) := by
  obtain ⟨base, loss, _, hbound⟩ := oddProductPrimitiveMap_oneHigh_pair hT hA hinterp hγ
  exact uniformTameGerm_bilinearMultilinear
    (p := A.grading) (q := A.grading) (base := base) (loss := loss) (oddProductPrimitiveMap hT hA hinterp hγ)
    (fun s _ => hbound s)
    (withSeminorms_graded (fun n => A.level n) A.bond) z0

theorem angularJetProductMap_uniformTameGerm
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) (z0 : A.Space × A.Space) :
    UniformTameGerm (pairGrading A.grading A.grading) A.grading z0
      (fun z : A.Space × A.Space => angularJetProductMap hT hA hinterp hγ ![z.1, z.2]) := by
  obtain ⟨base, loss, _, hbound⟩ := angularJetProductMap_oneHigh hT hA hinterp hγ
  exact uniformTameGerm_bilinearMultilinear
    (p := A.grading) (q := A.grading) (base := base) (loss := loss) (angularJetProductMap hT hA hinterp hγ)
    (fun s _ => hbound s)
    (withSeminorms_graded (fun n => A.level n) A.bond) z0

end ContinuousFlexibility.Statements.SobolevModelData
