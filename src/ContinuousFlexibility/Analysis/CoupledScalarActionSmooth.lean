import ContinuousFlexibility.Scalar.WeightedSmoothTameAlgebra
import ContinuousFlexibility.Analysis.CoupledPhysicalTameComposition
import ContinuousFlexibility.Analysis.CoupledControlResponseSmooth

/-!
# Smooth scalar action on the actual output spaces

The independent real parameter multiplies the recovered scalar error.
The same continuous bilinear action supplies its full directional tower,
and composition keeps the whole given parameter domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements

section ScalarAction

variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

theorem coupled_scalarAction_smoothTameOn (q : ℕ → Seminorm ℝ F) :
    SmoothTameOn (pairGrading realGrading q) q univ
      (fun z : ℝ × F => z.1 • z.2) := by
  have hB : ∀ s, 0 ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ × F,
      q s (bilinearJetValue (scalarSMulPairMultilinear (F := F)) x y) ≤
        C * (pairGrading realGrading q (s + 0) x * pairGrading realGrading q 0 y +
          pairGrading realGrading q 0 x * pairGrading realGrading q (s + 0) y) := by
    intro s _
    refine ⟨1, zero_le_one, fun x y => ?_⟩
    rw [scalarSMulPairMultilinear_apply, map_smul_eq_mul]
    simp only [one_mul, Nat.add_zero]
    have hx : ‖x.1‖ ≤ pairGrading realGrading q 0 x :=
      le_add_of_nonneg_right (apply_nonneg (q 0) x.2)
    have hy : q s y.2 ≤ pairGrading realGrading q s y :=
      le_add_of_nonneg_left (norm_nonneg y.1)
    exact (mul_le_mul hx hy (apply_nonneg _ _) (apply_nonneg _ _)).trans
      (le_add_of_nonneg_left (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  exact smoothTameOn_quadratic (scalarSMulPairMultilinear (F := F)) hB

end ScalarAction

section SourceComposition

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {p : ℕ → Seminorm ℝ X} {U : Set X} {a : X → ℝ} {f : X → S.Source}

theorem coupled_smoothTameOn_source_smul
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (ha : SmoothTameOn p realGrading U a)
    (hf : SmoothTameOn p S.sourceGrading U f) :
    SmoothTameOn p S.sourceGrading U (fun x => a x • f x) := by
  have hq : WithSeminorms (pairGrading realGrading S.sourceGrading) :=
    withSeminorms_pairGrading weighted_realGrading_withSeminorms
      (coupled_sourceGrading_withSeminorms S)
  letI : LocallyConvexSpace ℝ (ℝ × S.Source) := hq.toLocallyConvexSpace
  exact coupled_smoothTameOn_comp_source hS hp ht hq
    (smoothTameOn_prodMk_generic hp ht ha hf)
    (coupled_scalarAction_smoothTameOn S.sourceGrading) (fun _ _ => mem_univ _)

end SourceComposition

end ContinuousFlexibility.Analysis
