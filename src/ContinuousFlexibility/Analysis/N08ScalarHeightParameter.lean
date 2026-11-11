import ContinuousFlexibility.Analysis.N08Neighborhoods
import ContinuousFlexibility.Scalar.WeightedStatePrimitives
import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations

/-! # The actual height coordinates in the scalar finite-jet calculus -/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

section Abstract

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

private def n08_heightParameterCLM : ((E × ℝ) × F) × ℝ →L[ℝ] ((E × E) × ℝ) × ℝ where
  toFun z := (((0, z.1.1.1), z.1.1.2), z.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, zero_add]
  map_smul' c x := by
    simp only [Prod.smul_mk, Prod.fst_smul, Prod.snd_smul, smul_zero]
  cont := ((continuous_const.prodMk continuous_fst.fst.fst).prodMk
    continuous_fst.fst.snd).prodMk continuous_snd

private theorem n08_heightParameterCLM_tame
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    IsTameLinear (pairGrading (pairGrading (pairGrading p realGrading) q) realGrading)
      (pairGrading (pairGrading (pairGrading p p) realGrading) realGrading)
      (n08_heightParameterCLM (E := E) (F := F)).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun z => ?_⟩
  change ((p s 0 + p s z.1.1.1) + |z.1.1.2|) + |z.2| ≤
    (1 : ℝ) * ((p (s + 0) z.1.1.1 + |z.1.1.2| + q (s + 0) z.1.2) + |z.2|)
  simp only [map_zero, zero_add, NNReal.coe_one, one_mul, Nat.add_zero]
  have hq := apply_nonneg (q s) z.1.2
  linarith

end Abstract

def n08ScalarHeightParameter (S : PhysicalSpacesData) :
    AnnularState S × ℝ →L[ℝ] ScalarWeightedState S := n08_heightParameterCLM

theorem n08ScalarHeightParameter_apply (S : PhysicalSpacesData) (z : AnnularState S × ℝ) :
    n08ScalarHeightParameter S z = (((0, z.1.1.1), z.1.1.2), z.2) := rfl

theorem n08ScalarHeightParameter_increment (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) :
    scalarStateIncrement S (n08ScalarHeightParameter S z) = stateU S z.1 := rfl

theorem n08ScalarHeightParameter_isTame (S : PhysicalSpacesData) :
    IsTameLinear (pairGrading (stateGrading S) realGrading) (scalarStateGrading S)
      (n08ScalarHeightParameter S).toLinearMap 0 0 :=
  n08_heightParameterCLM_tame (S.height (3 / 4 : ℝ)).grading
    (pairGrading realGrading
      (pairGrading (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading))

theorem n08ScalarHeightParameter_uniformTameGerm (S : PhysicalSpacesData)
    (z0 : AnnularState S × ℝ) :
    UniformTameGerm (pairGrading (stateGrading S) realGrading) (scalarStateGrading S)
      z0 (n08ScalarHeightParameter S) :=
  uniformTameGerm_continuousLinear
    (withSeminorms_pairGrading (solve_stateGrading_withSeminorms S)
      weighted_realGrading_withSeminorms) z0
    (n08ScalarHeightParameter S) (n08ScalarHeightParameter_isTame S)

end ContinuousFlexibility.Statements
