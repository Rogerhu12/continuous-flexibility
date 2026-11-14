module

public import ContinuousFlexibility.Scalar.WeightedSmoothTameLinear
public import ContinuousFlexibility.Scalar.WeightedHeightAlgebra

/-!
# Pulling actual height families back to product parameter spaces

A state family can be evaluated on the first factor while the second
factor ranges freely. The source grading is exactly the prescribed sum
grading, with zero projection loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
  {f : X → ScalarHeightSpace S} {x0 : X}

theorem scalarHeight_uniformTameGerm_fst
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (hq : Monotone q) (hqt : WithSeminorms q)
    (y0 : Y) (hf : UniformTameGerm p (scalarHeightGrading S) x0 f) :
    UniformTameGerm (pairGrading p q) (scalarHeightGrading S) (x0, y0)
      (fun z : X × Y => f z.1) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  letI : LocallyConvexSpace ℝ X := ht.toLocallyConvexSpace
  letI : IsTopologicalAddGroup Y := hqt.isTopologicalAddGroup
  letI : ContinuousSMul ℝ Y := hqt.continuousSMul
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  have hfst := uniformTameGerm_continuousLinear
    (withSeminorms_pairGrading ht hqt) (x0, y0)
    (ContinuousLinearMap.fst ℝ X Y) (scalar_pair_fst_isTame p q)
  have hc := UniformTameGerm.comp
    (f := fun z : X × Y => z.1) (g := f) hfst hf
    (tamePairGrading_monotone hp hq) (withSeminorms_pairGrading ht hqt) hp
  simpa only [Function.comp_def] using hc

theorem scalarHeight_smoothTameOn_fst
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (hq : Monotone q) (hqt : WithSeminorms q)
    {U : Set X} (hU : IsOpen U)
    (hf : SmoothTameOn p (scalarHeightGrading S) U f) :
    SmoothTameOn (pairGrading p q) (scalarHeightGrading S) (U ×ˢ univ)
      (fun z : X × Y => f z.1) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  letI : LocallyConvexSpace ℝ X := ht.toLocallyConvexSpace
  letI : IsTopologicalAddGroup Y := hqt.isTopologicalAddGroup
  letI : ContinuousSMul ℝ Y := hqt.continuousSMul
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  have hfst := smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
    (ContinuousLinearMap.fst ℝ X Y) (scalar_pair_fst_isTame p q)
  have hc := smoothTameOn_comp_generic
    (f := fun z : X × Y => z.1) (g := f)
    (tamePairGrading_monotone hp hq) (withSeminorms_pairGrading ht hqt)
    ht hfst hf (fun _ hz => hz.1)
  simpa only [Function.comp_def] using hc

end ContinuousFlexibility.Statements
