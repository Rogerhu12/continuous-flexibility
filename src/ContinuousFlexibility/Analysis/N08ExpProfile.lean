module

public import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets
public import ContinuousFlexibility.Scalar.WeightedCompositionGerm

/-! # The actual exponential perturbation in the weak profile weight -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

private theorem n08_contDiff_exp_sub_one : ContDiff ℝ ∞ (fun a : ℝ => Real.exp a - 1) :=
  Real.contDiff_exp.sub contDiff_const

private theorem n08_exp_sub_one_zero : (fun a : ℝ => Real.exp a - 1) 0 = 0 := by simp

def n08ExpProfile (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : (S.height n08WeakControlWeight).Space) : (S.height n08WeakControlWeight).Space :=
  SobolevModelData.weightedCompositionMap hT (hS.1 n08WeakControlWeight)
    ((hS.2.2.2.1 n08WeakControlWeight).2.2) n08WeakControlWeight_pos
    n08_contDiff_exp_sub_one n08_exp_sub_one_zero u

theorem n08ExpProfile_decode (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : (S.height n08WeakControlWeight).Space) (p : PolarPoint) :
    (S.height n08WeakControlWeight).decode (n08ExpProfile hT hS u) p =
      Real.exp ((S.height n08WeakControlWeight).decode u p) - 1 :=
  congrFun (SobolevModelData.decode_weightedCompositionMap hT (hS.1 n08WeakControlWeight)
    ((hS.2.2.2.1 n08WeakControlWeight).2.2) n08WeakControlWeight_pos
    n08_contDiff_exp_sub_one n08_exp_sub_one_zero u) p

theorem n08ExpProfile_zero (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    n08ExpProfile hT hS 0 = 0 :=
  SobolevModelData.weightedCompositionMap_zero hT (hS.1 n08WeakControlWeight)
    ((hS.2.2.2.1 n08WeakControlWeight).2.2) n08WeakControlWeight_pos
    n08_contDiff_exp_sub_one n08_exp_sub_one_zero

theorem UniformTameGerm.n08ExpProfile
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {p : ℕ → Seminorm ℝ X} {x0 : X} {f : X → (S.height n08WeakControlWeight).Space}
    (hf : UniformTameGerm p (S.height n08WeakControlWeight).grading x0 f)
    (hf0 : f x0 = 0) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (S.height n08WeakControlWeight).grading x0
      (fun x => n08ExpProfile hT hS (f x)) :=
  hf.weightedComposition hf0 hT hS n08WeakControlWeight_pos
    n08_contDiff_exp_sub_one n08_exp_sub_one_zero hp ht

end ContinuousFlexibility.Statements
