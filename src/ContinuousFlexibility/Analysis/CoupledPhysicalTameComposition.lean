module

public import ContinuousFlexibility.Analysis.CoupledTameComposition
public import ContinuousFlexibility.Analysis.CoupledConstantCircle
public import ContinuousFlexibility.Scalar.WeightedStateTopology

/-!
# Composition in the original physical product and subspaces

These wrappers use the existing projective-limit equivalences for
products, real constants, and closed subspaces. They transport only the
chain rule; the input and output gradings remain the prescribed ones.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

section Subtraction

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y]

theorem coupled_smoothTameOn_sub
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    (hp : Monotone p) {U : Set X} {f g : X → Y}
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn p q U g) :
    SmoothTameOn p q U (fun x => f x - g x) := by
  have hn := solve_smoothTameOn_postcomp hg (-(ContinuousLinearMap.id ℝ Y))
    (r := q) (B := 1) zero_le_one (fun n y => by
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
        map_neg_eq_map, one_mul, le_refl])
  apply smoothTameOn_congr (smoothTameOn_add hp hf hn)
  intro x hx
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, sub_eq_add_neg]

end Subtraction

private def coupledHeightPairEquiv (S : PhysicalSpacesData) : HeightPair S ≃L[ℝ]
    ProjectiveLimit (fun n => (S.height (3 / 4 : ℝ)).level n × ℝ)
      (fun n => ((S.height (3 / 4 : ℝ)).bond n).prodMap (ContinuousLinearMap.id ℝ ℝ)) :=
  ((ContinuousLinearEquiv.refl ℝ (S.height (3 / 4 : ℝ)).Space).prodCongr
    (constEquiv ℝ)).trans
      (prodEquiv (fun n => (S.height (3 / 4 : ℝ)).level n) (S.height (3 / 4 : ℝ)).bond
        (fun _ => ℝ) (fun _ => ContinuousLinearMap.id ℝ ℝ))

private def coupledScalarOutputEquiv (S : PhysicalSpacesData) : (HeightPair S × ℝ) ≃L[ℝ]
    ProjectiveLimit (fun n => ((S.height (3 / 4 : ℝ)).level n × ℝ) × ℝ)
      (fun n => (((S.height (3 / 4 : ℝ)).bond n).prodMap
        (ContinuousLinearMap.id ℝ ℝ)).prodMap (ContinuousLinearMap.id ℝ ℝ)) :=
  ((coupledHeightPairEquiv S).prodCongr (constEquiv ℝ)).trans
    (prodEquiv (fun n => (S.height (3 / 4 : ℝ)).level n × ℝ)
      (fun n => ((S.height (3 / 4 : ℝ)).bond n).prodMap (ContinuousLinearMap.id ℝ ℝ))
      (fun _ => ℝ) (fun _ => ContinuousLinearMap.id ℝ ℝ))

section PhysicalComposition

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
  {U : Set X} {V : Set Y} {f : X → Y}
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem coupled_smoothTameOn_comp_heightPair
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    {g : Y → HeightPair S}
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn q (heightPairGrading S) V g)
    (hmap : MapsTo f U V) :
    SmoothTameOn p (heightPairGrading S) U (g ∘ f) := by
  letI : ∀ n, CompleteSpace ((S.height (3 / 4 : ℝ)).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 (3 / 4 : ℝ)) n
  exact coupled_smoothTameOn_comp_equiv hp htp htq (coupledHeightPairEquiv S) hf hg hmap

theorem coupled_smoothTameOn_comp_scalarOutput
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    {g : Y → HeightPair S × ℝ}
    (hf : SmoothTameOn p q U f)
    (hg : SmoothTameOn q (pairGrading (heightPairGrading S) realGrading) V g)
    (hmap : MapsTo f U V) :
    SmoothTameOn p (pairGrading (heightPairGrading S) realGrading) U (g ∘ f) := by
  letI : ∀ n, CompleteSpace ((S.height (3 / 4 : ℝ)).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 (3 / 4 : ℝ)) n
  exact coupled_smoothTameOn_comp_equiv hp htp htq (coupledScalarOutputEquiv S) hf hg hmap

theorem coupled_smoothTameOn_comp_source
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    {g : Y → S.Source}
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn q S.sourceGrading V g)
    (hmap : MapsTo f U V) : SmoothTameOn p S.sourceGrading U (g ∘ f) := by
  letI : ∀ n, CompleteSpace ((S.height (3 / 4 : ℝ)).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 (3 / 4 : ℝ)) n
  letI : ∀ n, CompleteSpace ↥(subLevel S.Q.toLinearMap.ker n) := fun n =>
    subLevel_completeSpace S.Q.toLinearMap.ker n
  exact coupled_smoothTameOn_comp_equiv hp htp htq
    (subspaceEquiv S.Q.toLinearMap.ker S.Q.isClosed_ker) hf hg hmap

theorem coupled_smoothTameOn_comp_constantCircle
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    {g : Y → CoupledConstantCircle hM}
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn q (coupledConstantCircleGrading hM) V g)
    (hmap : MapsTo f U V) : SmoothTameOn p (coupledConstantCircleGrading hM) U (g ∘ f) := by
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    (hM.2.1 n).isComplete.completeSpace_coe
  letI : ∀ n, CompleteSpace ↥(subLevel (coupledConstantCircleSubmodule hM) n) := fun n =>
    subLevel_completeSpace (coupledConstantCircleSubmodule hM) n
  exact coupled_smoothTameOn_comp_equiv hp htp htq
    (subspaceEquiv (coupledConstantCircleSubmodule hM) (coupledConstantCircle_isClosed hM))
    hf hg hmap

end PhysicalComposition

end ContinuousFlexibility.Analysis
