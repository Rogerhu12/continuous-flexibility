module

public import ContinuousFlexibility.Scalar.WeightedOddHeightAlgebra
public import ContinuousFlexibility.Scalar.WeightedAngularJetProductBounds
public import ContinuousFlexibility.Scalar.WeightedHeightGerms

/-!
# Uniform tame germs for the actual odd scalar algebra

Odd fields are kept as decoded angular derivatives of even primitives.
Their products use the proved continuous bilinear maps and the corresponding
one-high-factor estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {x0 : X} {f g : X → ScalarHeightSpace S}

theorem UniformTameGerm.scalarHeightOddMul
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hg : UniformTameGerm p (scalarHeightGrading S) x0 g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarHeightOddMul hT hS (f x) (g x)) := by
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  obtain ⟨base, loss, _, hbound⟩ := SobolevModelData.oddProductPrimitiveMap_oneHigh
    hT (hS.1 scalarBeta) (scalarHeightInterpolation hS) scalarBeta_pos
  let B := SobolevModelData.oddProductPrimitiveMap
    hT (hS.1 scalarBeta) (scalarHeightInterpolation hS) scalarBeta_pos
  have hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ScalarHeightSpace S,
        scalarHeightGrading S s (bilinearJetValue B u v) ≤
          C * (scalarHeightGrading S (s + loss) u * scalarHeightGrading S base v +
            scalarHeightGrading S base u * scalarHeightGrading S (s + loss) v) := by
    intro s _
    obtain ⟨C, hC, hCu⟩ := hbound s
    refine ⟨C, hC, fun u v => ?_⟩
    change scalarHeightGrading S s (B ![u, v]) ≤ _
    rw [← oneHigh_fin_two (scalarHeightGrading S base)
      (scalarHeightGrading S (s + loss)) u v]
    exact hCu ![u, v]
  exact hf.bilinear hg B hB hp ht (scalarHeightGrading_monotone S)
    (weighted_scalarHeightGrading_withSeminorms S)

theorem UniformTameGerm.scalarHeightOddUnitalAct
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hg : UniformTameGerm p (scalarHeightGrading S) x0 g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarHeightOddUnitalAct hT hS (f x) (g x)) :=
  hg.add (hf.scalarHeightOddMul hg hT hS hp ht) hp ht

theorem UniformTameGerm.scalarHeightAngularMul
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hg : UniformTameGerm p (scalarHeightGrading S) x0 g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarHeightAngularMul hT hS (f x) (g x)) := by
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  obtain ⟨base, loss, _, hbound⟩ := SobolevModelData.angularJetProductMap_oneHigh
    hT (hS.1 scalarBeta) (scalarHeightInterpolation hS) scalarBeta_pos.le
  exact hf.bilinear hg
    (SobolevModelData.angularJetProductMap hT (hS.1 scalarBeta)
      (scalarHeightInterpolation hS) scalarBeta_pos.le)
    (fun s _ => hbound s) hp ht (scalarHeightGrading_monotone S)
    (weighted_scalarHeightGrading_withSeminorms S)

end ContinuousFlexibility.Statements
