import ContinuousFlexibility.Scalar.WeightedSmoothTameLinear
import ContinuousFlexibility.Scalar.WeightedOddHeightAlgebra
import ContinuousFlexibility.Scalar.WeightedAngularProductGerms
import ContinuousFlexibility.Scalar.WeightedProductTower

/-!
# Actual height products on unchanged smooth tame domains

The three bilinear height operations act on arbitrary common open source
domains. The domain is retained, so independent height parameters can
range over their entire spaces.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem smoothTameOn_scalarHeight_postcompose
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {X Y : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {U : Set X} {f : X → Y} {loss base : ℕ}
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) (hqt : WithSeminorms q)
    (hf : SmoothTameOn p q U f)
    (L : Y →L[ℝ] ScalarHeightSpace S)
    (hL : IsTameLinear q (scalarHeightGrading S) L.toLinearMap loss base) :
    SmoothTameOn p (scalarHeightGrading S) U (fun x => L (f x)) := by
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  exact smoothTameOn_postcompose_generic hp ht hqt hf L hL

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {U : Set X}
  {f g : X → ScalarHeightSpace S}

theorem smoothTameOn_scalarHeightMul
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (hf : SmoothTameOn p (scalarHeightGrading S) U f)
    (hg : SmoothTameOn p (scalarHeightGrading S) U g) :
    SmoothTameOn p (scalarHeightGrading S) U
      (fun x => scalarHeightMul hT hS (f x) (g x)) := by
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  obtain ⟨base, loss, _, hB⟩ := SobolevModelData.decodedProductMap_twoFactor
    hT (hS.1 scalarBeta) (scalarHeightInterpolation hS) scalarBeta_pos.le
  exact smoothTameOn_bilinear_comp
    (f := f) (g := g) (p := p) (q := scalarHeightGrading S) (r := scalarHeightGrading S)
    (base := base) (loss := loss) hp ht (weighted_scalarHeightGrading_withSeminorms S)
    hf hg (SobolevModelData.decodedProductMap hT (hS.1 scalarBeta)
      (scalarHeightInterpolation hS) scalarBeta_pos.le 1) hB

theorem smoothTameOn_scalarHeightOddMul
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (hf : SmoothTameOn p (scalarHeightGrading S) U f)
    (hg : SmoothTameOn p (scalarHeightGrading S) U g) :
    SmoothTameOn p (scalarHeightGrading S) U
      (fun x => scalarHeightOddMul hT hS (f x) (g x)) := by
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  obtain ⟨base, loss, _, hB⟩ := SobolevModelData.oddProductPrimitiveMap_oneHigh_pair
    hT (hS.1 scalarBeta) (scalarHeightInterpolation hS) scalarBeta_pos
  exact smoothTameOn_bilinear_comp
    (f := f) (g := g) (p := p) (q := scalarHeightGrading S) (r := scalarHeightGrading S)
    (base := base) (loss := loss) hp ht (weighted_scalarHeightGrading_withSeminorms S)
    hf hg (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
      (scalarHeightInterpolation hS) scalarBeta_pos) (fun s _ => hB s)

theorem smoothTameOn_scalarHeightAngularMul
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (hf : SmoothTameOn p (scalarHeightGrading S) U f)
    (hg : SmoothTameOn p (scalarHeightGrading S) U g) :
    SmoothTameOn p (scalarHeightGrading S) U
      (fun x => scalarHeightAngularMul hT hS (f x) (g x)) := by
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  obtain ⟨base, loss, _, hB⟩ := SobolevModelData.angularJetProductMap_oneHigh
    hT (hS.1 scalarBeta) (scalarHeightInterpolation hS) scalarBeta_pos.le
  exact smoothTameOn_bilinear_comp
    (f := f) (g := g) (p := p) (q := scalarHeightGrading S) (r := scalarHeightGrading S)
    (base := base) (loss := loss) hp ht (weighted_scalarHeightGrading_withSeminorms S)
    hf hg (SobolevModelData.angularJetProductMap hT (hS.1 scalarBeta)
      (scalarHeightInterpolation hS) scalarBeta_pos.le) (fun s _ => hB s)

end ContinuousFlexibility.Statements
