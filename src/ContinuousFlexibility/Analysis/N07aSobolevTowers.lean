module

public import ContinuousFlexibility.Analysis.N07aClosedTowers

/-!
# Lifting actual L² coordinate towers to a Sobolev model

Each finite Hilbert product is restricted to the model's closed weak
graph. The resulting levels are then restricted to the closed graph of
the actual bonding maps. Only the original values are identified; higher
graph relations follow from the genuine parameter difference quotients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
  {U : Set X} {g : X → A.Space}

/-- The finite coordinate towers take values in the actual closed level. -/
def n07aSobolevParameterLevelTower
    (hA : IsSobolevModel D T γ A) (hU : IsOpen U)
    (J : ∀ s (j : JetIndex s), SmoothDirections U (fun x => ((g x).val s).val j))
    (s : ℕ) : SmoothDirections U (fun x => (g x).val s) :=
  n07aSmoothDirectionsCodRestrict (A.level s) (hA.2.1 s)
    (smoothDirectionsScalarPostcompose (smoothDirectionsScalarPi hU (J s))
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : JetIndex s => CylinderL2)).symm.toContinuousLinearMap)
    (fun x => (g x).val s) (by
      intro x _
      apply PiLp.ext
      intro j
      rfl)

theorem n07aSobolevParameterLevelTower_D_coordinate
    (hA : IsSobolevModel D T γ A) (hU : IsOpen U)
    (J : ∀ s (j : JetIndex s), SmoothDirections U (fun x => ((g x).val s).val j))
    (s k : ℕ) {x : X} (hx : x ∈ U) (v : Fin k → X) (j : JetIndex s) :
    (((n07aSobolevParameterLevelTower hA hU J s).D k x v).val j) = (J s j).D k x v := by
  unfold n07aSobolevParameterLevelTower
  rw [n07aSmoothDirectionsCodRestrict_D_coe _ _ _ _ _ k hx v]
  rfl

/-- The actual model-valued map has a genuine tower as soon as all its
actual L² coordinates have genuine towers on the same open domain. -/
def n07aSobolevParameterTower
    (hA : IsSobolevModel D T γ A) (hU : IsOpen U)
    (J : ∀ s (j : JetIndex s), SmoothDirections U (fun x => ((g x).val s).val j)) :
    SmoothDirections U g :=
  n07aSmoothDirectionsProjective hU
    (fun s => n07aSobolevParameterLevelTower hA hU J s) g (fun _ _ _ => rfl)

/-- The model derivative keeps exactly the original L² coordinate. -/
theorem n07aSobolevParameterTower_D_coordinate
    (hA : IsSobolevModel D T γ A) (hU : IsOpen U)
    (J : ∀ s (j : JetIndex s), SmoothDirections U (fun x => ((g x).val s).val j))
    (k : ℕ) {x : X} (hx : x ∈ U) (v : Fin k → X) (s : ℕ) (j : JetIndex s) :
    (((n07aSobolevParameterTower hA hU J).D k x v).val s).val j = (J s j).D k x v := by
  unfold n07aSobolevParameterTower
  rw [n07aSmoothDirectionsProjective_D_coordinate _ _ _ _ k hx v s]
  exact n07aSobolevParameterLevelTower_D_coordinate hA hU J s k hx v j

end ContinuousFlexibility.Analysis
