module

public import ContinuousFlexibility.Analysis.N04PrincipalDividedAtlas

/-!
# The complete principal-atom interface

The five undivided fields determine the three stored cubic quotients.
The quotient construction keeps the same neighborhood, so all eight
principal atoms have their exact frozen current-data interface together.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem n04Principal_completeData {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hA : G.Data η (fun _ => True) b ε (G.atomFamily η .principalA) (G.atomRef η .principalA))
    (hAI : G.Data η (fun _ => True) b ε
      (G.atomFamily η .principalAInverse) (G.atomRef η .principalAInverse))
    (hB : G.Data η (fun _ => True) b ε (G.atomFamily η .principalB) (G.atomRef η .principalB))
    (hC : G.Data η (fun _ => True) b ε (G.atomFamily η .principalC) (G.atomRef η .principalC))
    (hV : G.Data η (fun _ => True) b ε (G.atomFamily η .potential) (G.atomRef η .potential)) :
    ∀ a : Atom, atomIsPrincipal a →
      G.Data η (fun _ => True) b ε (G.atomFamily η a) (G.atomRef η a) := by
  have hAP : G.Data η (G.Pos η) b ε
      (G.atomFamily η .principalA) (G.atomRef η .principalA) :=
    hA.mono (fun _ _ => trivial) le_rfl le_rfl (G.cost_nonneg η).1 (G.cost_nonneg η).2.1
  have hBP : G.Data η (G.Pos η) b ε
      (G.atomFamily η .principalB) (G.atomRef η .principalB) :=
    hB.mono (fun _ _ => trivial) le_rfl le_rfl (G.cost_nonneg η).1 (G.cost_nonneg η).2.1
  have hCP : G.Data η (G.Pos η) b ε
      (G.atomFamily η .principalC) (G.atomRef η .principalC) :=
    hC.mono (fun _ _ => trivial) le_rfl le_rfl (G.cost_nonneg η).1 (G.cost_nonneg η).2.1
  have hDA : G.Data η (fun _ => True) b ε
      (G.atomFamily η .dividedA) (G.atomRef η .dividedA) :=
    G.n04PrincipalDivided_data h η href 0 hAP
  have hDB : G.Data η (fun _ => True) b ε
      (G.atomFamily η .dividedB) (G.atomRef η .dividedB) :=
    G.n04PrincipalDivided_data h η href 1 hBP
  have hDC : G.Data η (fun _ => True) b ε
      (G.atomFamily η .dividedC) (G.atomRef η .dividedC) :=
    G.n04PrincipalDivided_data h η href 2 hCP
  intro a ha
  cases a <;> simp only [atomIsPrincipal] at ha
  case principalA => exact hA
  case principalAInverse => exact hAI
  case principalB => exact hB
  case principalC => exact hC
  case potential => exact hV
  case dividedA => exact hDA
  case dividedB => exact hDB
  case dividedC => exact hDC

end N04RealizationGauge

end ContinuousFlexibility.Analysis
