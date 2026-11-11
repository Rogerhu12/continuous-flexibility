import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.FinCases

/-!
# Fixing one input of a genuine continuous bilinear map

These are actual continuous linear maps in the original topologies. They
avoid imposing a separate topology on a curried operator space.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

def scalarBilinearFixLeft
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) (x : E) : E →L[ℝ] F :=
  B.toContinuousLinearMap ![x, 0] 1

def scalarBilinearFixRight
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) (y : E) : E →L[ℝ] F :=
  B.toContinuousLinearMap ![0, y] 0

theorem scalarBilinearFixLeft_apply
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) (x y : E) :
    scalarBilinearFixLeft B x y = B ![x, y] := by
  change B (Function.update ![x, 0] 1 y) = B ![x, y]
  apply congrArg B
  funext i
  fin_cases i <;> simp

theorem scalarBilinearFixRight_apply
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) (x y : E) :
    scalarBilinearFixRight B y x = B ![x, y] := by
  change B (Function.update ![0, y] 0 x) = B ![x, y]
  apply congrArg B
  funext i
  fin_cases i <;> simp

end ContinuousFlexibility.Statements
