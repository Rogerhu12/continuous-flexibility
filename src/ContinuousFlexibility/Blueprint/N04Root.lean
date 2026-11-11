import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Analysis.RootCompositionBounds
import ContinuousFlexibility.Analysis.RootCompositionSmooth

/-!
# Blueprint node N04Root

Even and odd parts of a smooth function under the substitution λ = x^(3/2), with fixed loss.

Source: `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1046–1211.

Task file: `docs/tasks/N04Root.md`.

The even root average preserves every finite derivative order. The odd
divided difference is the even root average of a smooth integral of the
middle derivative, giving exactly one derivative of loss. Ordinary jets
at the boundary are controlled by their negative-halfspace comparison.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04Root : RootCompositionTarget := by
  refine ⟨?_, exists_rootComposition_csBound⟩
  intro G hG
  exact ⟨contDiffOn_rootEven hG, contDiffOn_rootOdd hG⟩

/-- info: 'ContinuousFlexibility.Blueprint.N04Root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms N04Root

end ContinuousFlexibility.Blueprint
