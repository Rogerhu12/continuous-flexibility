import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Radial.MorseChainFullRealization

/-!
# Blueprint node R05a

The accumulating chain of Morse cells and joins for every admissible height sequence, with flatness and coefficient bounds.

Source: `paper/flexible-surface-readable/05-flat-end-chain.tex` lines 28–323.

Task file: `docs/tasks/R05a.md`. The geometry and uniform estimates are
constructed independently of the spectral input retained in this signature.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R05a (hR04 : R04Statement) : R05aStatement := by
  clear hR04
  exact Radial.exists_morseChainRealization

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.R05a
