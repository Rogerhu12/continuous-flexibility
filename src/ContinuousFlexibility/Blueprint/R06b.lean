import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Radial.TailNaturalFull

/-!
# Blueprint node R06b

Deep tail: the unique square-integrable line, its decay, and the localized Green kernel.

Source: `paper/flexible-surface-readable/05-flat-end-chain.tex` lines 513–790.

Task file: `docs/tasks/R06b.md`. The natural line and the actual localized
kernel are constructed in `Radial.TailNaturalFull`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R06b : R06bStatement := by
  intro C η₀ K₀ hC hη₀ hη₁ hK₀ hOperator
  refine ⟨C, min η₀ (1 / 16), max K₀ 32, hC,
    lt_min hη₀ (by norm_num), (min_le_left _ _).trans_lt hη₁,
    hK₀.trans_le (le_max_left _ _), ?_⟩
  intro T hT hη hK
  obtain ⟨hI, hIₙ, G, hnorm, hgraph, hinverse, htrunc⟩ :=
    hOperator T hT (hη.trans (min_le_left _ _)) ((le_max_left _ _).trans hK)
  have hfull := ContinuousFlexibility.Radial.tailNaturalLineAndGreenKernel hT
    (hη.trans (min_le_right _ _)) ((le_max_right _ _).trans hK) hI G hgraph
  exact ⟨hI, hIₙ, G, hnorm, hgraph, hinverse, htrunc, hfull.1, hfull.2⟩

end ContinuousFlexibility.Blueprint
