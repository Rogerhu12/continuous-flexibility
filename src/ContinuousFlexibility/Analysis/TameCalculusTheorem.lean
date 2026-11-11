import ContinuousFlexibility.Analysis.TameComposition
import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# The complete tame-calculus target

This assembles the six frozen calculus clauses on the actual projective
limits, together with smoothing on the exponential sequence model.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

/-- All clauses of the project's fixed tame-calculus statement. -/
theorem h01Statement : H01Statement := by
  refine ⟨?_, ?_⟩
  · intro B _ _ _
    exact hasSmoothing_exponentialSequence B
  · intro E F G _ _ _ _ _ _ _ _ _ e f g
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro L hL
      obtain ⟨loss, base, hL⟩ := hL
      exact smoothTameOn_continuousLinear L hL
    · intro U V hU hV u v hmap hu hv
      exact smoothTameOn_comp hU hV hmap hu hv
    · intro U u v hu hv
      exact smoothTameOn_add (gradedSeminorm_monotone E e) hu hv
    · exact hasInterpolation_of_hasSmoothing (gradedSeminorm_monotone E e)
    · exact hasSmoothing_of_tameRetraction (gradedSeminorm_monotone E e)
    · intro B hB
      obtain ⟨loss, base, hB⟩ := hB
      exact smoothTameOn_bilinear
        (withSeminorms_graded E e) (withSeminorms_graded F f) (withSeminorms_graded G g)
        (gradedSeminorm_monotone G g) B hB

end ContinuousFlexibility.Analysis
