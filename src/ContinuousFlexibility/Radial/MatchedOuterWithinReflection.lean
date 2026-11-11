import ContinuousFlexibility.Radial.MatchedOuterSideGlue
import ContinuousFlexibility.Radial.OuterOutwardHilbert
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Exact outward within derivatives at the two matching cuts

Reflection transports the one-sided derivative without an ambient
differentiability assumption.  The sign is exactly the frozen outward
flux sign, for the original side representatives.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology Pointwise
open ContinuousFlexibility.Statements

/-- This identity remains valid for arbitrary functions, because both
the domain and the point are transported by the same linear equivalence. -/
theorem matchedOuter_derivWithin_reflection
    (D : ReferenceData) (right : Bool) (entry : ℝ) (u : ℝ → ℝ) :
    derivWithin (fun x => u (outerOutwardRadius right x))
        (Ico (outerOutwardRadius right entry)
          (outerOutwardRadius right (tailPhysicalEndpoint D right)))
        (outerOutwardRadius right entry) =
      outerTailSign right *
        derivWithin u (if right then Ico entry D.b else Ioc D.a entry) entry := by
  cases right
  · have hs : -(Ico (-entry) (-D.a)) = Ioc D.a entry := by
      ext x
      simp only [Set.mem_neg, mem_Ico, mem_Ioc, neg_le_neg_iff, neg_lt_neg_iff]
      exact and_comm
    change derivWithin (fun x => u (-x)) (Ico (-entry) (-D.a)) (-entry) =
      (-1) * derivWithin u (Ioc D.a entry) entry
    rw [derivWithin_comp_neg, hs, neg_neg]
    ring
  · change derivWithin u (Ico entry D.b) entry =
      1 * derivWithin u (Ico entry D.b) entry
    exact (one_mul _).symm

/-- Left frozen flux is the actual outward derivative of the left
representative, normalized by the unchanged boundary scale. -/
theorem matchedOuterSideGlue_flux_left {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    (uL uR : ℝ → ℝ) :
    matchingOuterFlux D M (matchedOuterSideGlue M.innerLeft M.innerRight uL uR) 0 =
      D.w M.innerLeft *
        derivWithin (fun x => uL (outerOutwardRadius false x))
          (Ico (outerOutwardRadius false M.innerLeft)
            (outerOutwardRadius false (tailPhysicalEndpoint D false)))
          (outerOutwardRadius false M.innerLeft) /
        Real.sqrt (M.boundaryScale 0) := by
  rw [matchedOuter_derivWithin_reflection]
  change (-1) * D.w M.innerLeft *
      derivWithin (matchedOuterSideGlue M.innerLeft M.innerRight uL uR)
        (closure (matchingOuterRegion D M)) M.innerLeft /
        Real.sqrt (M.boundaryScale 0) =
    D.w M.innerLeft * ((-1) * derivWithin uL (Ioc D.a M.innerLeft) M.innerLeft) /
      Real.sqrt (M.boundaryScale 0)
  rw [matchedOuterSideGlue_matching_derivWithin_left ha hm hb]
  ring

/-- Right frozen flux uses the same outward derivative convention. -/
theorem matchedOuterSideGlue_flux_right {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    (uL uR : ℝ → ℝ) :
    matchingOuterFlux D M (matchedOuterSideGlue M.innerLeft M.innerRight uL uR) 1 =
      D.w M.innerRight *
        derivWithin (fun x => uR (outerOutwardRadius true x))
          (Ico (outerOutwardRadius true M.innerRight)
            (outerOutwardRadius true (tailPhysicalEndpoint D true)))
          (outerOutwardRadius true M.innerRight) /
        Real.sqrt (M.boundaryScale 1) := by
  rw [matchedOuter_derivWithin_reflection]
  change 1 * D.w M.innerRight *
      derivWithin (matchedOuterSideGlue M.innerLeft M.innerRight uL uR)
        (closure (matchingOuterRegion D M)) M.innerRight /
        Real.sqrt (M.boundaryScale 1) =
    D.w M.innerRight * (1 * derivWithin uR (Ico M.innerRight D.b) M.innerRight) /
      Real.sqrt (M.boundaryScale 1)
  rw [matchedOuterSideGlue_matching_derivWithin_right ha hm hb]
  ring

end ContinuousFlexibility.Radial
