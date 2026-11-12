import ContinuousFlexibility.Analysis.N07aParameterGrading
import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Analysis.TameInverseTheorem

/-!
# Smooth tame inversion on the actual normalized height space

The final wrapper uses an actual `ScalarInverseData`. Its analytic inputs
remain explicit: the forward family, both inverse identities, joint
continuity, and a fixed-loss linear-family estimate. This module supplies
the smooth-tame bridge, not those analytic estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)

/-- A normalized continuous tame inverse of the actual forward family is
smooth tame, with values returned in the full frozen output space. -/
theorem n07a_normalizedInverse_smoothTame
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    (F : (StateDirections S × ℝ) → N07aNormalizedUnknown hD hT hS →L[ℝ] S.Source)
    (V : (StateDirections S × ℝ) → S.Source →ₗ[ℝ] N07aNormalizedUnknown hD hT hS)
    (hF : SmoothTameOn
      (n07aParameterNormalizedGrading hD hT hS) S.sourceGrading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS => F z.1 z.2))
    (hleft : ∀ z ∈ U, ∀ u, V z (F z u) = u)
    (hright : ∀ z ∈ U, ∀ f, F z (V z f) = f)
    (hV : ContinuousOn
      (fun z : (StateDirections S × ℝ) × S.Source => V z.1 z.2) (U ×ˢ univ))
    (hVTame : LinearFamilyTame (n07aParameterGrading S)
      (n07aNormalizedGrading hD hT hS) S.sourceGrading U V) :
    SmoothTameOn
      (n07aParameterSourceGrading S)
      (n07aOutputGrading S) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × S.Source =>
        ((V z.1 z.2 : N07aNormalizedUnknown hD hT hS) : HeightPair S × ℝ)) := by
  have hnormalized : SmoothTameOn
      (n07aParameterSourceGrading S)
      (n07aNormalizedGrading hD hT hS) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × S.Source => V z.1 z.2) :=
    smoothTameOn_inverseFamily
    (p := n07aParameterGrading S)
    (q := n07aNormalizedGrading hD hT hS) (r := S.sourceGrading)
    (tamePairGrading_monotone (solve_sectorGrading_monotone S)
      weighted_realGrading_monotone)
    (n07aNormalizedGrading_monotone hD hT hS) (n07aSourceGrading_monotone S)
    (withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S)
      weighted_realGrading_withSeminorms)
    (n07aNormalizedGrading_withSeminorms hD hT hS) (n07aSourceGrading_withSeminorms S)
    hU F V hF hleft hright hV hVTame
  exact solve_smoothTameOn_postcomp hnormalized
    (n07aNormalizationSubmodule hD hT hS).subtypeL (B := 1) zero_le_one
    (fun n u => by
      simp only [Submodule.subtypeL_apply, n07aNormalizedGrading_apply, one_mul,
        n07aOutputGrading, le_refl])

end ContinuousFlexibility.Analysis
