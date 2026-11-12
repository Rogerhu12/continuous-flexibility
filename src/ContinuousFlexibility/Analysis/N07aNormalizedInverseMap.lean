import ContinuousFlexibility.Analysis.N07aNormalizedInverseCore

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

section ScalarInverse

variable (C : NonlinearGeometryData S)
  (U : Set (StateDirections S × ℝ)) (G : ScalarInverseData S)
  (hrow : ∀ z ∈ U, ∀ f : S.Source,
    referenceRow D (heightPairField S (G.G (liftSectorParameter S C z) f).1) = 0)

/-- Restrict the given physical inverse to the row-zero subspace on its
parameter domain.  Its unused values outside that domain are zero. -/
def n07aNormalizedInverse :
    (StateDirections S × ℝ) → S.Source →ₗ[ℝ] N07aNormalizedUnknown hD hT hS := by
  classical
  exact fun z => if hz : z ∈ U then
    (G.G (liftSectorParameter S C z)).toLinearMap.codRestrict
      (n07aNormalizationSubmodule hD hT hS)
      (fun f => (n07aNormalizationSubmodule_mem_iff hD hT hS _).mpr (hrow z hz f))
    else 0

theorem n07aNormalizedInverse_apply_coe (z : StateDirections S × ℝ) (hz : z ∈ U)
    (f : S.Source) :
    ((n07aNormalizedInverse hD hT hS C U G hrow z f :
      N07aNormalizedUnknown hD hT hS) : HeightPair S × ℝ) =
      G.G (liftSectorParameter S C z) f := by
  classical
  unfold n07aNormalizedInverse
  rw [dite_eq_left hz]
  rfl

end ScalarInverse

end ContinuousFlexibility.Analysis
