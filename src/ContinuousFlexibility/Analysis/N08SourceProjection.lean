import ContinuousFlexibility.Analysis.N08StateProjection
import ContinuousFlexibility.Analysis.N08ScalarConservation
import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Analysis.SolveTameSubspace
import ContinuousFlexibility.Scalar.WeightedSmoothTameLinear
import ContinuousFlexibility.Scalar.WeightedStateTopology

/-!
# The actual global projection to compatible scalar sources

The physical-space data already provide the continuous tame rank-one
projection `f ↦ f - Q(f) ψ`. Restricting its codomain to the actual kernel
gives a global source-valued map. Its derivative towers need no domain or
sector cutoff. Conservation identifies its values with the encoded scalar
residual wherever the actual equation is realized.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

private theorem sourceProjection_data (hS : IsPhysicalSpaces D T S) :
    ∃ P : (S.height (3 / 4 : ℝ)).Space →L[ℝ] (S.height (3 / 4 : ℝ)).Space,
      (∀ f, P f = f - S.Q f • S.psi) ∧ (∀ f, S.Q (P f) = 0) ∧
      (∀ f, S.Q f = 0 → P f = f) ∧
      (∃ loss base, IsTameLinear (S.height (3 / 4 : ℝ)).grading
        (S.height (3 / 4 : ℝ)).grading P.toLinearMap loss base) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hP, _⟩ := hS
  exact hP

private theorem sourceProjection_mem (hS : IsPhysicalSpaces D T S)
    (f : (S.height (3 / 4 : ℝ)).Space) :
    (sourceProjection_data hS).choose f ∈ S.Q.toLinearMap.ker :=
  (LinearMap.mem_ker).2 ((sourceProjection_data hS).choose_spec.2.1 f)

def n08SourceProjection (hS : IsPhysicalSpaces D T S) :
    (S.height (3 / 4 : ℝ)).Space →L[ℝ] S.Source :=
  (sourceProjection_data hS).choose.codRestrict S.Q.toLinearMap.ker (sourceProjection_mem hS)

private theorem sourceProjection_coe_ambient (hS : IsPhysicalSpaces D T S)
    (f : (S.height (3 / 4 : ℝ)).Space) :
    (n08SourceProjection hS f).val = (sourceProjection_data hS).choose f :=
  ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

theorem n08SourceProjection_coe (hS : IsPhysicalSpaces D T S)
    (f : (S.height (3 / 4 : ℝ)).Space) :
    (n08SourceProjection hS f).val = f - S.Q f • S.psi :=
  (sourceProjection_coe_ambient hS f).trans ((sourceProjection_data hS).choose_spec.1 f)

theorem n08SourceProjection_identity_of_compatible (hS : IsPhysicalSpaces D T S)
    {f : (S.height (3 / 4 : ℝ)).Space} (hf : S.Q f = 0) :
    (n08SourceProjection hS f).val = f :=
  (sourceProjection_coe_ambient hS f).trans ((sourceProjection_data hS).choose_spec.2.2.1 f hf)

theorem n08SourceProjection_retract (hS : IsPhysicalSpaces D T S) (f : S.Source) :
    n08SourceProjection hS f.val = f :=
  Subtype.ext (n08SourceProjection_identity_of_compatible hS ((LinearMap.mem_ker).1 f.property))

theorem n08SourceProjection_isTame (hS : IsPhysicalSpaces D T S) :
    ∃ loss base, IsTameLinear (S.height (3 / 4 : ℝ)).grading S.sourceGrading
      (n08SourceProjection hS).toLinearMap loss base :=
  n08_codRestrict_existsTame
    (p := (S.height (3 / 4 : ℝ)).grading) (q := (S.height (3 / 4 : ℝ)).grading)
    S.Q.toLinearMap.ker (sourceProjection_data hS).choose (sourceProjection_mem hS)
    (sourceProjection_data hS).choose_spec.2.2.2

theorem n08SourceProjection_smoothTame (hS : IsPhysicalSpaces D T S) :
    SmoothTameOn (S.height (3 / 4 : ℝ)).grading S.sourceGrading univ
      (n08SourceProjection hS) := by
  obtain ⟨loss, base, ht⟩ := n08SourceProjection_isTame hS
  exact smoothTameOn_continuousLinear (n08SourceProjection hS) ht

section Postcomposition

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {U : Set X} {f : X → (S.height (3 / 4 : ℝ)).Space}

/-- Postcomposition supplies the actual source-valued tower on precisely
the original open domain, even when realization holds only on its sector. -/
def n08SourceProjection_smoothDirections (hS : IsPhysicalSpaces D T S)
    (J : SmoothDirections U f) :
    SmoothDirections U (fun x => n08SourceProjection hS (f x)) :=
  solveSmoothDirectionsPostcomp J (n08SourceProjection hS)

theorem n08SourceProjection_postcompose_smoothTame (hS : IsPhysicalSpaces D T S)
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p) (ht : WithSeminorms p)
    (hf : SmoothTameOn p (S.height (3 / 4 : ℝ)).grading U f) :
    SmoothTameOn p S.sourceGrading U (fun x => n08SourceProjection hS (f x)) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  letI : ∀ n, CompleteSpace ((S.height (3 / 4 : ℝ)).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 (3 / 4 : ℝ)) n
  obtain ⟨loss, base, hP⟩ := (sourceProjection_data hS).choose_spec.2.2.2
  have hcomp := smoothTameOn_postcompose_generic hp ht
    (withSeminorms_graded (fun n => (S.height (3 / 4 : ℝ)).level n)
      (S.height (3 / 4 : ℝ)).bond) hf (sourceProjection_data hS).choose hP
  exact solve_smoothTameOn_codRestrict S.Q.toLinearMap.ker S.Q.isClosed_ker hcomp
    (fun x => n08SourceProjection hS (f x))
    (fun x _ => sourceProjection_coe_ambient hS (f x))

end Postcomposition

/-- The projected residual has the genuine field on the prescribed
sector because its unprojected field satisfies the actual conservation law. -/
theorem n08SourceProjection_decode_scalarResidual
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (f : (S.height (3 / 4 : ℝ)).Space)
    (hf : ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode f p = scalarResidualField D S C z p)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    (S.height (3 / 4 : ℝ)).decode (n08SourceProjection hS f).val p =
      scalarResidualField D S C z p := by
  rw [n08SourceProjection_identity_of_compatible hS
    (n08_compatible_of_decode_scalarResidual hT hS hN hz hs f hf)]
  exact hf p hp

end ContinuousFlexibility.Statements
