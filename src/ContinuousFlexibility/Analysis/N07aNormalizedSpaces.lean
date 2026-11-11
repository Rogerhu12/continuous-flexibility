import ContinuousFlexibility.Analysis.SolveNormalization
import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Scalar.WeightedStateTopology

/-!
# The actual normalized height space and its grading

The physical inverse takes values in the kernel of the true normalization
row.  This module constructs that closed subspace with the induced
physical grading and the actual subspace topology.  Its inclusion in the
full `HeightPair` and scalar output preserves every seminorm estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- The physical output grading, including the free left constant and the
scalar coefficient of the distinguished source column. -/
def n07aOutputGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ (HeightPair S × ℝ) :=
  pairGrading (heightPairGrading S) realGrading

theorem n07aOutputGrading_monotone (S : PhysicalSpacesData) :
    Monotone (n07aOutputGrading S) :=
  tamePairGrading_monotone
    (tamePairGrading_monotone (gradedSeminorm_monotone _ _)
      weighted_realGrading_monotone) weighted_realGrading_monotone

theorem n07aOutputGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms (n07aOutputGrading S) :=
  withSeminorms_pairGrading
    (withSeminorms_pairGrading (withSeminorms_graded _ _)
      weighted_realGrading_withSeminorms) weighted_realGrading_withSeminorms

theorem n07aSourceGrading_monotone (S : PhysicalSpacesData) :
    Monotone S.sourceGrading :=
  fun _ _ h f => gradedSeminorm_monotone _ _ h f.val

theorem n07aSourceGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms S.sourceGrading :=
  (Topology.IsInducing.subtypeVal).withSeminorms
    (f := S.Q.toLinearMap.ker.subtype) (withSeminorms_graded _ _)

theorem n07a_sectorNeighborhood_isOpen (S : PhysicalSpacesData)
    (base : ℕ) (ε q0 : ℝ) : IsOpen (sectorNeighborhood S base ε q0) :=
  (isOpen_lt
    (((solve_sectorGrading_withSeminorms S).continuous_seminorm base).comp continuous_fst)
    continuous_const).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

variable (hD : IsRadialReference D) (hT : IsMaterialData D T)
  (hS : IsPhysicalSpaces D T S)

/-- The actual integral row ignores the distinguished-source coefficient. -/
def n07aNormalizationRow : (HeightPair S × ℝ) →L[ℝ] ℝ :=
  (heightReferenceRowCLM hD hT hS).comp
    (ContinuousLinearMap.fst ℝ (HeightPair S) ℝ)

theorem n07aNormalizationRow_apply (u : HeightPair S × ℝ) :
    n07aNormalizationRow hD hT hS u =
      referenceRow D (heightPairField S u.1) := by
  simp only [n07aNormalizationRow, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', heightReferenceRowCLM_apply]

/-- The genuine normalized unknowns of the physical scalar equation. -/
def n07aNormalizationSubmodule : Submodule ℝ (HeightPair S × ℝ) :=
  (n07aNormalizationRow hD hT hS).toLinearMap.ker

abbrev N07aNormalizedUnknown : Type := n07aNormalizationSubmodule hD hT hS

theorem n07aNormalizationSubmodule_mem_iff (u : HeightPair S × ℝ) :
    u ∈ n07aNormalizationSubmodule hD hT hS ↔
      referenceRow D (heightPairField S u.1) = 0 := by
  simp only [n07aNormalizationSubmodule, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, n07aNormalizationRow_apply]

theorem n07aNormalizationSubmodule_isClosed :
    IsClosed (n07aNormalizationSubmodule hD hT hS : Set (HeightPair S × ℝ)) :=
  (n07aNormalizationRow hD hT hS).isClosed_ker

theorem n07aNormalizedUnknown_row (u : N07aNormalizedUnknown hD hT hS) :
    referenceRow D (heightPairField S u.val.1) = 0 :=
  (n07aNormalizationSubmodule_mem_iff hD hT hS u.val).mp u.property

/-- Restriction of the prescribed output grading to the normalized space. -/
def n07aNormalizedGrading :
    ℕ → Seminorm ℝ (N07aNormalizedUnknown hD hT hS) :=
  fun n => (n07aOutputGrading S n).comp (n07aNormalizationSubmodule hD hT hS).subtype

theorem n07aNormalizedGrading_apply (n : ℕ) (u : N07aNormalizedUnknown hD hT hS) :
    n07aNormalizedGrading hD hT hS n u = n07aOutputGrading S n u.val := by
  simp only [n07aNormalizedGrading, Seminorm.comp_apply, Submodule.subtype_apply]

theorem n07aNormalizedGrading_monotone :
    Monotone (n07aNormalizedGrading hD hT hS) := by
  intro m n h u
  simpa only [n07aNormalizedGrading_apply] using n07aOutputGrading_monotone S h u.val

theorem n07aNormalizedGrading_withSeminorms :
    WithSeminorms (n07aNormalizedGrading hD hT hS) :=
  (Topology.IsInducing.subtypeVal).withSeminorms
    (f := (n07aNormalizationSubmodule hD hT hS).subtype)
    (n07aOutputGrading_withSeminorms S)

/-- The inclusion loses neither derivatives nor material weights. -/
theorem n07aNormalizedSubtype_isTame :
    IsTameLinear (n07aNormalizedGrading hD hT hS) (n07aOutputGrading S)
      (n07aNormalizationSubmodule hD hT hS).subtype 0 0 := by
  intro n _
  refine ⟨1, fun u => ?_⟩
  simp only [Nat.add_zero, NNReal.coe_one, one_mul, Submodule.subtype_apply,
    n07aNormalizedGrading_apply, le_refl]
end ContinuousFlexibility.Analysis
