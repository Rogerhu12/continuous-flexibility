import ContinuousFlexibility.Analysis.CoupledControlLift
import ContinuousFlexibility.Analysis.SolveTameSubspace

/-!
# The closed space of angular-constant controls

The control inverse is first solved in its Banach space and then recovered
in this closed subspace of the original circle model.  Its grading is the
inherited circle grading, so no second representation of higher control
orders is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

variable {T : MaterialData} {γ : ℝ} {M : CircleModelData}

/-- The kernel of identity minus the actual angular-mean projection. -/
def coupledConstantCircleSubmodule (hM : IsCircleModel T γ M) : Submodule ℝ M.Space :=
  ((ContinuousLinearMap.id ℝ M.Space) - circleAngularMeanProjection hM).ker

abbrev CoupledConstantCircle (hM : IsCircleModel T γ M) := coupledConstantCircleSubmodule hM

def coupledConstantCircleGrading (hM : IsCircleModel T γ M) :
    ℕ → Seminorm ℝ (CoupledConstantCircle hM) :=
  fun n => (M.grading n).comp (coupledConstantCircleSubmodule hM).subtype

theorem coupledConstantCircle_mem_iff (hM : IsCircleModel T γ M) (u : M.Space) :
    u ∈ coupledConstantCircleSubmodule hM ↔ circleAngularMeanProjection hM u = u := by
  change u - circleAngularMeanProjection hM u = 0 ↔ _
  rw [sub_eq_zero, eq_comm]

theorem coupledConstantCircle_isClosed (hM : IsCircleModel T γ M) :
    IsClosed (coupledConstantCircleSubmodule hM : Set M.Space) :=
  ((ContinuousLinearMap.id ℝ M.Space) - circleAngularMeanProjection hM).isClosed_ker

theorem coupledConstantCircle_constant (hM : IsCircleModel T γ M)
    (u : CoupledConstantCircle hM) (m : ℕ) (θ φ : ℝ) :
    M.decode u.val m θ = M.decode u.val m φ := by
  have hu := (coupledConstantCircle_mem_iff hM u.val).mp u.property
  rw [← hu]
  exact circleAngularMeanProjection_constant hM u.val m θ φ

theorem coupledConstantCircle_mem_of_constant (hM : IsCircleModel T γ M)
    (u : M.Space) (hu : ∀ m θ φ, M.decode u m θ = M.decode u m φ) :
    u ∈ coupledConstantCircleSubmodule hM :=
  (coupledConstantCircle_mem_iff hM u).mpr (circleAngularMeanProjection_eq_self hM u hu)

/-- The original mean projection with its actual constant-circle codomain. -/
def coupledConstantCircleProjection (hM : IsCircleModel T γ M) :
    M.Space →L[ℝ] CoupledConstantCircle hM :=
  (circleAngularMeanProjection hM).codRestrict (coupledConstantCircleSubmodule hM)
    (fun u => (coupledConstantCircle_mem_iff hM _).mpr
      (circleAngularMeanProjection_idempotent hM u))

theorem coupledConstantCircleProjection_val (hM : IsCircleModel T γ M) (u : M.Space) :
    (coupledConstantCircleProjection hM u).val = circleAngularMeanProjection hM u := rfl

theorem coupledConstantCircleProjection_coe (hM : IsCircleModel T γ M)
    (u : CoupledConstantCircle hM) : coupledConstantCircleProjection hM u.val = u := by
  apply Subtype.ext
  exact (coupledConstantCircle_mem_iff hM u.val).mp u.property

theorem coupledConstantCircleGrading_monotone (hM : IsCircleModel T γ M) :
    Monotone (coupledConstantCircleGrading hM) :=
  fun _ _ h u => gradedSeminorm_monotone _ _ h u.val

theorem coupledConstantCircleGrading_withSeminorms (hM : IsCircleModel T γ M) :
    WithSeminorms (coupledConstantCircleGrading hM) :=
  (Topology.IsInducing.subtypeVal).withSeminorms
    (f := (coupledConstantCircleSubmodule hM).subtype) (withSeminorms_graded _ _)

theorem coupledConstantCircleProjection_isTame (hM : IsCircleModel T γ M) :
    IsTameLinear M.grading (coupledConstantCircleGrading hM)
      (coupledConstantCircleProjection hM).toLinearMap 0 0 := by
  intro n _
  refine ⟨1, fun u => ?_⟩
  simpa only [Nat.add_zero, NNReal.coe_one, one_mul, coupledConstantCircleGrading,
    Seminorm.comp_apply, Submodule.subtype_apply, coupledConstantCircleProjection_val] using
    circleAngularMeanLinear_grading_le hM n u

theorem coupledConstantCircleSubtype_isTame (hM : IsCircleModel T γ M) :
    IsTameLinear (coupledConstantCircleGrading hM) M.grading
      (coupledConstantCircleSubmodule hM).subtype 0 0 := by
  intro n _
  exact ⟨1, fun u => by simp only [Nat.add_zero, NNReal.coe_one, one_mul,
    coupledConstantCircleGrading, Seminorm.comp_apply]⟩

/-- The reciprocal-diagonal recovery viewed in the closed constant space. -/
def coupledConstantCircleInverse (hM : IsCircleModel T γ M)
    (a : ℕ → ℝ) (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) :
    M.Space →L[ℝ] CoupledConstantCircle hM :=
  (coupledInverseControlLift hM a ha).codRestrict (coupledConstantCircleSubmodule hM)
    (fun u => coupledConstantCircle_mem_of_constant hM _
      (coupledInverseControlLift_constant hM a ha u))

theorem coupledConstantCircleInverse_val (hM : IsCircleModel T γ M)
    (a : ℕ → ℝ) (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) (u : M.Space) :
    (coupledConstantCircleInverse hM a ha u).val = coupledInverseControlLift hM a ha u := rfl

theorem coupledConstantCircleInverse_isTame (hM : IsCircleModel T γ M)
    (a : ℕ → ℝ) (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) :
    IsTameLinear M.grading (coupledConstantCircleGrading hM)
      (coupledConstantCircleInverse hM a ha).toLinearMap 0 0 := by
  intro n _
  refine ⟨2, fun u => ?_⟩
  simpa only [Nat.add_zero, NNReal.coe_ofNat, coupledConstantCircleGrading,
    Seminorm.comp_apply, Submodule.subtype_apply, coupledConstantCircleInverse_val] using
    coupledInverseControlLift_grading_le hM a ha n u

end ContinuousFlexibility.Statements
