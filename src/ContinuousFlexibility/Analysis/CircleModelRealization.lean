import ContinuousFlexibility.Statements.Analysis
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Realizing circle operators in the supplied physical model

The decoder in `IsCircleModel` identifies the existing projective limit
with the actual smooth weighted circle fields. These lemmas lift scalar
linear operators through that decoder and convert physical norm estimates
into a fixed-loss estimate for the existing grading. The grading is the
finite maximum of all coordinate norms through the stated order.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped NNReal

theorem circleDecode_mem_range_iff
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (f : ℕ → ℝ → ℝ) :
    f ∈ LinearMap.range S.decode ↔ CircleMember T γ f := by
  obtain ⟨_, _, _, hmember, hrealize, _⟩ := hS
  constructor
  · rintro ⟨u, rfl⟩
    exact hmember u
  · exact hrealize f

theorem circleGrading_le_iff_circleNorm
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (n : ℕ) (u : S.Space) {c : ℝ} (hc : 0 ≤ c) :
    S.grading n u ≤ c ↔ ∀ i ≤ n, circleNorm T γ i (S.decode u) ≤ c := by
  obtain ⟨_, _, _, _, _, _, _, hnorm⟩ := hS
  simpa only [CircleModelData.grading, hnorm] using
    gradedSeminorm_le_iff (fun i => S.level i) S.bond n u hc

section LinearLift

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

/-- The unique lift of an actual linear family of weighted circle fields. -/
def liftCircleLinear (hS : IsCircleModel T γ S)
    (F : E →ₗ[ℝ] (ℕ → ℝ → ℝ))
    (hF : ∀ x, CircleMember T γ (F x)) : E →ₗ[ℝ] S.Space :=
  LinearMap.codRestrictOfInjective F S.decode hS.2.2.2.2.2.1
    (fun x => (circleDecode_mem_range_iff hS (F x)).mpr (hF x))

theorem liftCircleLinear_decode (hS : IsCircleModel T γ S)
    (F : E →ₗ[ℝ] (ℕ → ℝ → ℝ))
    (hF : ∀ x, CircleMember T γ (F x)) (x : E) :
    S.decode (liftCircleLinear hS F hF x) = F x := by
  exact LinearMap.codRestrictOfInjective_comp_apply F S.decode hS.2.2.2.2.2.1
    (fun y => (circleDecode_mem_range_iff hS (F y)).mpr (hF y)) x

theorem liftCircleLinear_unique (hS : IsCircleModel T γ S)
    (F : E →ₗ[ℝ] (ℕ → ℝ → ℝ))
    (hF : ∀ x, CircleMember T γ (F x))
    (L : E →ₗ[ℝ] S.Space) (hL : ∀ x, S.decode (L x) = F x) :
    L = liftCircleLinear hS F hF := by
  apply LinearMap.ext
  intro x
  apply hS.2.2.2.2.2.1
  rw [hL, liftCircleLinear_decode]

theorem liftCircleLinear_grading_le_iff (hS : IsCircleModel T γ S)
    (F : E →ₗ[ℝ] (ℕ → ℝ → ℝ))
    (hF : ∀ x, CircleMember T γ (F x))
    (n : ℕ) (x : E) {c : ℝ} (hc : 0 ≤ c) :
    S.grading n (liftCircleLinear hS F hF x) ≤ c ↔
      ∀ i ≤ n, circleNorm T γ i (F x) ≤ c := by
  rw [circleGrading_le_iff_circleNorm hS n _ hc, liftCircleLinear_decode]

/-- Physical estimates with one fixed loss imply the corresponding tame
estimate. The finite maximum of the numerical constants controls the
finite maximum defining the target grading. -/
theorem liftCircleLinear_isTame (hS : IsCircleModel T γ S)
    (F : E →ₗ[ℝ] (ℕ → ℝ → ℝ))
    (hF : ∀ x, CircleMember T γ (F x))
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (loss : ℕ)
    (hbound : ∀ n, ∃ C : ℝ≥0, ∀ x,
      circleNorm T γ n (F x) ≤ (C : ℝ) * p (n + loss) x) :
    IsTameLinear p S.grading (liftCircleLinear hS F hF) loss 0 := by
  classical
  choose C hC using hbound
  intro n _
  refine ⟨(Finset.Iic n).sup C, ?_⟩
  intro x
  apply (liftCircleLinear_grading_le_iff hS F hF n x
    (mul_nonneg (NNReal.coe_nonneg _) (apply_nonneg _ _))).mpr
  intro i hi
  have hCi : (C i : ℝ) ≤ ((Finset.Iic n).sup C : ℝ≥0) := by
    exact_mod_cast (Finset.le_sup (f := C) (Finset.mem_Iic.mpr hi))
  calc
    circleNorm T γ i (F x) ≤ (C i : ℝ) * p (i + loss) x := hC i x
    _ ≤ ((Finset.Iic n).sup C : ℝ≥0) * p (n + loss) x :=
      mul_le_mul hCi (hp (Nat.add_le_add_right hi loss) x)
        (apply_nonneg _ _) (NNReal.coe_nonneg _)

theorem liftCircleLinear_continuous [TopologicalSpace E]
    (hS : IsCircleModel T γ S)
    (F : E →ₗ[ℝ] (ℕ → ℝ → ℝ))
    (hF : ∀ x, CircleMember T γ (F x))
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (htop : WithSeminorms p)
    (loss : ℕ)
    (hbound : ∀ n, ∃ C : ℝ≥0, ∀ x,
      circleNorm T γ n (F x) ≤ (C : ℝ) * p (n + loss) x) :
    Continuous (liftCircleLinear hS F hF) := by
  exact (liftCircleLinear_isTame hS F hF p hp loss hbound).continuous htop
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond)

end LinearLift

end ContinuousFlexibility.Statements
