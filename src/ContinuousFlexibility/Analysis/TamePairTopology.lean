module

public import ContinuousFlexibility.Analysis.TameLocalCalculus

/-!
# The topology of the sum grading on a product

The two coordinate families generate the product topology. The diagonal
sum grading generates the same topology: a coordinate seminorm is bounded
by the sum at its own index, and that sum is bounded by twice the maximum
of its two coordinate seminorms. No monotonicity assumption is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set TopologicalSpace
open ContinuousFlexibility.Statements

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- The diagonal sum of two generating seminorm families generates the
ordinary product topology, with no monotonicity hypotheses. -/
theorem withSeminorms_pairGrading {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : WithSeminorms p) (hq : WithSeminorms q) :
    WithSeminorms (pairGrading p q) := by
  classical
  let r : Bool → ℕ → Seminorm ℝ (E × F)
    | true => fun n => (p n).comp (LinearMap.fst ℝ E F)
    | false => fun n => (q n).comp (LinearMap.snd ℝ E F)
  let t : Bool → TopologicalSpace (E × F)
    | true => induced (Prod.fst : E × F → E) inferInstance
    | false => induced (Prod.snd : E × F → F) inferInstance
  have hr (b : Bool) : WithSeminorms (topology := t b) (r b) := by
    cases b
    · exact (LinearMap.snd ℝ E F).withSeminorms_induced hq
    · exact (LinearMap.fst ℝ E F).withSeminorms_induced hp
  have hσ : WithSeminorms (SeminormFamily.sigma r) := by
    have hi : WithSeminorms (topology := ⨅ b : Bool, t b)
        (SeminormFamily.sigma r) :=
      withSeminorms_iInf (𝕜 := ℝ) (E := E × F) (ι := Bool)
        (κ := fun _ => ℕ) (p := r) (t := t) hr
    have htop : (⨅ b : Bool, t b) = (inferInstance : TopologicalSpace (E × F)) := by
      rw [iInf_bool_eq, instTopologicalSpaceProd]
    rw [htop] at hi
    exact hi
  have hr₁ (n : ℕ) (x : E × F) :
      SeminormFamily.sigma r ⟨true, n⟩ x = p n x.1 :=
    Seminorm.comp_apply (p n) (LinearMap.fst ℝ E F) x
  have hr₂ (n : ℕ) (x : E × F) :
      SeminormFamily.sigma r ⟨false, n⟩ x = q n x.2 :=
    Seminorm.comp_apply (q n) (LinearMap.snd ℝ E F) x
  apply hσ.congr
  · apply Seminorm.IsBounded.of_real
    intro n
    let s : Finset (Σ _ : Bool, ℕ) := {⟨true, n⟩, ⟨false, n⟩}
    refine ⟨s, 2, fun x => ?_⟩
    have h₁ : p n x.1 ≤ (s.sup (SeminormFamily.sigma r)) x := by
      rw [← hr₁ n x]
      exact Seminorm.le_finset_sup_apply (by simp [s])
    have h₂ : q n x.2 ≤ (s.sup (SeminormFamily.sigma r)) x := by
      rw [← hr₂ n x]
      exact Seminorm.le_finset_sup_apply (by simp [s])
    rw [LinearMap.id_apply, pairGrading_apply]
    linarith
  · apply Seminorm.IsBounded.of_real
    rintro ⟨b, n⟩
    refine ⟨{n}, 1, fun x => ?_⟩
    rw [LinearMap.id_apply, Finset.sup_singleton, one_mul, pairGrading_apply]
    cases b
    · rw [hr₂]
      exact le_add_of_nonneg_left (apply_nonneg (p n) x.1)
    · rw [hr₁]
      exact le_add_of_nonneg_right (apply_nonneg (q n) x.2)

end ContinuousFlexibility.Analysis
