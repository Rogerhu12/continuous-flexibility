import ContinuousFlexibility.Analysis.CircleJetAssembly
import ContinuousFlexibility.Analysis.N01NeighborhoodRestriction

/-!
# Sharp physical circle norms imply the frozen smooth tame bounds

The target grading is a finite maximum of physical circle norms. Taking
a finite sum of the numerical constants preserves the previously fixed
loss and low input order. The genuine tower is unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {T : MaterialData} {γ : ℝ} {S : CircleModelData} {U : Set E} {f : E → S.Space}

theorem circle_grading_oneHigh_bound
    (hS : IsCircleModel T γ S) (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (J : SmoothDirections U f) (k loss base : ℕ)
    (hbound : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Fin k → E,
      circleNorm T γ s (S.decode (J.D k x v)) ≤
        C * oneHighVariationWeight p base (s + loss) x v) :
    ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Fin k → E,
      S.grading s (J.D k x v) ≤ C * oneHighVariationWeight p base (s + loss) x v := by
  classical
  choose K hK hb using hbound
  intro s
  let C : ℝ := ∑ i ∈ Finset.range (s + 1), K i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i hi => hK i)
  refine ⟨C, hC, ?_⟩
  intro x hx v
  have hW (i : ℕ) : 0 ≤ oneHighVariationWeight p base (i + loss) x v := by
    unfold oneHighVariationWeight
    positivity
  apply (circleGrading_le_iff_circleNorm hS s (J.D k x v) (mul_nonneg hC (hW s))).mpr
  intro i hi
  have hKi : K i ≤ C :=
    Finset.single_le_sum (fun j hj => hK j) (Finset.mem_range.mpr (by omega))
  exact (hb i x hx v).trans (mul_le_mul hKi
    (oneHighVariationWeight_mono hp le_rfl (Nat.add_le_add_right hi loss) x v)
    (hW i) hC)

/-- No loss depending on the output order is introduced when passing
from the physical norms to the actual projective grading. -/
theorem smoothTameOn_circle_of_oneHigh_norm_bounds
    (hS : IsCircleModel T γ S) (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (J : SmoothDirections U f)
    (hbound : ∀ k, ∃ loss base : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ U, ∀ v : Fin k → E,
        circleNorm T γ s (S.decode (J.D k x v)) ≤
          C * oneHighVariationWeight p base (s + loss) x v) :
    SmoothTameOn p S.grading U f := by
  refine ⟨J, ?_⟩
  intro k x₀ hx₀
  obtain ⟨loss, base, hb⟩ := hbound k
  refine ⟨loss, base, 1, zero_lt_one, ?_⟩
  intro s hs
  obtain ⟨C, hC, hCs⟩ := circle_grading_oneHigh_bound hS p hp J k loss base hb s
  refine ⟨C, hC, ?_⟩
  intro x hx hnear v
  exact hCs x hx v

end ContinuousFlexibility.Statements
