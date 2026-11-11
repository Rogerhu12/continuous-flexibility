import ContinuousFlexibility.Analysis.SourceJetAssembly
import ContinuousFlexibility.Analysis.N01NeighborhoodRestriction

/-!
# Fixed-loss source bounds in the original projective grading

Finite maxima of physical Sobolev norms preserve the fixed input loss
and base order of a genuine directional tower.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {U : Set E} {f : E → S.Source}

theorem source_grading_oneHigh_bound
    (hS : IsPhysicalSpaces D T S) (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (J : SmoothDirections U f) (k loss base : ℕ)
    (hbound : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Fin k → E,
      physicalNorm T (3 / 4 : ℝ) s (physicalSourceDecode S (J.D k x v)) ≤
        C * oneHighVariationWeight p base (s + loss) x v) :
    ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Fin k → E,
      S.sourceGrading s (J.D k x v) ≤ C * oneHighVariationWeight p base (s + loss) x v := by
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
  apply (sourceGrading_le_iff_physicalNorm hS s (J.D k x v) (mul_nonneg hC (hW s))).mpr
  intro i hi
  have hKi : K i ≤ C :=
    Finset.single_le_sum (fun j hj => hK j) (Finset.mem_range.mpr (by omega))
  exact (hb i x hx v).trans (mul_le_mul hKi
    (oneHighVariationWeight_mono hp le_rfl (Nat.add_le_add_right hi loss) x v)
    (hW i) hC)

theorem smoothTameOn_source_of_oneHigh_norm_bounds
    (hS : IsPhysicalSpaces D T S) (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (J : SmoothDirections U f)
    (hbound : ∀ k, ∃ loss base : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ U, ∀ v : Fin k → E,
        physicalNorm T (3 / 4 : ℝ) s (physicalSourceDecode S (J.D k x v)) ≤
          C * oneHighVariationWeight p base (s + loss) x v) :
    SmoothTameOn p S.sourceGrading U f := by
  refine ⟨J, ?_⟩
  intro k x₀ hx₀
  obtain ⟨loss, base, hb⟩ := hbound k
  refine ⟨loss, base, 1, zero_lt_one, ?_⟩
  intro s hs
  obtain ⟨C, hC, hCs⟩ := source_grading_oneHigh_bound hS p hp J k loss base hb s
  refine ⟨C, hC, ?_⟩
  intro x hx hnear v
  exact hCs x hx v

end ContinuousFlexibility.Statements
