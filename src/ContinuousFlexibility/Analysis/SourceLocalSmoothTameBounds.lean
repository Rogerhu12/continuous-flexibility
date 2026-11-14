module

public import ContinuousFlexibility.Analysis.SourceSmoothTameBounds
public import ContinuousFlexibility.Analysis.MaterialDivergenceNormBounds

/-!
# Local physical-norm estimates give the original source tame grading

Monotonicity of the actual weighted jet norm controls every lower
projective level at the same output order. The low order, loss, and
neighborhood from the local one-high estimate are therefore preserved.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

private theorem smoothTameOn_of_local_majorant
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {U : Set E} {f : E → F}
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (N : ℕ → F → ℝ) (hN : ∀ s y, q s y ≤ N s y)
    (J : SmoothDirections U f)
    (hbound : ∀ k x₀, x₀ ∈ U → ∃ loss base : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
        p base (x - x₀) < δ → ∀ v : Fin k → E,
        N s (J.D k x v) ≤ C * oneHighVariationWeight p base (s + loss) x v) :
    SmoothTameOn p q U f := by
  refine ⟨J, fun k x₀ hx₀ => ?_⟩
  obtain ⟨loss, base, δ, hδ, hb⟩ := hbound k x₀ hx₀
  refine ⟨loss, base, δ, hδ, fun s hs => ?_⟩
  obtain ⟨C, hC, hnorm⟩ := hb s hs
  exact ⟨C, hC, fun x hx hnear v => (hN s (J.D k x v)).trans (hnorm x hx hnear v)⟩

theorem sourceGrading_le_physicalNorm
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (u : S.Source) (s : ℕ) :
    S.sourceGrading s u ≤ physicalNorm T (3 / 4 : ℝ) s (physicalSourceDecode S u) := by
  have hu : HeightMember D T (3 / 4 : ℝ) (physicalSourceDecode S u) :=
    (hS.1 (3 / 4 : ℝ)).2.2.2.1 u.val
  apply (sourceGrading_le_iff_physicalNorm hS s u (Real.sqrt_nonneg _)).mpr
  intro i hi
  exact physicalNorm_monotone_of_memLp hu.2.2.2.2 hi

theorem smoothTameOn_source_of_local_oneHigh_norm_bounds
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {U : Set E} {f : E → S.Source}
    (hS : IsPhysicalSpaces D T S) (p : ℕ → Seminorm ℝ E)
    (J : SmoothDirections U f)
    (hbound : ∀ k x₀, x₀ ∈ U → ∃ loss base : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
        p base (x - x₀) < δ → ∀ v : Fin k → E,
        physicalNorm T (3 / 4 : ℝ) s (physicalSourceDecode S (J.D k x v)) ≤
          C * oneHighVariationWeight p base (s + loss) x v) :
    SmoothTameOn p S.sourceGrading U f :=
  smoothTameOn_of_local_majorant p S.sourceGrading
    (fun s u => physicalNorm T (3 / 4 : ℝ) s (physicalSourceDecode S u))
    (fun s u => sourceGrading_le_physicalNorm hS u s) J hbound

end ContinuousFlexibility.Statements
