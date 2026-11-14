import ContinuousFlexibility.Analysis.SmoothDirectionsGluing
import ContinuousFlexibility.Analysis.RadialGermGlue

/-!
# Joint towers across a fixed radial glue

A radial interval of agreement is chosen before the state. The two
overlapping open pieces cover the original state product with the whole
physical plane. Uniqueness glues the genuine towers of the literal
piecewise field, with no restriction of the state neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {U : Set E}

def n04Realization_radialGlue_jointDirections
    (hU : IsOpen U) (c : ℝ) (f g : E → PolarPoint → ℝ)
    (Jf : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => f p.1 p.2))
    (Jg : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => g p.1 p.2))
    {ε : ℝ} (hε : 0 < ε)
    (hmatch : ∀ x ∈ U, ∀ r ∈ Metric.ball c ε, ∀ θ, f x (r, θ) = g x (r, θ)) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => radialGermGlue c (f p.1) (g p.1) p.2) := by
  let V : Bool → Set (E × PolarPoint) := fun side =>
    U ×ˢ {p : PolarPoint | if side then c - ε < p.1 else p.1 < c + ε}
  have hV (side : Bool) : IsOpen (V side) := by
    cases side
    · exact hU.prod (isOpen_lt continuous_fst continuous_const)
    · exact hU.prod (isOpen_lt continuous_const continuous_fst)
  have hsub (side : Bool) : V side ⊆ U ×ˢ (univ : Set PolarPoint) :=
    fun _ hp => ⟨hp.1, mem_univ _⟩
  have hcover : ∀ p ∈ U ×ˢ (univ : Set PolarPoint), ∃ side, p ∈ V side := by
    intro p hp
    by_cases hlt : p.2.1 < c + ε
    · exact ⟨false, hp.1, hlt⟩
    · refine ⟨true, hp.1, ?_⟩
      change c - ε < p.2.1
      linarith
  let J : ∀ side, SmoothDirections (V side)
      (fun p : E × PolarPoint => radialGermGlue c (f p.1) (g p.1) p.2) := by
    intro side
    cases side with
    | false =>
        apply (Jf.restrict (hV false) (hsub false)).congrOn
        intro p hp
        by_cases hlt : p.2.1 < c
        · simp only [radialGermGlue, if_pos hlt]
        · have hb : p.2.1 ∈ Metric.ball c ε := by
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            have hu : p.2.1 < c + ε := hp.2
            constructor <;> linarith
          simp only [radialGermGlue, if_neg hlt]
          exact hmatch p.1 hp.1 p.2.1 hb p.2.2
    | true =>
        apply (Jg.restrict (hV true) (hsub true)).congrOn
        intro p hp
        by_cases hlt : p.2.1 < c
        · have hb : p.2.1 ∈ Metric.ball c ε := by
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            have hl : c - ε < p.2.1 := hp.2
            constructor <;> linarith
          simp only [radialGermGlue, if_pos hlt]
          exact (hmatch p.1 hp.1 p.2.1 hb p.2.2).symm
        · simp only [radialGermGlue, if_neg hlt]
  exact (exists_smoothDirections_of_open_cover (hU.prod isOpen_univ) V J hsub hcover).choose

end ContinuousFlexibility.Analysis
