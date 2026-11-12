import ContinuousFlexibility.Analysis.N08CircleDiagonalContinuity
import ContinuousFlexibility.Analysis.TameJetLocalBounds

/-!
# One actual neighborhood for every control diagonal entry

The physical state grading generates its product topology. Therefore an
arbitrary neighborhood of the reference parameter contains a centered
state neighborhood, with a prescribed minimum order and maximum radius.
Finite-entry continuity and a uniform tail estimate can then be retained
on the same neighborhood of the same actual diagonal.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

/-- The standard state neighborhoods form a neighborhood basis at the
reference parameter. Their order may be increased and their radius capped. -/
theorem n08_stateNeighborhood_subset_nhds
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    {W : Set (AnnularState S × ℝ)} (hW : W ∈ 𝓝 (C.referenceState, (0 : ℝ)))
    (required : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℕ, ∃ η : ℝ, required ≤ b ∧ 0 < η ∧ η ≤ δ ∧
      stateNeighborhood S C b η ⊆ W := by
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨b, r, hr, hb⟩ := exists_seminormBall_subset_nhds
    (solve_stateGrading_monotone S) (solve_stateGrading_withSeminorms S) hU
  obtain ⟨t, ht, htV⟩ := Metric.mem_nhds_iff.mp hV
  let η : ℝ := min r (min t δ)
  have hη : 0 < η := lt_min hr (lt_min ht hδ)
  have hηr : η ≤ r := min_le_left _ _
  have hηt : η ≤ t := (min_le_right _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨max b required, η, le_max_right _ _, hη, hηδ, ?_⟩
  intro z hz
  apply hUV
  constructor
  · exact hb z.1 (((solve_stateGrading_monotone S (le_max_left b required)
      (z.1 - C.referenceState)).trans_lt hz.1).trans_le hηr)
  · apply htV
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hz.2.trans_le hηt

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

/-- A quarter-size tail error and the already proved finite-entry
continuity give the final half-to-two bounds on one stronger neighborhood.
The diagonal is the actual first control jet throughout this statement. -/
theorem n08CircleDiagonal_uniform_of_tail
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    (htail : ∃ b : ℕ, ∃ δ : ℝ, ∃ I : Finset ℕ,
      base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C b δ, stateSector S z.1 →
        ∀ m, m ∉ I → |n08CircleDiagonal hS hR z m - 1| ≤ (1 / 4 : ℝ)) :
    ∃ b : ℕ, ∃ δ : ℝ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C b δ, stateSector S z.1 →
        ∀ m, (1 / 2 : ℝ) ≤ |n08CircleDiagonal hS hR z m| ∧
          |n08CircleDiagonal hS hR z m| ≤ 2 := by
  obtain ⟨tailBase, tailRadius, I, htailBase, htailRadius, htailOld, htailBound⟩ := htail
  have hfinite := n08CircleDiagonal_finite_near_reference hT hS hN hR I
  obtain ⟨b, δ, hb, hδ, hδtail, hfiniteBound⟩ :=
    n08_stateNeighborhood_subset_nhds S C hfinite tailBase htailRadius
  refine ⟨b, δ, htailBase.trans hb, hδ, hδtail.trans htailOld, ?_⟩
  intro z hz hs m
  by_cases hm : m ∈ I
  · exact hfiniteBound hz m hm
  · have h := abs_le.mp
      (htailBound z (n08_stateNeighborhood_mono hb hδtail hz) hs m hm)
    have hpos : 0 ≤ n08CircleDiagonal hS hR z m := by linarith only [h.1]
    rw [abs_of_nonneg hpos]
    constructor <;> linarith only [h.1, h.2]

end ContinuousFlexibility.Statements
