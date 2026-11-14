module

public import ContinuousFlexibility.Radial.DeepTailPhysicalPoisson

/-!
# The optional initial resistance edge

The first edge may precede the first mass entrance. Its own hypothesis
controls the same actual Green contraction as on all subsequent edges.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem deepTail_initial_small {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hinitial : T.entrance < T.node 0) :
    T.Λ * tailInitialGapMass T * tailInitialResistance T ≤ T.η ∧
      tailInitialGapMass T ≤ T.η * tailMass T 0 ∧
      T.K ≤ T.Λ * tailMass T 0 * tailInitialResistance T := by
  rcases hT.2.2.2.1 with heq | hgap
  · exact False.elim (hinitial.ne heq.symm)
  · exact hgap.2

theorem tailInitialResistance_pos {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hinitial : T.entrance < T.node 0) : 0 < tailInitialResistance T :=
  deepTail_interval_resistance_pos hT le_rfl hinitial (deepTail_node_lt_endpoint hT 0)

theorem deepTail_initial_inverse_resistance {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hinitial : T.entrance < T.node 0) :
    (tailInitialResistance T)⁻¹ ≤ T.Λ * tailMass T 0 / T.K :=
  tail_inverse_resistance_bound (lt_trans zero_lt_one hT.2.2.2.2.2.2.1)
    (tailInitialResistance_pos hT hinitial) (deepTail_initial_small hT hinitial).2.2

theorem deepTail_initialEdge_diagonal_small {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hinitial : T.entrance < T.node 0) :
    let hsub := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
    let hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
    let hpos := fun x hx => deepTail_pos hT x (hsub hx)
    tailEdgeDiagonalSize
      ((tailResistanceChart_strictMono (tailClampedDensity_continuous hinitial.le hp)
        (tailClampedDensity_pos hinitial.le hpos) T.entrance) hinitial)
      (tailClampedEdgePotential hinitial.le hp hpos T.Λ) ≤ T.η := by
  dsimp only
  have hsub := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
  have hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
  have hpos := fun x hx => deepTail_pos hT x (hsub hx)
  have h := tailClampedEdge_diagonal_le (c := T.entrance) hinitial
    ⟨le_rfl, hinitial.le⟩ hp hpos hT.2.2.1.le
  simp only [intervalIntegral.integral_same, zero_mul, zero_add] at h
  apply h.trans
  change T.Λ * (tailInitialResistance T * tailInitialGapMass T) ≤ T.η
  calc
    _ = T.Λ * tailInitialGapMass T * tailInitialResistance T := by ring
    _ ≤ _ := (deepTail_initial_small hT hinitial).1

/-- Actual initial-edge Poisson data, with no extra hypothesis beyond the
initial-edge alternative in `DeepTailHypotheses`. -/
theorem exists_deepTail_initialPoissonData {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hinitial : T.entrance < T.node 0) :
    Nonempty (TailPhysicalPoissonData T.p T.entrance (T.node 0) T.Λ T.η hinitial.le) := by
  have hsub := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
  exact exists_tailPhysicalPoissonData hinitial
    ((deepTail_contDiffOn hT).continuousOn.mono hsub)
    (fun x hx => deepTail_pos hT x (hsub hx)) hT.2.2.1.le hT.2.2.2.2.2.1
    (deepTail_initialEdge_diagonal_small hT hinitial)

end ContinuousFlexibility.Radial
