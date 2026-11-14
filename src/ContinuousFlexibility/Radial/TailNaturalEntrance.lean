module

public import ContinuousFlexibility.Radial.TailNaturalInterpolation
public import ContinuousFlexibility.Radial.TailNaturalNodeBounds
public import ContinuousFlexibility.Radial.TailRegularIntervalState

/-!
# The natural solution does not satisfy the entrance Dirichlet condition

At the first mass entrance the outgoing natural flux is positive on the
mass scale. If a separate initial gap is present, this exceeds its free
impedance, so the actual solution has a negative entrance value.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem tailNaturalFirstFlux_lower {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) {a : ℕ → ℝ}
    (ha₀ : a 0 = 1) (ha₁ : |a 1| ≤ 1) :
    T.Λ * tailMass T 0 / 2 ≤ tailPoissonInterpolationFlux T hT a (T.node 0) := by
  let A := T.Λ * tailMass T 0
  have hA : 0 < A := mul_pos hT.2.2.1 (tailMass_pos hT 0)
  have hc : tailActualNodeCoupling T hT 0 ≤ A / 8 :=
    tailNode_coupling_le_eighth_mass (tailResistance_pos hT 0) hK
      (hT.2.2.2.2.2.2.2.2.2.2 0).2.2.2.1 (tailActualNodeCoupling_upper hT hη 0)
  have hca : -(A / 8) ≤ tailActualNodeCoupling T hT 0 * a 1 := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp ha₁).1
      (tailActualNodeCoupling_pos hT 0).le
    nlinarith only [h, hc]
  have hr : (tailActualEdgeLength T 0)⁻¹ ≤ A / 8 :=
    (deepTail_inverse_edge_left hT 0).trans
      (div_le_div_of_nonneg_left hA.le (by norm_num) (by linarith only [hK]))
  have hp := (tailActualEdgePairing_left_scaled_bounds hT hη hK 0).1
  have hvalue : tailPoissonInterpolationFlux T hT a (T.node 0) =
      -tailActualEdgeDiagonal T hT 0 (tailActualEdgePoisson T hT 0) false +
        tailActualNodeCoupling T hT 0 * a 1 := by
    unfold tailPoissonInterpolationFlux
    rw [morseOutwardGlue_apply_block (deepTail_node_strictMono hT)
      (show T.node 0 ∈ Ico (T.node 0) (T.node (0 + 1)) from
        ⟨le_rfl, tailActualEdge_order hT 0⟩),
      (tailActualEdgeInterpolationFlux_endpoints hT 0 (a 0) (a 1)).1, ha₀, mul_one]
  rw [hvalue, tailActualEdgeDiagonal_eq_pairing]
  change A / 2 ≤ -((tailActualEdgeLength T 0)⁻¹ -
    T.Λ * tailActualEdgePairing T hT 0 false 0 (tailActualEdgeLength T 0)) +
      tailActualNodeCoupling T hT 0 * a 1
  linarith only [hp, hr, hca]

theorem tailActualState_entrance_ne_zero {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hK : 32 ≤ T.K) {u v : ℝ → ℝ}
    (h : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (hu₀ : u (T.node 0) = 1)
    (hv₀ : T.Λ * tailMass T 0 / 2 ≤ v (T.node 0)) :
    u T.entrance ≠ 0 := by
  rcases hT.2.2.2.1 with heq | hg
  · rw [← heq, hu₀]
    exact one_ne_zero
  · have hsub := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
    have hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
    have hp₀ := fun x hx => deepTail_pos hT x (hsub hx)
    have hR : 0 < tailInitialResistance T := deepTail_interval_resistance_pos hT
      le_rfl hg.1 (deepTail_node_lt_endpoint hT 0)
    have hA : 0 < T.Λ * tailMass T 0 := mul_pos hT.2.2.1 (tailMass_pos hT 0)
    have hKpos : 0 < T.K := lt_trans (by norm_num) hT.2.2.2.2.2.2.1
    have hi : 1 / tailInitialResistance T ≤ T.Λ * tailMass T 0 / T.K := by
      apply (div_le_div_iff₀ hR hKpos).mpr
      simpa only [one_mul] using hg.2.2.2
    have hstrict : 1 / tailInitialResistance T < v (T.node 0) := by
      have hsmall : T.Λ * tailMass T 0 / T.K ≤ T.Λ * tailMass T 0 / 8 :=
        div_le_div_of_nonneg_left hA.le (by norm_num) (by linarith only [hK])
      linarith only [hi, hsmall, hv₀, hA]
    obtain ⟨U, V, hUV, hUb, hVb, hnegative⟩ := exists_tailRegularInterval_state
      hg.1 hp hp₀ hT.2.2.1.le (hg.2.1.trans_lt hT.2.2.2.2.2.1) 1 (v (T.node 0))
    have heq := tailFirstOrderSystem_eqOn_Icc
      (show T.node 0 ∈ Icc T.entrance (T.node 0) from ⟨hg.1.le, le_rfl⟩)
      hp (fun x hx => (hp₀ x hx).ne') (h.mono hsub) hUV
      (hu₀.trans hUb.symm) hVb.symm T.entrance ⟨le_rfl, hg.1.le⟩
    rw [heq.1]
    exact (hnegative zero_le_one hstrict).ne

end ContinuousFlexibility.Radial
