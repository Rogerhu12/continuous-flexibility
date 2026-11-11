import ContinuousFlexibility.Analysis.N01FlowLocalizedDirections
import ContinuousFlexibility.Analysis.N01EndpointParameterTower
import ContinuousFlexibility.Analysis.SmoothDirectionsEuler
import ContinuousFlexibility.Analysis.HeightScalarVariationWeights

/-!
# Every pure scalar flow jet has a local physical height factor

The true scaling identity supplies the Euler relation throughout the
scalar segment. A mixed N01 jet and the scalar mean value theorem then
bound every positive pure scalar order, including at scalar parameter
zero. The precise one-high-factor height expression is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

private theorem scalar_segment_mul_mem {t q : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t * q ∈ uIcc (0 : ℝ) q := by
  rcases le_total (0 : ℝ) q with hq | hq
  · rw [uIcc_of_le hq]
    exact ⟨mul_nonneg ht.1 hq,
      (mul_le_mul_of_nonneg_right ht.2 hq).trans_eq (one_mul q)⟩
  · rw [uIcc_of_ge hq]
    refine ⟨?_, mul_nonpos_of_nonneg_of_nonpos ht.1 hq⟩
    simpa only [one_mul] using mul_le_mul_of_nonpos_right ht.2 hq

theorem N01Properties.sectorFlow_pure_scalar_height_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m b θ r, b ≤ s → r ∈ Icc (C.left m) (C.right m) →
      ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun y => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C y)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ η : HeightPair S,
        (∀ t ∈ Ioo (C.left m) (C.right m), ∀ ψ,
          heightPairField S η (t, ψ) = stateU S (liftSectorParameter S C z).1 (t, ψ)) →
        |J.D (n + 1) z (fun _ => scalarParameterDirection S)| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + loss) z) *
              heightPairGrading S base η + heightPairGrading S (s + loss) η) := by
  obtain ⟨B, hB, hclosed⟩ := hN.sectorFlow_closed_tower hS hT (n + 2) s
  refine ⟨B, hB, fun m b θ r hb hr => ?_⟩
  obtain ⟨J, hJ⟩ := hclosed m b θ r hb hr
  refine ⟨J, fun z hz η hη => ?_⟩
  let x₀ : StateDirections S × ℝ := (z.1, 0)
  let P : ℝ := B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
    T.E0 (T.sample (C.cell m)) ^ B
  have hsample := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 (C.cell m)
  have hH : 0 < T.H (T.sample (C.cell m)) := (hT.2.1 _ hsample).2.1
  have hE : 0 < T.E0 (T.sample (C.cell m)) := (hT.2.1 _ hsample).2.2.1
  have hP : 0 ≤ P := mul_nonneg
    (mul_nonneg hB.le (Real.rpow_nonneg hH.le _)) (Real.rpow_nonneg hE.le _)
  have hEuler (q : ℝ) (hq : x₀ + q • scalarParameterDirection S ∈
      sectorNeighborhood S base ε ε) :
      J.D 1 (x₀ + q • scalarParameterDirection S) (fun _ => heightParameterDirection S η) =
        q * J.D 1 (x₀ + q • scalarParameterDirection S) (fun _ => scalarParameterDirection S) := by
    dsimp only [x₀] at hq ⊢
    rw [scalarParameter_zero_line] at hq ⊢
    have hηq : ∀ t ∈ Ioo (C.left m) (C.right m), ∀ ψ,
        heightPairField S η (t, ψ) =
          heightPairField S (liftSectorParameter S C (z.1, q)).1.1 (t, ψ) := by
      intro t ht ψ
      exact hη t ht ψ
    exact (hN.ordinaryFlowFamily_first_height_jet_locality hS hT hq η
      (liftSectorParameter S C (z.1, q)).1.1 m b θ hr hηq J).trans
        (hN.ordinaryFlowFamily_height_scalar_jet hS hT hq m b θ hr J)
  have hline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      x₀ + (t * z.2) • scalarParameterDirection S ∈ sectorNeighborhood S base ε ε := by
    dsimp only [x₀]
    rw [scalarParameter_zero_line]
    exact sectorParameter_scalar_segment_mem hz (scalar_segment_mul_mem ht)
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |J.D (n + 2) (x₀ + (t * z.2) • scalarParameterDirection S)
        (Fin.snoc (fun _ : Fin (n + 1) => scalarParameterDirection S)
          (heightParameterDirection S η))| ≤
        P * (((n : ℝ) + 2 +
          pairGrading (sectorGrading S) realGrading (s + loss) z) *
            heightPairGrading S base η + heightPairGrading S (s + loss) η) := by
    have h := hJ _ (hline t ht)
      (Fin.snoc (fun _ : Fin (n + 1) => scalarParameterDirection S)
        (heightParameterDirection S η))
    rw [oneHighVariationWeight_scalar_height] at h
    have hgrade := sectorPairGrading_scalar_segment_le S (s + loss) z.1
      (scalar_segment_mul_mem (q := z.2) ht)
    have hbase : 0 ≤ heightPairGrading S base η := apply_nonneg _ _
    have hadd : ((n + 1 : ℕ) : ℝ) + 1 +
        pairGrading (sectorGrading S) realGrading (s + loss)
          (x₀ + (t * z.2) • scalarParameterDirection S) ≤
        (n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + loss) z := by
      dsimp only [x₀]
      rw [scalarParameter_zero_line]
      simp only [Nat.cast_add, Nat.cast_one]
      linarith only [hgrade]
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_right hadd hbase)
        (heightPairGrading S (s + loss) η)) hP)
  have h := J.abs_pure_scalar_jet_le_of_mixed_euler_bound x₀
    (scalarParameterDirection S) (heightParameterDirection S η) hEuler n z.2 _ hline hbound
  simpa only [x₀, scalarParameter_zero_line, P] using h

end ContinuousFlexibility.Statements
