import ContinuousFlexibility.Analysis.N08SectorControlColumn
import ContinuousFlexibility.Analysis.N08ControlResponseBounds

/-!
# All-order control responses through the existing scalar inverse

The same actual smoothing column is used on sector states and extended by
zero elsewhere. Its low source norm is uniformly bounded on a single
stronger neighborhood, so the existing inverse-family estimate has only
one high state factor. The bound includes the source, the full height pair,
and the scalar compatibility response at every output order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {G : ScalarInverseData S}
  {base loss : ℕ} {ε : ℝ}

/-- The control column is chosen together with one stronger state
neighborhood, its actual derivative, its sector smoothness, and the three
component bounds required by N08. The scalar inverse is unchanged. -/
theorem n08ControlInverseResponse_exists
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hG : ScalarInverseProperties D S C L G base ε) :
    ∃ newBase newLoss : ℕ, ∃ η : ℝ,
      base ≤ newBase ∧ loss ≤ newLoss ∧ 0 < η ∧ η ≤ ε ∧
      ∃ H : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source,
        (∀ z, ¬ stateSector S z.1 → H z = 0) ∧
        (∀ z ∈ stateNeighborhood S C newBase η, stateSector S z.1 →
          ∀ u : CircleSpace S,
          HasProjectiveLineDerivAt
            (fun x => n08ActualScalarResidual hT hS hN (x, z.2))
            (H z (n08ControlRestriction S u)) z.1 (0, (0, (u, 0)))) ∧
        (∀ s : ℕ, ∃ K : ℝ, 0 < K ∧
          ∀ z ∈ stateNeighborhood S C newBase η, ∀ b : ControlBanach,
          S.sourceGrading s (H z b) +
            heightPairGrading S s (G.G z (H z b)).1 + |(G.G z (H z b)).2| ≤
              K * (1 + stateGrading S (s + newLoss) (z.1 - C.referenceState) + |z.2|) * ‖b‖) ∧
        SmoothTameOn
          (pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading)
          S.sourceGrading (sectorNeighborhood S newBase η η ×ˢ univ)
          (fun z : (StateDirections S × ℝ) × ControlBanach =>
            H (liftSectorParameter S C z.1) z.2) := by
  classical
  obtain ⟨columnBase, columnLoss, δ, hδ, Hraw, hderiv, hsmooth, hcolumn⟩ :=
    n08ActualControlColumn_exists hT hS hN
  let H := n08SectorControlColumn S Hraw
  let commonBase := max base columnBase
  let ρ : ℝ := min ε (δ / 2)
  let V : Set (StateDirections S × ℝ) := sectorNeighborhood S commonBase ρ ρ
  have hρ : 0 < ρ := lt_min hN.2.1 (half_pos hδ)
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρδ : 2 * ρ ≤ δ := by
    have h := min_le_right ε (δ / 2)
    dsimp only [ρ]
    linarith
  have hmap : MapsTo (liftSectorParameter S C) V
      {z | n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ} :=
    n08_sectorNeighborhood_maps_controlBall (le_max_right _ _) hρδ
  have hV : V ⊆ sectorNeighborhood S base ε ε :=
    n08_sectorNeighborhood_mono (le_max_left _ _) hρε hρε
  have hGv : LinearFamilyTame (pairGrading (sectorGrading S) realGrading)
      (pairGrading (heightPairGrading S) realGrading) S.sourceGrading V
      (fun z => (G.G (liftSectorParameter S C z)).toLinearMap) :=
    n08_linearFamilyTame_restrict hG.2.2.1 hV
  have hHv : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ V, ∀ b : ControlBanach,
      S.sourceGrading s (H (liftSectorParameter S C z) b) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + columnLoss) z) * ‖b‖ := by
    intro s
    obtain ⟨K, hK, hKb⟩ := hcolumn s
    refine ⟨K, hK, fun z hz b => ?_⟩
    have h := hKb (liftSectorParameter S C z) (hmap hz) b
    change S.sourceGrading s (n08SectorControlColumn S Hraw (liftSectorParameter S C z) b) ≤ _
    rw [n08SectorControlColumn_lift hN.2.2.1]
    simpa only [n08StateParameterGrading, n08_liftSectorParameter_difference] using h
  have hmono := tamePairGrading_monotone (solve_sectorGrading_monotone S)
    weighted_realGrading_monotone
  have houtput : Monotone (pairGrading (heightPairGrading S) realGrading) :=
    tamePairGrading_monotone
      (tamePairGrading_monotone (gradedSeminorm_monotone _ _) weighted_realGrading_monotone)
      weighted_realGrading_monotone
  obtain ⟨responseBase, responseLoss, hresponse⟩ :=
    n08_controlResponse_bound hmono houtput hGv hHv
  let newBase := max commonBase responseBase
  let newLoss := max loss responseLoss
  let η : ℝ := min ρ (1 / 2)
  have hη : 0 < η := lt_min hρ (by norm_num)
  have hηρ : η ≤ ρ := min_le_left _ _
  have hηε : η ≤ ε := hηρ.trans hρε
  have hηδ : 2 * η ≤ δ := (mul_le_mul_of_nonneg_left hηρ (by norm_num)).trans hρδ
  have hηone : 2 * η ≤ 1 := by
    have h := min_le_right ρ (1 / 2 : ℝ)
    dsimp only [η]
    linarith
  have hnewV : sectorNeighborhood S newBase η η ⊆ V :=
    n08_sectorNeighborhood_mono (le_max_left _ _) hηρ hηρ
  have hnewMap : MapsTo (liftSectorParameter S C) (sectorNeighborhood S newBase η η)
      {z | n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ} :=
    fun _ hz => hmap (hnewV hz)
  refine ⟨newBase, newLoss, η, (le_max_left base columnBase).trans (le_max_left _ _),
    le_max_left _ _, hη, hηε, H,
    (fun z hz => n08SectorControlColumn_of_not_sector Hraw hz), ?_, ?_, ?_⟩
  · intro z hz hs u
    have hball : n08StateParameterGrading S columnBase
        (z - (C.referenceState, 0)) < δ :=
      (n08_stateNeighborhood_pairGrading_lt
        ((le_max_right base columnBase).trans (le_max_left _ _)) hz).trans_le hηδ
    have heq : H z = Hraw z := n08SectorControlColumn_of_sector Hraw hs
    rw [heq]
    exact hderiv z hball u
  · intro s
    obtain ⟨K, hK, hKb⟩ := hresponse s
    refine ⟨K, hK, fun z hz b => ?_⟩
    by_cases hs : stateSector S z.1
    · let y := n08SectorParameterCenter hN.2.2.1 z hs
      have hy : y ∈ sectorNeighborhood S newBase η η :=
        n08SectorParameterCenter_mem hN.2.2.1 hs hz
      have hsmall : pairGrading (sectorGrading S) realGrading responseBase y < 1 :=
        (n08_sectorNeighborhood_pairGrading_lt (le_max_right _ _) hy).trans_le hηone
      have hb := hKb y (hnewV hy) hsmall b
      have hb' : S.sourceGrading s (H z b) +
          pairGrading (heightPairGrading S) realGrading s (G.G z (H z b)) ≤
          K * (1 + n08StateParameterGrading S (s + responseLoss)
            (z - (C.referenceState, 0))) * ‖b‖ := by
        simpa only [y, n08SectorParameterCenter_lift, n08SectorParameterCenter_grading] using hb
      have hhigh := n08StateParameterGrading_monotone S
        (Nat.add_le_add_left (le_max_right loss responseLoss) s) (z - (C.referenceState, 0))
      have hfinal := hb'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hhigh) hK.le) (norm_nonneg b))
      change S.sourceGrading s (H z b) +
          (heightPairGrading S s (G.G z (H z b)).1 + |(G.G z (H z b)).2|) ≤
          K * (1 + (stateGrading S (s + newLoss) (z.1 - C.referenceState) + |z.2 - 0|)) * ‖b‖
        at hfinal
      simpa only [sub_zero, add_assoc] using hfinal
    · have heq : H z = 0 := n08SectorControlColumn_of_not_sector Hraw hs
      simp only [heq, zero_apply, map_zero, Prod.fst_zero, Prod.snd_zero, abs_zero, add_zero]
      exact mul_nonneg (mul_nonneg hK.le
        (add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _))) (norm_nonneg _)
  · exact n08SectorControlColumn_smoothTame hN.2.2.1 hsmooth hnewMap

end ContinuousFlexibility.Statements
