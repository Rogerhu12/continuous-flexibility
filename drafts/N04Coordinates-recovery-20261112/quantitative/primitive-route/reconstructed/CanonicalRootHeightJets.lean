import ContinuousFlexibility.Analysis.CanonicalRootRelativeJets

/-!
# Jets of the actual relative root height

Both factors come from the same stored root charts. The current height
is evaluated at the genuine relative transport, whose image stays on
that same root circle. One product-composition estimate covers the
height ratio and its reciprocal without an additional inverse estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def CanonicalRootHeightJetFamily
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (side : Bool) (B : ℕ → ℝ) : Prop :=
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let r := n01ComponentRoot C m side
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ θ : ℝ,
    ContDiffAt ℝ ∞ (n04CoordinatesCurrentHeightRatio C K z i) (r, θ) ∧
      0 < n04CoordinatesCurrentHeightRatio C K z i (r, θ) ∧
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
        loss B (z - (C.referenceState, 0))
        (n04CoordinatesCurrentHeightRatio C K z i) (r, θ) ∧
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
        loss B (z - (C.referenceState, 0))
        (fun y => (n04CoordinatesCurrentHeightRatio C K z i y)⁻¹) (r, θ)

/-- The common neighborhood and loss precede the component. The actual
stored height and transport are unchanged throughout the construction. -/
theorem n04b_exists_common_root_heightJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ outLoss ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∀ side : Bool, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        CanonicalRootHeightJetFamily S C K newBase outLoss ε' m side B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨rootBase, rootLoss, ηR, hbR, _hRlow, hηR, hηRε, hroots⟩ :=
    n04b_exists_common_root_endpoint_fields hS hT hN hfield hA hB
  obtain ⟨relativeBase, relativeLoss, ηT, hbT, _hTlow, hηT, hηTε, hrelative⟩ :=
    n04b_exists_common_root_relative_positiveJets hS hT hN hfield hA hB
  let inputLoss := max rootLoss relativeLoss
  obtain ⟨low, outLoss, hproduct⟩ :=
    relativeHeightProduct_allJets_fixed_loss hp hI inputLoss
  let newBase := max rootBase (max relativeBase (max low outLoss))
  let ε' := min (min ηR ηT) (1 / 2 : ℝ)
  have hε' : 0 < ε' := lt_min (lt_min hηR hηT) (by norm_num)
  have hbaseR : rootBase ≤ newBase := le_max_left _ _
  have hbaseT : relativeBase ≤ newBase := (le_max_left _ _).trans (le_max_right _ _)
  have hbaseLow : low ≤ newBase :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbaseOut : outLoss ≤ newBase :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hε'R : ε' ≤ ηR := (min_le_left _ _).trans (min_le_left _ _)
  have hε'T : ε' ≤ ηT := (min_le_left _ _).trans (min_le_right _ _)
  have hb' : base ≤ newBase := hbR.trans hbaseR
  have hε'ε : ε' ≤ ε := hε'R.trans hηRε
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hrefR : (C.referenceState, 0) ∈ stateNeighborhood S C rootBase ηR :=
    reference_mem_stateNeighborhood S C rootBase hηR
  have hsref : stateSector S C.referenceState := hN.1.1.2.2.1.stateSector
  refine ⟨newBase, outLoss, ε', hb', hbaseOut, hε', hε'ε, ?_⟩
  intro m side
  let r := n01ComponentRoot C m side
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  obtain ⟨κJ, A, _hκJ, hApos, hroot⟩ := hroots m side
  obtain ⟨R, hRpos, hrel⟩ := hrelative m side
  let Q : ℕ → ℝ := fun n => A n + R n
  have hQ (n : ℕ) : 0 < Q n := add_pos (hApos n) (hRpos n)
  have hAQ (n : ℕ) : A n ≤ Q n := le_add_of_nonneg_right (hRpos n).le
  have hRQ (n : ℕ) : R n ≤ Q n := le_add_of_nonneg_left (hApos n).le
  obtain ⟨B, hBpos, hbnd⟩ := hproduct Q hQ
  refine ⟨B, hBpos, ?_⟩
  dsimp only [CanonicalRootHeightJetFamily]
  intro z hz hs θ
  let τ : PolarPoint → PolarPoint := canonicalCurrentPoint C K z i
  have hzold : z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C hb' hε'ε hz
  have hzR : z ∈ stateNeighborhood S C rootBase ηR :=
    stateNeighborhood_mono S C hbaseR hε'R hz
  have hzT : z ∈ stateNeighborhood S C relativeBase ηT :=
    stateNeighborhood_mono S C hbaseT hε'T hz
  have hzlow : z ∈ stateNeighborhood S C low ε' :=
    stateNeighborhood_mono S C hbaseLow le_rfl hz
  have hsmall : pairGrading (stateGrading S) realGrading low
      (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hzlow).trans (by
      have he : ε' ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  have hrelative := hrel z hzT hs θ
  have hτ : ContDiffAt ℝ ∞ τ (r, θ) := hrelative.1
  have hy : τ (r, θ) = (r, (τ (r, θ)).2) :=
    Prod.ext (canonicalCurrentPoint_root_radial hA hB.1 href hsref hzold hs m side θ) rfl
  have hcurrent : RootPhysicalFieldJetBound
      (pairGrading (stateGrading S) realGrading) rootLoss A
      (z - (C.referenceState, 0)) (K.chart z i) (K.height z i) (τ (r, θ)) := by
    rw [hy]
    exact (hroot z hzR hs (τ (r, θ)).2).2.2
  have hreference : RootPhysicalFieldJetBound
      (pairGrading (stateGrading S) realGrading) rootLoss A
      (z - (C.referenceState, 0)) (K.chart (C.referenceState, 0) i)
      (K.height (C.referenceState, 0) i) (r, θ) :=
    RootPhysicalFieldJetBound.from_zero (fun n => (hApos n).le)
      (by simpa only [sub_self] using (hroot _ hrefR hsref θ).2.2) _
  have hheight {f : PolarPoint → ℝ} {p : PolarPoint}
      (hf : PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
        rootLoss A (z - (C.referenceState, 0)) f p) :
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
        inputLoss Q (z - (C.referenceState, 0)) f p :=
    hf.mono hp (le_max_left _ _) (fun n => (hApos n).le) hAQ
  have hτjets (n : ℕ) (hn : 1 ≤ n) :
      ‖iteratedFDeriv ℝ n τ (r, θ)‖ ≤
        Q n * (1 + pairGrading (stateGrading S) realGrading (n + inputLoss)
          (z - (C.referenceState, 0))) :=
    (hrelative.2.2.1 n hn).trans (mul_le_mul (hRQ n)
      (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_right _ _) n) _))
      (add_nonneg zero_le_one (apply_nonneg _ _)) (hQ n).le)
  have hqjets := hbnd (z - (C.referenceState, 0)) hsmall
    (K.height (C.referenceState, 0) i) (fun y => (K.height z i y)⁻¹) τ (r, θ)
    hreference.2.1 (hcurrent.2.1.inv hcurrent.2.2.1.ne') hτ
    (hheight hreference.2.2.2.2.1) (hheight hcurrent.2.2.2.2.2) hτjets
  have hinvjets := hbnd (z - (C.referenceState, 0)) hsmall
    (fun y => (K.height (C.referenceState, 0) i y)⁻¹) (K.height z i) τ (r, θ)
    (hreference.2.1.inv hreference.2.2.1.ne') hcurrent.2.1 hτ
    (hheight hreference.2.2.2.2.2) (hheight hcurrent.2.2.2.2.1) hτjets
  have hclosed : (r, θ) ∈ physicalPieceClosed S K (C.referenceState, 0) i :=
    (canonicalCutRoot_mem_closed_and_zero hA hB.1 href hsref m side θ).1
  have hq := n04Coordinates_currentHeightRatio_contDiffAt_pos_closed
    hA href hsref hzold hs i hclosed
  refine ⟨hq.1, hq.2, ?_, ?_⟩
  · simpa only [n04CoordinatesCurrentHeightRatio, div_eq_mul_inv, τ] using hqjets
  · have he : (fun y => (n04CoordinatesCurrentHeightRatio C K z i y)⁻¹) =
        (fun y => (K.height (C.referenceState, 0) i y)⁻¹ * K.height z i (τ y)) := by
      funext y
      simp only [n04CoordinatesCurrentHeightRatio, inv_div, div_eq_mul_inv, mul_comm, τ]
    rw [he]
    exact hinvjets

end ContinuousFlexibility.Analysis
