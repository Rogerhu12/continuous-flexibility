import ContinuousFlexibility.Analysis.CanonicalPositiveFiniteEndpointBounds
import ContinuousFlexibility.Analysis.N04bActualAtlasInteriorCompletion
import ContinuousFlexibility.Analysis.CanonicalPositiveSourceInteriorDivision

/-!
# All ordinary jets of the same certified positive endpoint sources

The common neighborhood and loss precede every component and derivative
order. The source is the retained negative root field or the actual
ambient identity. Its high-order coefficient is independent of the state;
only the single displayed high grading depends on the state. This does
not assert material growth of those component coefficients.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

structure RootEndpointTameJetBounds {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (A : ℕ → ℝ) (z : E)
    (F : PolarPoint → PolarPoint) (q : PolarPoint → ℝ) (r : ℝ) : Prop where
  coordinate_jets : ∀ k : ℕ, 1 ≤ k → ∀ θ : ℝ,
    ‖iteratedFDeriv ℝ k F (r, θ)‖ ≤ A k * (1 + p (k + loss) z)
  height_jets : ∀ k : ℕ, ∀ θ : ℝ,
    ‖iteratedFDeriv ℝ k q (r, θ)‖ ≤ A k * (1 + p (k + loss) z)
  inverse_height_jets : ∀ k : ℕ, ∀ θ : ℝ,
    ‖iteratedFDeriv ℝ k (fun y => (q y)⁻¹) (r, θ)‖ ≤ A k * (1 + p (k + loss) z)

theorem RootEndpointTameJetBounds.mono_envelope
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A B : ℕ → ℝ} {z : E}
    {F : PolarPoint → PolarPoint} {q : PolarPoint → ℝ} {r : ℝ}
    (h : RootEndpointTameJetBounds p loss A z F q r) (hAB : ∀ k, A k ≤ B k) :
    RootEndpointTameJetBounds p loss B z F q r := by
  have he (k : ℕ) : A k * (1 + p (k + loss) z) ≤ B k * (1 + p (k + loss) z) :=
    mul_le_mul_of_nonneg_right (hAB k) (add_nonneg zero_le_one (apply_nonneg _ _))
  exact {
    coordinate_jets := fun k hk θ => (h.coordinate_jets k hk θ).trans (he k)
    height_jets := fun k θ => (h.height_jets k θ).trans (he k)
    inverse_height_jets := fun k θ => (h.inverse_height_jets k θ).trans (he k) }

private theorem rootEndpointTameJetBounds_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (z : E) (r : ℝ) :
    RootEndpointTameJetBounds p loss (fun _ => 1) z id (fun _ => 1) r := by
  have hone (k : ℕ) : 1 ≤ (1 : ℝ) * (1 + p (k + loss) z) := by
    rw [one_mul]
    exact le_add_of_nonneg_right (apply_nonneg (p (k + loss)) z)
  have hconst (k : ℕ) (θ : ℝ) :
      ‖iteratedFDeriv ℝ k (fun _ : PolarPoint => (1 : ℝ)) (r, θ)‖ ≤ 1 := by
    cases k with
    | zero => simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_one, le_refl]
    | succ k =>
        rw [iteratedFDeriv_succ_const]
        simp only [Pi.zero_apply, norm_zero, zero_le_one]
  exact {
    coordinate_jets := fun k hk θ =>
      ((flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.id ℝ PolarPoint) hk (r, θ)).trans
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := PolarPoint))).trans (hone k)
    height_jets := fun k θ => (hconst k θ).trans (hone k)
    inverse_height_jets := fun k θ => by
      simpa only [inv_one] using (hconst k θ).trans (hone k) }

private theorem rootEndpointTameJetBounds_of_field_bounds
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {lF lQ outLoss : ℕ}
    {A B Q : ℕ → ℝ} {z : E}
    {F : PolarPoint → PolarPoint} {q : PolarPoint → ℝ} {r : ℝ}
    (hp : Monotone p) (hQone : ∀ k, 1 ≤ Q k)
    (hAQ : ∀ k, A k ≤ Q k) (hBQ : ∀ k, B k ≤ Q k)
    (hlF : lF ≤ outLoss) (hlQ : lQ ≤ outLoss)
    (hF : ∀ k : ℕ, 1 ≤ k → ∀ θ : ℝ,
      ‖iteratedFDeriv ℝ k F (r, θ)‖ ≤ A k * (1 + p (k + lF) z))
    (hq : ∀ k : ℕ, ∀ θ : ℝ,
      ‖iteratedFDeriv ℝ k q (r, θ)‖ ≤ B k * (1 + p (k + lQ) z))
    (hqi : ∀ k : ℕ, ∀ θ : ℝ,
      ‖iteratedFDeriv ℝ k (fun y => (q y)⁻¹) (r, θ)‖ ≤
        B k * (1 + p (k + lQ) z)) :
    RootEndpointTameJetBounds p outLoss Q z F q r := by
  have hraise (a : ℕ → ℝ) (haQ : ∀ k, a k ≤ Q k)
      (l : ℕ) (hl : l ≤ outLoss) (k : ℕ) :
      a k * (1 + p (k + l) z) ≤ Q k * (1 + p (k + outLoss) z) :=
    mul_le_mul (haQ k)
      (add_le_add le_rfl (hp (Nat.add_le_add_left hl k) _))
      (add_nonneg zero_le_one (apply_nonneg _ _)) (zero_le_one.trans (hQone k))
  exact {
    coordinate_jets := fun k hk θ => (hF k hk θ).trans (hraise A hAQ lF hlF k)
    height_jets := fun k θ => (hq k θ).trans (hraise B hBQ lQ hlQ k)
    inverse_height_jets := fun k θ => (hqi k θ).trans (hraise B hBQ lQ hlQ k) }

private theorem canonicalRootTameJetFamily_of_families
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    {bF lF bQ lQ : ℕ} {εF εQ : ℝ} (m : ℕ) (side : Bool)
    (hp : Monotone (pairGrading (stateGrading S) realGrading))
    (hF : ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
      CanonicalRootRelativeJetFamily S C K bF lF εF m side A)
    (hQ : ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      CanonicalRootHeightJetFamily S C K bQ lQ εQ m side B) :
    ∃ Q : ℕ → ℝ, (∀ k, 1 ≤ Q k) ∧
      ∀ z ∈ stateNeighborhood S C (max bF bQ) (min εF εQ), stateSector S z.1 →
        RootEndpointTameJetBounds (pairGrading (stateGrading S) realGrading)
          (max lF lQ) Q (z - (C.referenceState, 0))
          (canonicalCurrentPoint C K z (if side then (K.cutPair m).2 else (K.cutPair m).1))
          (n04CoordinatesCurrentHeightRatio C K z
            (if side then (K.cutPair m).2 else (K.cutPair m).1))
          (n01ComponentRoot C m side) := by
  let A : ℕ → ℝ := Classical.choose hF
  let B : ℕ → ℝ := Classical.choose hQ
  have hApos : ∀ k, 0 < A k := (Classical.choose_spec hF).1
  have hBpos : ∀ k, 0 < B k := (Classical.choose_spec hQ).1
  have hrelative : CanonicalRootRelativeJetFamily S C K bF lF εF m side A :=
    (Classical.choose_spec hF).2
  have hheight : CanonicalRootHeightJetFamily S C K bQ lQ εQ m side B :=
    (Classical.choose_spec hQ).2
  let Q : ℕ → ℝ := fun k => 1 + A k + B k
  have hQone (k : ℕ) : 1 ≤ Q k := by
    dsimp only [Q]
    linarith only [hApos k, hBpos k]
  have hAQ (k : ℕ) : A k ≤ Q k := by
    dsimp only [Q]
    linarith only [hBpos k]
  have hBQ (k : ℕ) : B k ≤ Q k := by
    dsimp only [Q]
    linarith only [hApos k]
  refine ⟨Q, hQone, ?_⟩
  intro z hz hs
  have hzF : z ∈ stateNeighborhood S C bF εF :=
    stateNeighborhood_mono S C (le_max_left bF bQ) (min_le_left εF εQ) hz
  have hzQ : z ∈ stateNeighborhood S C bQ εQ :=
    stateNeighborhood_mono S C (le_max_right bF bQ) (min_le_right εF εQ) hz
  exact rootEndpointTameJetBounds_of_field_bounds hp hQone hAQ hBQ
    (le_max_left lF lQ) (le_max_right lF lQ)
    (fun k hk θ => (hrelative z hzF hs θ).2.2.1 k hk)
    (fun k θ => (hheight z hzQ hs θ).2.2.1 k)
    (fun k θ => (hheight z hzQ hs θ).2.2.2 k)

private theorem positiveSourceJetBounds_of_rootFamilies
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hroots : ∀ m : ℕ, ∀ side : Bool, ∃ A : ℕ → ℝ, (∀ k, 1 ≤ A k) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootEndpointTameJetBounds (pairGrading (stateGrading S) realGrading)
          loss A (z - (C.referenceState, 0))
          (canonicalCurrentPoint C K z (if side then (K.cutPair m).2 else (K.cutPair m).1))
          (n04CoordinatesCurrentHeightRatio C K z
            (if side then (K.cutPair m).2 else (K.cutPair m).1))
          (n01ComponentRoot C m side))
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (side : Bool)
    (j : N04PositiveEndpointSource C i side) :
    ∃ A : ℕ → ℝ, (∀ k, 1 ≤ A k) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootEndpointTameJetBounds (pairGrading (stateGrading S) realGrading)
          loss A (z - (C.referenceState, 0))
          (n04PositiveSourceMap j K z) (n04PositiveSourceHeight j K z)
          (n04PositiveEndpoint i side) := by
  rcases j with ⟨o, ho⟩
  cases o with
  | none =>
      exact ⟨fun _ => 1, fun _ => le_rfl, fun z _hz _hs =>
        rootEndpointTameJetBounds_identity _ loss (z - (C.referenceState, 0)) _⟩
  | some m =>
      let A : ℕ → ℝ := Classical.choose (hroots m (!side))
      have hAone : ∀ k, 1 ≤ A k := (Classical.choose_spec (hroots m (!side))).1
      refine ⟨A, hAone, ?_⟩
      intro z hz hs
      have h : RootEndpointTameJetBounds
          (pairGrading (stateGrading S) realGrading) loss A (z - (C.referenceState, 0))
          (canonicalCurrentPoint C K z
            (if !side then (K.cutPair m).2 else (K.cutPair m).1))
          (n04CoordinatesCurrentHeightRatio C K z
            (if !side then (K.cutPair m).2 else (K.cutPair m).1))
          (n01ComponentRoot C m (!side)) :=
        (Classical.choose_spec (hroots m (!side))).2 z hz hs
      change RootEndpointTameJetBounds _ loss A _
        (canonicalCurrentPoint C K z (if side then (K.cutPair m).1 else (K.cutPair m).2))
        (n04CoordinatesCurrentHeightRatio C K z
          (if side then (K.cutPair m).1 else (K.cutPair m).2))
        (n04PositiveEndpoint i side)
      change n04PositiveEndpoint i side = (if side then C.left m else C.right m) at ho
      rw [ho]
      cases side <;> exact h

private theorem positiveSourceJets_of_rootFamilyExistentials
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hp : Monotone (pairGrading (stateGrading S) realGrading))
    (hF : ∃ bF lF : ℕ, ∃ εF : ℝ,
      base ≤ bF ∧ lF ≤ bF ∧ 0 < εF ∧ εF ≤ ε ∧
        ∀ m : ℕ, ∀ side : Bool, ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
          CanonicalRootRelativeJetFamily S C K bF lF εF m side A)
    (hQ : ∃ bQ lQ : ℕ, ∃ εQ : ℝ,
      base ≤ bQ ∧ lQ ≤ bQ ∧ 0 < εQ ∧ εQ ≤ ε ∧
        ∀ m : ℕ, ∀ side : Bool, ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
          CanonicalRootHeightJetFamily S C K bQ lQ εQ m side B) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ outLoss ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ j : ∀ side, N04PositiveEndpointSource C i side,
      ∃ A : ℕ → ℝ, (∀ k, 1 ≤ A k) ∧
        ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 → ∀ side,
          RootEndpointTameJetBounds (pairGrading (stateGrading S) realGrading)
            outLoss A (z - (C.referenceState, 0))
            (n04PositiveSourceMap (j side) K z) (n04PositiveSourceHeight (j side) K z)
            (n04PositiveEndpoint i side) := by
  classical
  obtain ⟨bF, lF, εF, hbF, hlF, hεF, hεFε, hF⟩ := hF
  obtain ⟨bQ, lQ, εQ, hbQ, hlQ, hεQ, hεQε, hQ⟩ := hQ
  let newBase := max bF bQ
  let outLoss := max lF lQ
  let ε' := min εF εQ
  refine ⟨newBase, outLoss, ε', hbF.trans (le_max_left _ _), max_le_max hlF hlQ,
    lt_min hεF hεQ, (min_le_left _ _).trans hεFε, ?_⟩
  intro i j
  have hroots (m : ℕ) (side : Bool) :=
    canonicalRootTameJetFamily_of_families m side hp (hF m side) (hQ m side)
  choose A hAone hbound using fun side =>
    positiveSourceJetBounds_of_rootFamilies hroots i side (j side)
  let B : ℕ → ℝ := fun k => A false k + A true k
  have hB (k : ℕ) : 1 ≤ B k := by
    dsimp only [B]
    linarith only [hAone false k, hAone true k]
  have hAB (side : Bool) (k : ℕ) : A side k ≤ B k := by
    cases side
    · exact le_add_of_nonneg_right (zero_le_one.trans (hAone true k))
    · exact le_add_of_nonneg_left (zero_le_one.trans (hAone false k))
  exact ⟨B, hB, fun z hz hs side => (hbound side z hz hs).mono_envelope (hAB side)⟩

/-- Certified endpoint selection preserves the actual all-order root
estimates. Both ends use one envelope and one common derivative loss. -/
theorem n04b_exists_common_positive_source_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ outLoss ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ j : ∀ side, N04PositiveEndpointSource C i side,
      ∃ A : ℕ → ℝ, (∀ k, 1 ≤ A k) ∧
        ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 → ∀ side,
          RootEndpointTameJetBounds (pairGrading (stateGrading S) realGrading)
            outLoss A (z - (C.referenceState, 0))
            (n04PositiveSourceMap (j side) K z) (n04PositiveSourceHeight (j side) K z)
            (n04PositiveEndpoint i side) := by
  exact positiveSourceJets_of_rootFamilyExistentials
    (tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl))
    (n04b_exists_common_root_relative_positiveJets hS hT hN hfield hA hB)
    (n04b_exists_common_root_heightJets hS hT hN hfield hA hB)

/-- The temporary completion affects no source field. These all-order
estimates therefore apply to the original actual typed atlas itself. -/
theorem n04Coordinates_actual_positiveSource_allJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ outLoss ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ j : ∀ side, N04PositiveEndpointSource C i side,
      ∃ A : ℕ → ℝ, (∀ k, 1 ≤ A k) ∧
        ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 → ∀ side,
          let K := n04bActualTypedAtlas hT hS hN hfield e
          RootEndpointTameJetBounds (pairGrading (stateGrading S) realGrading)
            outLoss A (z - (C.referenceState, 0))
            (n04PositiveSourceMap (j side) K z) (n04PositiveSourceHeight (j side) K z)
            (n04PositiveEndpoint i side) := by
  have hA := n04bWithInteriorDivision_partA
    (n04b_actualTypedAtlas_partA hT hS hN hfield e)
  have hB := n04bActualTypedAtlas_interiorCompletion_partB hT hS hN hfield e
  have hout := n04b_exists_common_positive_source_jets hS hT hN hfield hA hB
  simpa only [n04PositiveSourceMap_withInteriorDivision,
    n04PositiveSourceHeight_withInteriorDivision] using hout

end ContinuousFlexibility.Analysis
