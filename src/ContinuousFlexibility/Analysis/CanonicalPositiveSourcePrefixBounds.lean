module

public import ContinuousFlexibility.Analysis.CanonicalPositiveSourceJetBounds

/-!
# A single high-data envelope for the retained endpoint family

The finite sum is chosen before the state and is linear in its one high
grading. It supplies the positive coordinate and full height jets needed
at any requested order. This operation never selects an interpolation
width, changes its fixed construction order, or changes the stored atlas.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped BigOperators ContDiff

theorem exists_rootEndpointTameJet_finite_prefix_envelope
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (loss : ℕ)
    (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (z : E) (F : PolarPoint → PolarPoint)
      (q : PolarPoint → ℝ) (r : ℝ), RootEndpointTameJetBounds p loss A z F q r →
      1 ≤ B * (1 + p (N + loss) z) ∧
      (∀ k, 1 ≤ k → k ≤ N → ∀ θ,
        ‖iteratedFDeriv ℝ k F (r, θ)‖ ≤ B * (1 + p (N + loss) z)) ∧
      (∀ k, k ≤ N → ∀ θ,
        ‖iteratedFDeriv ℝ k q (r, θ)‖ ≤ B * (1 + p (N + loss) z)) ∧
      ∀ k, k ≤ N → ∀ θ,
        ‖iteratedFDeriv ℝ k (fun y => (q y)⁻¹) (r, θ)‖ ≤ B * (1 + p (N + loss) z) := by
  let B : ℝ := 1 + ∑ k ∈ Finset.range (N + 1), A k
  have hB : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hA k)
  have hAB (k : ℕ) (hk : k ≤ N) : A k ≤ B :=
    (Finset.single_le_sum (fun j _ => hA j)
      (Finset.mem_range.mpr (by omega : k < N + 1))).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨B, hB, ?_⟩
  intro z F q r h
  have hone : 1 ≤ 1 + p (N + loss) z := le_add_of_nonneg_right (apply_nonneg _ _)
  have hraise (k : ℕ) (hk : k ≤ N) :
      A k * (1 + p (k + loss) z) ≤ B * (1 + p (N + loss) z) :=
    mul_le_mul (hAB k hk)
      (add_le_add le_rfl (hp (Nat.add_le_add_right hk loss) z))
      (add_nonneg zero_le_one (apply_nonneg _ _)) (zero_le_one.trans hB)
  exact ⟨hB.trans (le_mul_of_one_le_right (zero_le_one.trans hB) hone),
    fun k hk hkn θ => (h.coordinate_jets k hk θ).trans (hraise k hkn),
    fun k hkn θ => (h.height_jets k θ).trans (hraise k hkn),
    fun k hkn θ => (h.inverse_height_jets k θ).trans (hraise k hkn)⟩

private theorem positiveSourceFinitePrefixes_of_allJets
    {E I : Type*} [AddCommGroup E] [Module ℝ E] {J : I → Type*}
    {p : ℕ → Seminorm ℝ E} {U : ℕ → ℝ → Set E} {sector : E → Prop}
    {center : E → E}
    {F : (i : I) → J i → Bool → E → PolarPoint → PolarPoint}
    {q : (i : I) → J i → Bool → E → PolarPoint → ℝ}
    {r : I → Bool → ℝ} {base : ℕ} {ε : ℝ}
    (hp : Monotone p)
    (hsources : ∃ newBase outLoss : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ outLoss ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i : I, ∀ j : J i, ∃ A : ℕ → ℝ, (∀ k, 1 ≤ A k) ∧
        ∀ z ∈ U newBase ε', sector z → ∀ side : Bool,
          RootEndpointTameJetBounds p outLoss A (center z)
            (F i j side z) (q i j side z) (r i side)) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ outLoss ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i : I, ∀ j : J i, ∃ B : ℕ → ℝ, (∀ N, 1 ≤ B N) ∧
        ∀ N z, z ∈ U newBase ε' → sector z → ∀ side : Bool,
          let M := B N * (1 + p (N + outLoss) (center z))
          1 ≤ M ∧
          (∀ k, 1 ≤ k → k ≤ N → ∀ θ,
            ‖iteratedFDeriv ℝ k (F i j side z) (r i side, θ)‖ ≤ M) ∧
          (∀ k, k ≤ N → ∀ θ,
            ‖iteratedFDeriv ℝ k (q i j side z) (r i side, θ)‖ ≤ M) ∧
          ∀ k, k ≤ N → ∀ θ,
            ‖iteratedFDeriv ℝ k (fun y => (q i j side z y)⁻¹) (r i side, θ)‖ ≤ M := by
  classical
  obtain ⟨newBase, outLoss, ε', hb, hl, hε', hε'ε, hsources⟩ := hsources
  refine ⟨newBase, outLoss, ε', hb, hl, hε', hε'ε, ?_⟩
  intro i j
  obtain ⟨A, hA, hsource⟩ := hsources i j
  choose B hB hbound using fun N => exists_rootEndpointTameJet_finite_prefix_envelope
    hp outLoss A (fun k => zero_le_one.trans (hA k)) N
  refine ⟨B, hB, ?_⟩
  intro N z hz hs side
  exact hbound N (center z) (F i j side z) (q i j side z) (r i side)
    (hsource z hz hs side)

/-- One sequence of finite-prefix coefficients controls the genuine
source fields on one common neighborhood, for every high order. -/
theorem n04Coordinates_actual_positiveSource_finite_prefixes
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
      ∃ B : ℕ → ℝ, (∀ N, 1 ≤ B N) ∧
        ∀ N z, z ∈ stateNeighborhood S C newBase ε' → stateSector S z.1 → ∀ side,
          let K := n04bActualTypedAtlas hT hS hN hfield e
          let F := n04PositiveSourceMap (j side) K z
          let q := n04PositiveSourceHeight (j side) K z
          let r := n04PositiveEndpoint i side
          let M := B N * (1 + pairGrading (stateGrading S) realGrading (N + outLoss)
            (z - (C.referenceState, 0)))
          1 ≤ M ∧
          (∀ k, 1 ≤ k → k ≤ N → ∀ θ, ‖iteratedFDeriv ℝ k F (r, θ)‖ ≤ M) ∧
          (∀ k, k ≤ N → ∀ θ, ‖iteratedFDeriv ℝ k q (r, θ)‖ ≤ M) ∧
          ∀ k, k ≤ N → ∀ θ, ‖iteratedFDeriv ℝ k (fun y => (q y)⁻¹) (r, θ)‖ ≤ M := by
  exact positiveSourceFinitePrefixes_of_allJets
    (E := AnnularState S × ℝ)
    (I := N04PositiveComponent D.a D.b (deriv D.w))
    (J := fun i => (side : Bool) → N04PositiveEndpointSource C i side)
    (p := pairGrading (stateGrading S) realGrading)
    (U := stateNeighborhood S C) (sector := fun z => stateSector S z.1)
    (center := fun z => z - (C.referenceState, 0))
    (F := fun _ j side z =>
      n04PositiveSourceMap (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
    (q := fun _ j side z =>
      n04PositiveSourceHeight (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
    (r := n04PositiveEndpoint)
    (tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl))
    (n04Coordinates_actual_positiveSource_allJets hT hS hN hfield e)

end ContinuousFlexibility.Analysis
