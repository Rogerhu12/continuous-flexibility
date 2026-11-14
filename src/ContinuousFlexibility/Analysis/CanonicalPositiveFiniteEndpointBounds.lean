module

public import ContinuousFlexibility.Analysis.CanonicalRootFiniteEndpointBounds
public import ContinuousFlexibility.Analysis.CanonicalWholePositiveTransport

/-!
# Derived finite bounds for the actual positive endpoint sources

The certified source of each end is fixed before the state. A negative
neighbor uses its actual opposite root; an ambient end uses identity and
height one. The numerical lower/upper envelopes combine the two ends,
without changing the stored atlas or requiring a common material cell.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

private theorem rootEndpointJetBounds_identity (n : ℕ) (r : ℝ) :
    RootEndpointJetBounds n (id : PolarPoint → PolarPoint) (fun _ => 1) r 1 1 1 := by
  refine {
    radial_lower := ?_
    angular_lower := ?_
    coordinate_jets := ?_
    height_value := fun _ => le_rfl
    height_inverse := ?_
    height_jets := ?_ }
  · intro θ
    simp only [id_eq, radialPartial_fst, le_refl]
  · intro θ
    simp only [id_eq, angularPartial_snd, le_refl]
  · intro k hk _hkn θ
    exact (flowJet_norm_iteratedFDeriv_clm_le
      (ContinuousLinearMap.id ℝ PolarPoint) hk (r, θ)).trans
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := PolarPoint))
  · intro θ
    simp only [inv_one, le_refl]
  · intro k hk _hkn θ
    cases k with
    | zero => omega
    | succ k =>
        rw [iteratedFDeriv_succ_const]
        simp only [Pi.zero_apply, norm_zero, zero_le_one]

/-- All six finite input clauses of the whole-positive construction are
proved for the actual source maps. The common base/radius are chosen
before positive components, source choices and numerical envelopes. -/
theorem n04b_exists_common_positive_endpoint_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) (n : ℕ) :
    ∃ newBase : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ j : ∀ side, N04PositiveEndpointSource C i side,
      ∃ κ M H : ℝ, 0 < κ ∧ κ ≤ 1 ∧ κ⁻¹ ≤ M ∧ 1 ≤ M ∧ 1 ≤ H ∧
        ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
          WholePositiveEndpointJetBounds n
            (fun side => n04PositiveSourceMap (j side) K z)
            (fun side => n04PositiveSourceHeight (j side) K z)
            (n04PositiveLeft i) (n04PositiveRight i) κ κ M H := by
  classical
  obtain ⟨newBase, ε', hb, hε', hε'ε, hroots⟩ :=
    n04b_exists_common_root_finite_endpoint_bounds hS hT hN hfield hA hB n
  refine ⟨newBase, ε', hb, hε', hε'ε, ?_⟩
  intro i j
  have hsource (side : Bool) (j : N04PositiveEndpointSource C i side) :
      ∃ κ M H : ℝ, 0 < κ ∧ κ ≤ 1 ∧ 1 ≤ M ∧ 1 ≤ H ∧
        ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
          RootEndpointJetBounds n (n04PositiveSourceMap j K z)
            (n04PositiveSourceHeight j K z) (n04PositiveEndpoint i side) κ M H := by
    rcases j with ⟨o, ho⟩
    cases o with
    | none =>
        refine ⟨1, 1, 1, zero_lt_one, le_rfl, le_rfl, le_rfl, ?_⟩
        intro z _hz _hs
        exact rootEndpointJetBounds_identity n (n04PositiveEndpoint i side)
    | some m =>
        obtain ⟨κ, M, H, hκ, hκone, hM, hH, hbound⟩ := hroots m (!side)
        refine ⟨κ, M, H, hκ, hκone, hM, hH, ?_⟩
        intro z hz hs
        change RootEndpointJetBounds n
          (canonicalCurrentPoint C K z (if side then (K.cutPair m).1 else (K.cutPair m).2))
          (n04CoordinatesCurrentHeightRatio C K z
            (if side then (K.cutPair m).1 else (K.cutPair m).2))
          (n04PositiveEndpoint i side) κ M H
        change n04PositiveEndpoint i side = (if side then C.left m else C.right m) at ho
        rw [ho]
        have hh := hbound z hz hs
        cases side <;> exact hh
  choose κ M H hκ hκone hM hH hbound using fun side => hsource side (j side)
  let κ₀ := min (κ false) (κ true)
  let M₀ := max (max (M false) (M true)) κ₀⁻¹
  let H₀ := max (H false) (H true)
  have hκ₀ : 0 < κ₀ := lt_min (hκ false) (hκ true)
  have hκ₀one : κ₀ ≤ 1 := (min_le_left _ _).trans (hκone false)
  have hM₀ : 1 ≤ M₀ := (hM false).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hκ₀inv : κ₀⁻¹ ≤ M₀ := le_max_right _ _
  have hH₀ : 1 ≤ H₀ := (hH false).trans (le_max_left _ _)
  have hκside (side : Bool) : κ₀ ≤ κ side := by
    cases side
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hMside (side : Bool) : M side ≤ M₀ := by
    apply le_trans (b := max (M false) (M true)) _ (le_max_left _ _)
    cases side
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hHside (side : Bool) : H side ≤ H₀ := by
    cases side
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine ⟨κ₀, M₀, H₀, hκ₀, hκ₀one, hκ₀inv, hM₀, hH₀, ?_⟩
  intro z hz hs
  have hf (side : Bool) := hbound side z hz hs
  exact {
    angular_lower := fun side θ => (hκside side).trans ((hf side).angular_lower θ)
    radial_lower := fun side θ => (hκside side).trans ((hf side).radial_lower θ)
    coordinate_jets := fun side k hk hkn θ =>
      ((hf side).coordinate_jets k hk hkn θ).trans (hMside side)
    height_value := fun side θ => ((hf side).height_value θ).trans (hHside side)
    height_inverse := fun side θ => ((hf side).height_inverse θ).trans (hHside side)
    height_jets := fun side k hk hkn θ =>
      ((hf side).height_jets k hk hkn θ).trans (hHside side) }

end ContinuousFlexibility.Analysis
