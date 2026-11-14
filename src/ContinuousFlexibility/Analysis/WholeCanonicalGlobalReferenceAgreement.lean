module

public import ContinuousFlexibility.Analysis.WholeCanonicalAtlasReferencePartition
public import ContinuousFlexibility.Analysis.WholeCanonicalGlobalSymmetries

/-!
# The global relative fields on the reference pieces of the same atlas

The radius selector retains the whole-negative fields and the constructed
whole-positive fields. The genuine reference cut puts either negative
half inside its original component, where both stored charts give the
same actual travel transition and height ratio. On a positive piece the
reference identity and the actual inverse law identify the fields of the
same atlas record. No agreement conclusion is supplied as a hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04WholeCanonical_global_relative_reference_agreement
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (σ τ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) (n : ℕ)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (c d J H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (hm : ∀ i,
      let K := n04bActualTypedAtlas hT hS hN hfield e₀
      WholePositiveTransportMatching n
        (fun side => n04PositiveSourceMap (j i side) K z)
        (fun side => n04PositiveSourceHeight (j i side) K z)
        (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
        (c i) (d i) (J i) (H i))
    (href : ∀ i, σ (C.referenceState, 0) i = id ∧
      Q (C.referenceState, 0) i = (fun _ => (1 : ℝ))) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q N
    let F := n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id
    let q := n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
      (fun _ => (1 : ℝ))
    ∀ m, ∀ p ∈ referencePhysicalPieceOpen S W m,
      F p = canonicalCurrentPoint C W z m p ∧
        q p = W.height (C.referenceState, 0) m p / W.height z m (F p) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q N
  let F := n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id
  let q := n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
    (fun _ => (1 : ℝ))
  change ∀ m, ∀ p ∈ referencePhysicalPieceOpen S W m,
    F p = canonicalCurrentPoint C W z m p ∧
      q p = W.height (C.referenceState, 0) m p / W.height z m (F p)
  intro m p hp
  have hrad : W.physicalLeft m =
        n04WholePieceLeft C (n04bActualReferenceCut hN) (e m) ∧
      W.physicalRight m =
        n04WholePieceRight C (n04bActualReferenceCut hN) (e m) :=
    n04WholeCanonicalAtlasData_actual_reference_radii
      hT hS hN hfield e₀ e cell σ τ Q N m
  have hr : p.1 ∈ Ioo (n04WholePieceLeft C (n04bActualReferenceCut hN) (e m))
      (n04WholePieceRight C (n04bActualReferenceCut hN) (e m)) := by
    rw [← hrad.1, ← hrad.2]
    exact hp.1
  cases hi : e m with
  | inl a =>
      rcases a with ⟨a, side⟩
      have hhalf : p.1 ∈ Ioo (n04bNegativeLeft C (n04bActualReferenceCut hN) (a, side))
          (n04bNegativeRight C (n04bActualReferenceCut hN) (a, side)) := by
        simpa only [hi, n04WholePieceLeft, n04WholePieceRight] using hr
      have hwhole : p ∈ Ioo (C.left a) (C.right a) ×ˢ (univ : Set ℝ) :=
        ⟨n04b_negativeHalf_subset (n04bActualReferenceCut_mem hN) (a, side) hhalf,
          mem_univ _⟩
      have hclosed : p.1 ∈ Icc (C.left a) (C.right a) :=
        ⟨hwhole.1.1.le, hwhole.1.2.le⟩
      let k := if side then (K.cutPair a).2 else (K.cutPair a).1
      have hk : e₀ k = .inl (a, side) := by
        have hpair : K.cutPair a =
            (e₀.symm (.inl (a, false)), e₀.symm (.inl (a, true))) := rfl
        dsimp only [k]
        rw [hpair]
        cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true,
          Equiv.apply_symm_apply]
      have hstored (v : AnnularState S × ℝ) :
          W.chart v m = K.chart v k ∧ W.inverseChart v m = K.inverseChart v k ∧
            W.height v m = K.height v k := by
        rcases n04WholeCanonicalAtlasData_negative_fields
          C L K e cell σ τ Q N v m (a, side) hi with
          ⟨_, _, _, _, _, _, _, hchart, hinverse, hheight, _, _⟩
        exact ⟨hchart, hinverse, hheight⟩
      have hstoredPoint : canonicalCurrentPoint C W z m p =
          canonicalCurrentPoint C K z k p := by
        unfold canonicalCurrentPoint
        rw [(hstored z).2.1, (hstored (C.referenceState, 0)).1]
      have hFselected : F p = canonicalWholeNegativeTransport C K z a p :=
        n04WholeComponentField_eq_negative hN.1.1
          (canonicalWholeNegativeTransport C K z) (τ z) id (p := p) hclosed
      have hqselected : q p = canonicalWholeNegativeHeightRatio C K z a p :=
        n04WholeComponentField_eq_negative hN.1.1
          (canonicalWholeNegativeHeightRatio C K z) (Q z) (fun _ => (1 : ℝ))
          (p := p) hclosed
      have hcommon := canonicalWholeNegativeTransport_eq_travel hT hS hN hfield e₀ hz hs a
      have hFtravel : F p = n04CoordinatesNegativeTravelTransition S C L z a p :=
        hFselected.trans (hcommon.1 hwhole)
      have hqtravel : q p = n04CoordinatesNegativeTravelHeightRatio S C L z a p :=
        hqselected.trans (hcommon.2 hwhole)
      have hpoint : canonicalCurrentPoint C K z k p =
          n04CoordinatesNegativeTravelTransition S C L z a p :=
        n04Coordinates_actualAtlas_currentPoint_eq_travel
          hT hS hN hfield hz hs a e₀ k side hk hwhole
      have hratio : K.height (C.referenceState, 0) k p /
          K.height z k (n04CoordinatesNegativeTravelTransition S C L z a p) =
            n04CoordinatesNegativeTravelHeightRatio S C L z a p :=
        n04Coordinates_actualAtlas_height_ratio_eq_travel
          hT hS hN hfield hz hs a e₀ k side hk hwhole
      refine ⟨hFtravel.trans (hstoredPoint.trans hpoint).symm, ?_⟩
      calc
        q p = n04CoordinatesNegativeTravelHeightRatio S C L z a p := hqtravel
        _ = K.height (C.referenceState, 0) k p /
            K.height z k (n04CoordinatesNegativeTravelTransition S C L z a p) := hratio.symm
        _ = W.height (C.referenceState, 0) m p / W.height z m (F p) := by
          rw [(hstored (C.referenceState, 0)).2.2, (hstored z).2.2, hFtravel]
  | inr i =>
      have hpositive : p.1 ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) := by
        simpa only [hi, n04WholePieceLeft, n04WholePieceRight] using hr
      have hD := n04b_profileGeometry_of_through03 hN
      have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
      have hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
      have hFselected : F p = τ z i p :=
        n04WholeComponentField_eq_positive hf hC
          (canonicalWholeNegativeTransport C K z) (τ z) id (p := p) hpositive
      have hqselected : q p = Q z i p :=
        n04WholeComponentField_eq_positive hf hC
          (canonicalWholeNegativeHeightRatio C K z) (Q z) (fun _ => (1 : ℝ))
          (p := p) hpositive
      have hsame := n04WholeCanonicalAtlasData_positive_relative_fields
        C L K e cell σ τ Q N z m i hi (href i).1 (href i).2
        (hm i).geometry.left_inverse
      refine ⟨hFselected.trans (congrFun hsame.1 p).symm, ?_⟩
      calc
        q p = Q z i p := hqselected
        _ = n04CoordinatesCurrentHeightRatio C W z m p := (congrFun hsame.2 p).symm
        _ = W.height (C.referenceState, 0) m p / W.height z m (F p) := by
          unfold n04CoordinatesCurrentHeightRatio
          rw [hsame.1, hFselected]

/-- The same fixed fields provide the qualitative transport clauses,
including agreement with every reference piece of the same atlas. The
quantitative material estimates are not inputs or conclusions here. -/
theorem n04WholeCanonical_global_relative_transport_qualitative
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (σ τ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (c d J H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (hm : ∀ i,
      let K := n04bActualTypedAtlas hT hS hN hfield e₀
      WholePositiveTransportMatching 3
        (fun side => n04PositiveSourceMap (j i side) K z)
        (fun side => n04PositiveSourceHeight (j i side) K z)
        (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
        (c i) (d i) (J i) (H i))
    (href : ∀ i, σ (C.referenceState, 0) i = id ∧
      Q (C.referenceState, 0) i = (fun _ => (1 : ℝ))) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q N
    let F := n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id
    let q := n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
      (fun _ => (1 : ℝ))
    ContDiffOn ℝ 3 F (annularOpen D) ∧ ContDiffOn ℝ 3 q (annularOpen D) ∧
      MapsTo F (annularOpen D) (annularOpen D) ∧
      (∀ p, F (p + (0, Real.pi)) = F p + (0, Real.pi)) ∧
      Function.Periodic q (0, Real.pi) ∧
      (∀ p, F (p.1, -p.2) = ((F p).1, -(F p).2)) ∧
      (∀ r θ, q (r, -θ) = q (r, θ)) ∧
      (∀ m, ∀ p ∈ referencePhysicalPieceOpen S W m,
        F p = canonicalCurrentPoint C W z m p ∧
          q p = W.height (C.referenceState, 0) m p / W.height z m (F p)) ∧
      ∀ p ∈ annularOpen D, 0 < q p := by
  have hregular := n04WholeCanonical_global_relative_regular
    hT hS hN hfield e₀ 3 j (τ z) (σ z) (Q z) c d J H hz hs hm
  have hsym := n04WholeCanonical_global_relative_symmetries
    hT hS hN hfield e₀ 3 j (τ z) (σ z) (Q z) c d J H hz hs hm
  have hagree := n04WholeCanonical_global_relative_reference_agreement
    hT hS hN hfield e₀ e cell σ τ Q N 3 j c d J H hz hs hm href
  dsimp only
  exact ⟨hregular.1.of_le (by norm_num), hregular.2.1, hregular.2.2.1,
    hsym.1, hsym.2.1, hsym.2.2.1, hsym.2.2.2, hagree, hregular.2.2.2⟩

end ContinuousFlexibility.Analysis
