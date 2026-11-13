import ContinuousFlexibility.Analysis.N04RealizationRootEndpointControls
import ContinuousFlexibility.Analysis.N04RealizationRetainedPositiveEndpoints
import ContinuousFlexibility.Analysis.CanonicalWholePositiveTransport
import ContinuousFlexibility.Analysis.RetainedPositiveEndpointHostSample

/-!
# Positive endpoint controls at the prescribed midpoint sample

The original negative host estimates are transferred to any supplied cell
containing the actual positive midpoint. The retained seed excludes
ambient positive endpoints. The explicit lower, coordinate and height
controls are selected before the positive transport, on the same atlas
and one common neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

def N04RealizationPositiveEndpointControls
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (n base : ℕ) (ε C0 B : ℝ) : Prop :=
  ∀ (i : N04PositiveComponent D.a D.b (deriv D.w)) (j : ℕ),
    n04PositiveMidpoint i ∈ D.cells j →
    ∀ src : (side : Bool) → N04PositiveEndpointSource C i side,
      let M : ℝ := B * (C0 * T.E0 (T.sample j)) ^ B
      1 ≤ M ∧ ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        WholePositiveEndpointJetBounds n
          (fun side => n04PositiveSourceMap (src side) K z)
          (fun side => n04PositiveSourceHeight (src side) K z)
          (n04PositiveLeft i) (n04PositiveRight i) M⁻¹ M⁻¹ M M

/-- The same retained construction has explicit sample-controlled
positive endpoint inputs before any transport or height correction. -/
theorem n04Realization_exists_positiveEndpoint_material_controls
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2)
    (hq : 0 < q) {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    (Q : SeedReferenceConstruction q) (hQ : Q.reference = Γ.reference)
    {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε Kopt : ℝ}
    (hS : IsPhysicalSpaces Γ.reference T S) (hT : IsMaterialData Γ.reference T)
    (hN : NonlinearPropertiesThrough03 Γ.reference T S C E L base loss ε)
    (hfield : N04bFieldRegularity Γ.reference S C L base ε)
    (hA : N04PartA Γ.reference S C K base ε) (hB : N04PartB S C L K base ε)
    (hKopt : 0 < Kopt)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m))
    (hoptical : ∀ m x, x ∈ Ioo (C.left m) (C.right m) →
      Kopt⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-Kopt) *
        min (x - C.left m) (C.right m - x) ≤
          -deriv Γ.reference.w x / (x * Γ.reference.w x))
    (n : ℕ) :
    ∃ C0 B : ℝ, ∃ newBase : ℕ, ∃ η : ℝ,
      1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      1 ≤ B ∧ base ≤ newBase ∧ 0 < η ∧ η ≤ ε ∧
      N04RealizationPositiveEndpointControls
        Γ.reference T S C K n newBase η C0 B := by
  classical
  obtain ⟨C0, B₀, A₀, newBase, η, hC0, hfloor, hB₀, hA₀,
    hb, hη, hηε, hroots⟩ :=
    n04Realization_exists_rootEndpoint_material_controls hS hT hN hfield hA hB hKopt n
  have hC : controlGeometryConditions Γ.reference S C := hN.1.1.2.2.2.1
  obtain ⟨K₁, A₁, hK₁, hA₁, hsample⟩ :=
    retainedReference_positive_endpoint_host_sample_bound
      P hSelected hband hq hΓ hw hcoordinates hC hT hA₀.le
  have hC0pos : 0 < C0 := zero_lt_one.trans_le hC0
  let D : ℝ := B₀ * C0 ^ A₀ * K₁
  let B : ℝ := 2 + D + A₁
  have hD : 0 < D :=
    mul_pos (mul_pos hB₀ (Real.rpow_pos_of_pos hC0pos _)) hK₁
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hD, hA₁]
  have hDB : 1 + D ≤ B := by dsimp only [B]; linarith only [hA₁]
  have hA₁B : A₁ ≤ B := by dsimp only [B]; linarith only [hD]
  refine ⟨C0, B, newBase, η, hC0, hfloor, hB, hb, hη, hηε, ?_⟩
  intro i j hmid src
  let W : ℝ := C0 * T.E0 (T.sample j)
  let M : ℝ := B * W ^ B
  have hW : 1 ≤ W := hfloor j
  have hEj : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hΓ.2.1 hT j)).2.2.1
  have hEW : T.E0 (T.sample j) ≤ W := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC0 hEj.le
  have hWP : 1 ≤ W ^ B := Real.one_le_rpow hW (zero_le_one.trans hB)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hB hWP
  refine ⟨hM, fun z hz hs => ?_⟩
  have hsource (side : Bool) (s : N04PositiveEndpointSource C i side) :
      RootEndpointJetBounds n (n04PositiveSourceMap s K z)
        (n04PositiveSourceHeight s K z) (n04PositiveEndpoint i side) M⁻¹ M M := by
    rcases s with ⟨o, ho⟩
    cases o with
    | none =>
        have hc := (n04Realization_seed_positive_endpoints_sameReference Q hQ i side).1
        change n04PositiveEndpoint i side =
          (if side then Γ.reference.b else Γ.reference.a) at ho
        exfalso
        cases side
        · exact (ne_of_gt hc.1) (by
            simpa only [Bool.false_eq_true, ↓reduceIte] using ho)
        · exact (ne_of_lt hc.2) (by simpa only [↓reduceIte] using ho)
    | some m =>
        change n04PositiveEndpoint i side = (if side then C.left m else C.right m) at ho
        have hsample' := hsample i side m (C.cell m) j (hhost m) ho hmid
        have hEm : 0 < T.E0 (T.sample (C.cell m)) :=
          (hT.2.1 _ (materialSample_mem_interval hΓ.2.1 hT (C.cell m))).2.2.1
        let M₀ : ℝ := 1 + B₀ * (C0 * T.E0 (T.sample (C.cell m))) ^ A₀
        have hM₀pos : 0 < M₀ := by
          exact add_pos_of_pos_of_nonneg zero_lt_one
            (mul_nonneg hB₀.le (Real.rpow_nonneg (mul_nonneg hC0pos.le hEm.le) _))
        have hpower : T.E0 (T.sample j) ^ A₁ ≤ W ^ B :=
          (Real.rpow_le_rpow hEj.le hEW hA₁).trans
            (Real.rpow_le_rpow_of_exponent_le hW hA₁B)
        have hM₀ : M₀ ≤ M := by
          calc
            _ = 1 + (B₀ * C0 ^ A₀) * T.E0 (T.sample (C.cell m)) ^ A₀ := by
              dsimp only [M₀]
              rw [Real.mul_rpow hC0pos.le hEm.le]
              ring
            _ ≤ 1 + (B₀ * C0 ^ A₀) * (K₁ * T.E0 (T.sample j) ^ A₁) :=
              add_le_add_left (mul_le_mul_of_nonneg_left hsample'
                (mul_nonneg hB₀.le (Real.rpow_nonneg hC0pos.le _))) 1
            _ = 1 + D * T.E0 (T.sample j) ^ A₁ := by dsimp only [D]; ring
            _ ≤ W ^ B + D * W ^ B := add_le_add hWP
              (mul_le_mul_of_nonneg_left hpower hD.le)
            _ = (1 + D) * W ^ B := by ring
            _ ≤ B * W ^ B :=
              mul_le_mul_of_nonneg_right hDB (Real.rpow_nonneg (zero_le_one.trans hW) _)
        have hinv : M⁻¹ ≤ M₀⁻¹ := inv_anti₀ hM₀pos hM₀
        have hf : RootEndpointJetBounds n
            (n04PositiveSourceMap (⟨some m, ho⟩ : N04PositiveEndpointSource C i side) K z)
            (n04PositiveSourceHeight (⟨some m, ho⟩ : N04PositiveEndpointSource C i side) K z)
            (n04PositiveEndpoint i side) M₀⁻¹ M₀ M₀ := by
          change RootEndpointJetBounds n
            (canonicalCurrentPoint C K z (if side then (K.cutPair m).1 else (K.cutPair m).2))
            (n04CoordinatesCurrentHeightRatio C K z
              (if side then (K.cutPair m).1 else (K.cutPair m).2))
            (n04PositiveEndpoint i side) M₀⁻¹ M₀ M₀
          rw [ho]
          have h := hroots m (C.cell m) (hhost m) (hoptical m) (!side) z hz hs
          cases side <;> exact h
        exact {
          radial_lower := fun θ => hinv.trans (hf.radial_lower θ)
          angular_lower := fun θ => hinv.trans (hf.angular_lower θ)
          coordinate_jets := fun k hk hkn θ => (hf.coordinate_jets k hk hkn θ).trans hM₀
          height_value := fun θ => (hf.height_value θ).trans hM₀
          height_inverse := fun θ => (hf.height_inverse θ).trans hM₀
          height_jets := fun k hk hkn θ => (hf.height_jets k hk hkn θ).trans hM₀ }
  exact {
    angular_lower := fun side θ => (hsource side (src side)).angular_lower θ
    radial_lower := fun side θ => (hsource side (src side)).radial_lower θ
    coordinate_jets := fun side k hk hkn θ =>
      (hsource side (src side)).coordinate_jets k hk hkn θ
    height_value := fun side θ => (hsource side (src side)).height_value θ
    height_inverse := fun side θ => (hsource side (src side)).height_inverse θ
    height_jets := fun side k hk hkn θ =>
      (hsource side (src side)).height_jets k hk hkn θ }

end ContinuousFlexibility.Analysis
