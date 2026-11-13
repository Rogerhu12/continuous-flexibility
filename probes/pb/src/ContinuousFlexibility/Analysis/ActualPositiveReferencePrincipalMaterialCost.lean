import ContinuousFlexibility.Analysis.RetainedPositiveComponentProfileLower
import ContinuousFlexibility.Analysis.ActualPositiveReferenceAllOrderMaterialJets
import ContinuousFlexibility.Analysis.PositiveReferencePrescribedCosts
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Physical principal costs for the same displayed reference interpolation

The finite certificate is exactly the one retained by the actual all-order
producer. Its C0 and B are inputs here, so neither the Taylor width nor the
coordinate and height are chosen again. The true retained profile lower
bound is evaluated at the same physical midpoint sample. The envelope is
already normalized before the family is constructed; only then is the
independent coefficient/exponent cost packed into one constant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04Coordinates_retained_positive_reference_principal_material_cost
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
    (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
    (hfield : N04bFieldRegularity Γ.reference S C L base ε)
    (e : ℕ ≃ N04PieceIndex Γ.reference) (n : ℕ)
    {C0 B : ℝ} (hC0 : 1 ≤ C0) (hB : 1 ≤ B)
    (hE0 : ∀ j, 1 ≤ T.E0 (T.sample j))
    (hfinite : ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
        ∀ src : (side : Bool) → N04PositiveEndpointSource C i side,
          let A := n04bActualTypedAtlas hT hS hN hfield e
          let U := B * (C0 * T.E0 (T.sample j)) ^ B
          1 ≤ U ∧ (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ U ∧
            n04PositiveRight i - n04PositiveLeft i ≤ U ∧
            ∀ side : Bool,
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
                (n04PositiveEndpoint i side) 1 0 ∧
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
                (n04PositiveEndpoint i side) 0 0 ∧
              (∀ k : ℕ, 1 ≤ k → k ≤ n + 1 →
                |radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) ∧
              ∀ k : ℕ, k ≤ n + 1 →
                |radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
      ∀ src : (side : Bool) → N04PositiveEndpointSource C i side,
        let A := n04bActualTypedAtlas hT hS hN hfield e
        let U := B * (C0 * T.E0 (T.sample j)) ^ B
        let δ := positiveReferenceTaylorWidth n
          (n04PositiveLeft i) (n04PositiveRight i) U⁻¹ U
        let ys := fun side : Bool => radialEndpointTaylorSlice (n + 1)
          (n04PositiveEndpoint i side) (n04PositiveReferenceSourceCoordinate (src side) A)
        let hs := fun side : Bool => radialEndpointTaylorSlice (n + 1)
          (n04PositiveEndpoint i side) (n04PositiveReferenceSourceHeight (src side) A)
        let Y := positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i) δ
          (deriv (ys false)) (deriv (ys true))
        let H := positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i) δ
          (hs false) (hs true)
        PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
          (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
          (n04PositiveLeft i) (n04PositiveRight i) 0 1 ∧
        ∃ h k M : ℝ, 0 < h ∧ 0 < k ∧ 0 < M ∧
          (∀ x ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i),
            h ≤ H x ∧ deriv Y x ≤ M ∧
              k * min (x - n04PositiveLeft i) (n04PositiveRight i - x) ≤
                deriv Γ.reference.w x / x) ∧
          M ^ 2 ≤ (K * T.E0 (T.sample j) ^ K) * (h ^ 2 * k) := by
  obtain ⟨P0, A0, hP0, hA0, hprofile⟩ :=
    retainedReference_positive_component_profile_material_lower
      P hSelected hband hq hΓ hw hcoordinates hN.1.1.2.2.2.1 hT
  let d : ℝ := ((n + 2 : ℕ) : ℝ)
  let coefficient : ℝ := 16 * d ^ 2 * B ^ 6 * P0 * C0 ^ (6 * B)
  let exponent : ℝ := 6 * B + A0
  obtain ⟨K, hK, hpack⟩ := coefficientEnvelope_pack coefficient exponent
  refine ⟨K, hK, ?_⟩
  intro i j hmid src
  let A := n04bActualTypedAtlas hT hS hN hfield e
  let E : ℝ := T.E0 (T.sample j)
  let U : ℝ := B * (C0 * E) ^ B
  let a : Bool → ℝ := fun side => n04PositiveSourceLeft (src side)
  let b : Bool → ℝ := fun side => n04PositiveSourceRight (src side)
  let y : Bool → PolarPoint → ℝ :=
    fun side => n04PositiveReferenceSourceCoordinate (src side) A
  let hsource : Bool → PolarPoint → ℝ :=
    fun side => n04PositiveReferenceSourceHeight (src side) A
  let δ := positiveReferenceTaylorWidth n (n04PositiveLeft i) (n04PositiveRight i) U⁻¹ U
  let ys : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (n04PositiveEndpoint i side) (y side)
  let hs : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (n04PositiveEndpoint i side) (hsource side)
  let Y := positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i) δ
    (deriv (ys false)) (deriv (ys true))
  let H := positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i) δ
    (hs false) (hs true)
  have hinput := hfinite i j hmid src
  have hU : 1 ≤ U := hinput.1
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hE : 0 < E := zero_lt_one.trans_le (hE0 j)
  have hC0pos : 0 < C0 := zero_lt_one.trans_le hC0
  have hD := n04b_profileGeometry_of_through03 hN
  have hf : Continuous (deriv Γ.reference.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hlr : n04PositiveLeft i < n04PositiveRight i :=
    (n04PositiveComponent_bounds hf i).2.1
  have hd (side : Bool) :=
    n04Coordinates_actual_positive_reference_source_data hT hS hN hfield e (src side)
  have hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1 :=
    (positiveReferenceFiniteRadialJets_prescribed n
      (κ := U⁻¹) (M := U) (a := a) (b := b) (y := y) (h := hsource)
      hlr (inv_pos.mpr hUpos) hUpos.le
      (fun side => (hd side).1) (fun side => (hd side).2.1)
      (fun side => (hd side).2.2.1) (fun side => (hd side).2.2.2.1)
      (fun side => (hd side).2.2.2.2.1) (fun side => (hd side).2.2.2.2.2.1)
      (fun side x hx θ => (hd side).2.2.2.2.2.2.1 x hx θ)
      (fun side x hx θ => (hd side).2.2.2.2.2.2.2.1 x hx θ)
      (fun side => (hd side).2.2.2.2.2.2.2.2.1)
      (fun side => (hinput.2.2.2 side).1) (fun side => (hinput.2.2.2 side).2.1)
      (fun side => (hinput.2.2.2 side).2.2.1)
      (fun side => (hinput.2.2.2 side).2.2.2)).1
  have hcosts := positiveReferenceFiniteRadialJets_prescribed_costs n
    (κ := U⁻¹) (M := U) (U := U) (a := a) (b := b) (y := y) (h := hsource)
    hlr (inv_pos.mpr hUpos) hUpos.le hU le_rfl (inv_inv U).le
    hinput.2.1 hinput.2.2.1
    (fun side => (hd side).1) (fun side => (hd side).2.1)
    (fun side => (hd side).2.2.1) (fun side => (hd side).2.2.2.1)
    (fun side => (hd side).2.2.2.2.1) (fun side => (hd side).2.2.2.2.2.1)
    (fun side x hx θ => (hd side).2.2.2.2.2.2.1 x hx θ)
    (fun side x hx θ => (hd side).2.2.2.2.2.2.2.1 x hx θ)
    (fun side => (hd side).2.2.2.2.2.2.2.2.1)
    (fun side => (hinput.2.2.2 side).1) (fun side => (hinput.2.2.2 side).2.1)
    (fun side => (hinput.2.2.2 side).2.2.1)
    (fun side => (hinput.2.2.2 side).2.2.2)
  let h : ℝ := (4 * U ^ 2)⁻¹
  let k : ℝ := (P0 * E ^ A0)⁻¹
  let M : ℝ := d * U
  have hh : 0 < h := inv_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos hUpos))
  have hk : 0 < k := inv_pos.mpr (mul_pos hP0 (Real.rpow_pos_of_pos hE _))
  have hdpos : 0 < d := by dsimp only [d]; positivity
  have hM : 0 < M := mul_pos hdpos hUpos
  have hlow (x : ℝ) : h ≤ H x := by
    have hx := hcosts.2.2.2 x
    have hHx : 0 < H x := hx.2.2.2.1
    have hinv := inv_anti₀ (inv_pos.mpr hHx) hx.2.2.2.2.2
    rw [inv_inv] at hinv
    exact hinv
  have hU6 : U ^ 6 = B ^ 6 * C0 ^ (6 * B) * E ^ (6 * B) := by
    dsimp only [U]
    rw [mul_pow, ← Real.rpow_mul_natCast (mul_pos hC0pos hE).le B 6,
      show B * ((6 : ℕ) : ℝ) = 6 * B by push_cast; ring, Real.mul_rpow hC0pos.le hE.le]
    ring
  have hweight : 16 * d ^ 2 * U ^ 6 * P0 * E ^ A0 ≤ K * E ^ K := by
    calc
      _ = coefficient * E ^ exponent := by
        rw [hU6]
        dsimp only [coefficient, exponent]
        rw [Real.rpow_add hE]
        ring
      _ ≤ K * E ^ K := hpack E (hE0 j)
  have hratio : M ^ 2 / (h ^ 2 * k) = 16 * d ^ 2 * U ^ 6 * P0 * E ^ A0 := by
    dsimp only [M, h, k]
    field_simp [hUpos.ne', hP0.ne', (Real.rpow_pos_of_pos hE A0).ne']
    <;> ring
  change PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
    (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
    (n04PositiveLeft i) (n04PositiveRight i) 0 1 ∧
    ∃ h k M : ℝ, 0 < h ∧ 0 < k ∧ 0 < M ∧
      (∀ x ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i),
        h ≤ H x ∧ deriv Y x ≤ M ∧
          k * min (x - n04PositiveLeft i) (n04PositiveRight i - x) ≤
            deriv Γ.reference.w x / x) ∧
      M ^ 2 ≤ (K * E ^ K) * (h ^ 2 * k)
  refine ⟨hgeometry, h, k, M, hh, hk, hM, ?_, ?_⟩
  · intro x hx
    exact ⟨hlow x, (hcosts.2.2.2 x).2.1,
      hprofile i j hmid x ⟨hx.1.le, hx.2.le⟩⟩
  · exact (div_le_iff₀ (mul_pos (sq_pos_of_pos hh) hk)).mp (hratio.trans_le hweight)

end ContinuousFlexibility.Analysis
