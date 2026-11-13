import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootEndpoints
import ContinuousFlexibility.Analysis.N04RealizationLeadAssembly
import ContinuousFlexibility.Analysis.N04bActualAtlasInteriorCompletion
import ContinuousFlexibility.Analysis.CanonicalPositiveSourceInteriorDivision
import ContinuousFlexibility.Analysis.CanonicalWholePositiveTransport
import ContinuousFlexibility.Analysis.RetainedPositiveEndpointHostSample
import ContinuousFlexibility.Analysis.RetainedPositiveComponentInteriorEndpoints

/-!
# Actual positive endpoint inputs at their own midpoint samples

The genuine source at either end is the opposite root of its adjacent
negative component. The retained geometry compares that component's
original host sample with the positive midpoint sample. Thus one smaller
neighborhood and one material power provide all finite interpolation
inputs of the original atlas, uniformly over every positive component.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The true current source maps and height ratios have a common finite
sample envelope. Its reciprocal is a valid lower bound for both positive
diagonal entries. The parameter spaces and actual typed atlas are retained. -/
theorem n04PositiveGeometry_actual_positive_endpoint_material_bounds
    (W : N04RealizationStart) (X : N04RealizationChoice W) (n : ℕ) :
    ∃ newBase : ℕ, ∃ ε' B : ℝ,
      W.base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ W.ε ∧ 1 ≤ B ∧
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
        let M := B * W.U.E0 (W.U.sample (X.cell i)) ^ B
        1 ≤ M ∧
        ∀ z ∈ stateNeighborhood W.S W.C newBase ε', stateSector W.S z.1 →
          WholePositiveEndpointJetBounds n
            (fun side => n04PositiveSourceMap (X.src i side) (W.A X.e₀) z)
            (fun side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z)
            (n04PositiveLeft i) (n04PositiveRight i) M⁻¹ M⁻¹ M M := by
  let K := W.A X.e₀
  have hA := n04bWithInteriorDivision_partA
    (n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field X.e₀)
  have hB := n04bActualTypedAtlas_interiorCompletion_partB
    W.hT W.hS W.through03 W.field X.e₀
  have hroot := n04PositiveGeometry_actual_root_endpoint_material_bounds
    W.hS W.hT W.through03 W.field hA hB X.κ_pos n
  let C0 := hroot.choose
  let newBase := hroot.choose_spec.choose
  let ε' := hroot.choose_spec.choose_spec.choose
  let B₀ := hroot.choose_spec.choose_spec.choose_spec.choose
  have hdata := hroot.choose_spec.choose_spec.choose_spec.choose_spec
  have hC0 := hdata.1
  have hb := hdata.2.2.1
  have hε' := hdata.2.2.2.1
  have hε'ε := hdata.2.2.2.2.1
  have hB₀ := hdata.2.2.2.2.2.1
  have hrootBounds := hdata.2.2.2.2.2.2
  obtain ⟨K₁, A₁, hK₁, hA₁, hsample⟩ :=
    retainedReference_positive_endpoint_host_sample_bound W.P W.metadata.selected
      W.metadata.first_two one_pos W.realizes W.hw W.coordinates
      W.through03.1.1.2.2.2.1 W.hT (zero_le_one.trans hB₀)
  let D : ℝ := B₀ * C0 ^ B₀ * K₁
  have hD : 0 < D := mul_pos
    (mul_pos (zero_lt_one.trans_le hB₀)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hC0) _)) hK₁
  obtain ⟨B₁, hB₁, hpack⟩ := coefficientEnvelope_pack D A₁
  let B : ℝ := max 1 B₁
  have hBone : 1 ≤ B := le_max_left _ _
  have hB₁B : B₁ ≤ B := le_max_right _ _
  refine ⟨newBase, ε', B, hb, hε', hε'ε, hBone, ?_⟩
  intro i
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  let M : ℝ := B * E ^ B
  have hEU : W.T.E0 (W.T.sample (X.cell i)) ≤ E := le_enlargedMaterialData_E0 W.T _
  have hE : 1 ≤ E := (W.floor _).trans hEU
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hBone
    (Real.one_le_rpow hE (zero_le_one.trans hBone))
  refine ⟨hM, ?_⟩
  intro z hz hs
  have hsides (side : Bool) : RootEndpointJetBounds n
      (n04PositiveSourceMap (X.src i side) K z)
      (n04PositiveSourceHeight (X.src i side) K z)
      (n04PositiveEndpoint i side) M⁻¹ M M := by
    obtain ⟨m, hm⟩ : ∃ m, (X.src i side).val = some m := by
      cases ho : (X.src i side).val with
      | none =>
          have hamb : n04PositiveEndpoint i side =
              (if side then W.D.b else W.D.a) := by
            simpa only [ho] using (X.src i side).property
          have hc := (retainedReference_positive_endpoints_interior
            W.P W.metadata.selected W.metadata.first_two one_pos W.realizes W.hw W.coordinates i side).1
          exfalso
          cases side
          · exact (ne_of_gt hc.1) (by simpa only [Bool.false_eq_true, ↓reduceIte] using hamb)
          · exact (ne_of_lt hc.2) (by simpa only [↓reduceIte] using hamb)
      | some m => exact ⟨m, rfl⟩
    have hend : n04PositiveEndpoint i side =
        (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    have hsampleBound := hsample i side m (W.C.cell m) (X.cell i)
      (W.host m) hend (X.cell_mem i)
    let M₀ : ℝ := B₀ * (C0 * W.T.E0 (W.T.sample (W.C.cell m))) ^ B₀
    have hEm : 0 ≤ W.T.E0 (W.T.sample (W.C.cell m)) := zero_le_one.trans (W.floor _)
    have hcost : M₀ ≤ M := by
      calc
        M₀ = (B₀ * C0 ^ B₀) * W.T.E0 (W.T.sample (W.C.cell m)) ^ B₀ := by
          dsimp only [M₀]
          rw [Real.mul_rpow (zero_le_one.trans hC0) hEm]
          ring
        _ ≤ (B₀ * C0 ^ B₀) * (K₁ * W.T.E0 (W.T.sample (X.cell i)) ^ A₁) :=
          mul_le_mul_of_nonneg_left hsampleBound
            (mul_nonneg (zero_le_one.trans hB₀) (Real.rpow_nonneg (zero_le_one.trans hC0) _))
        _ = D * W.T.E0 (W.T.sample (X.cell i)) ^ A₁ := by dsimp only [D]; ring
        _ ≤ D * E ^ A₁ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (zero_le_one.trans (W.floor _)) hEU hA₁) hD.le
        _ ≤ B₁ * E ^ B₁ := hpack E hE
        _ ≤ M := mul_le_mul hB₁B (Real.rpow_le_rpow_of_exponent_le hE hB₁B)
          (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hBone)
    have hactual := hrootBounds z hz hs m (W.C.cell m) (W.host m) (X.optical m) (!side)
    have hraw : RootEndpointJetBounds n
        (n04PositiveSourceMap (X.src i side) K z)
        (n04PositiveSourceHeight (X.src i side) K z)
        (n04PositiveEndpoint i side) M₀⁻¹ M₀ M₀ := by
      have hr : (if !side then W.C.right m else W.C.left m) = n04PositiveEndpoint i side := by
        cases side <;> exact hend.symm
      have he := congrArg (fun t : ℝ => RootEndpointJetBounds n
        (n04PositiveSourceMap (X.src i side) K z)
        (n04PositiveSourceHeight (X.src i side) K z) t M₀⁻¹ M₀ M₀) hr
      apply he.mp
      cases side <;>
        simpa only [n04PositiveSourceMap, n04PositiveSourceHeight, hm,
          n01ComponentRoot, n04bWithInteriorDivision, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte] using hactual.2
    exact hraw.mono (inv_anti₀ (zero_lt_one.trans_le hactual.1) hcost) hcost hcost
  exact
    { angular_lower := fun side θ => (hsides side).angular_lower θ
      radial_lower := fun side θ => (hsides side).radial_lower θ
      coordinate_jets := fun side k hk hkn θ => (hsides side).coordinate_jets k hk hkn θ
      height_value := fun side θ => (hsides side).height_value θ
      height_inverse := fun side θ => (hsides side).height_inverse θ
      height_jets := fun side k hk hkn θ => (hsides side).height_jets k hk hkn θ }

end ContinuousFlexibility.Analysis
