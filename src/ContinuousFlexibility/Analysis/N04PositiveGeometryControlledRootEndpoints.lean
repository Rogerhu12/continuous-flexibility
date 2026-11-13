import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRelativeFields

/-!
# Actual finite relative endpoint bounds at the original host sample

This is the quantitative version of the existing qualitative finite root
factory. Its one numerical envelope controls the true current transport,
the true height ratio and both reciprocal positive diagonal bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem RootEndpointJetBounds.mono
    {n : ℕ} {F : PolarPoint → PolarPoint} {q : PolarPoint → ℝ}
    {r κ κ' M M' H H' : ℝ} (h : RootEndpointJetBounds n F q r κ M H)
    (hκ : κ' ≤ κ) (hM : M ≤ M') (hH : H ≤ H') :
    RootEndpointJetBounds n F q r κ' M' H' :=
  { radial_lower := fun θ => hκ.trans (h.radial_lower θ)
    angular_lower := fun θ => hκ.trans (h.angular_lower θ)
    coordinate_jets := fun k hk hkn θ => (h.coordinate_jets k hk hkn θ).trans hM
    height_value := fun θ => (h.height_value θ).trans hH
    height_inverse := fun θ => (h.height_inverse θ).trans hH
    height_jets := fun k hk hkn θ => (h.height_jets k hk hkn θ).trans hH }

/-- The finite numerical constant precedes every state, component, host
and orientation, with the same original atlas and state space. -/
theorem n04PositiveGeometry_actual_root_endpoint_material_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε K₀ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hK : 0 < K₀) (n : ℕ) :
    ∃ C0 : ℝ, ∃ newBase : ℕ, ∃ ε' B : ℝ,
      1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧ 1 ≤ B ∧
      ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ side : Bool,
        let r := n01ComponentRoot C m side
        let i := if side then (K.cutPair m).2 else (K.cutPair m).1
        let M := B * (C0 * T.E0 (T.sample j)) ^ B
        1 ≤ M ∧ RootEndpointJetBounds n (canonicalCurrentPoint C K z i)
          (n04CoordinatesCurrentHeightRatio C K z i) r M⁻¹ M M := by
  have hraw := n04PositiveGeometry_actual_root_finite_material_fields
    hS hT hN hfield hA hB hK (n + 2)
  let C0 := hraw.choose
  let newBase := hraw.choose_spec.choose
  let ε' := hraw.choose_spec.choose_spec.choose
  let B₀ := hraw.choose_spec.choose_spec.choose_spec.choose
  have hdata := hraw.choose_spec.choose_spec.choose_spec.choose_spec
  have hC0 := hdata.1
  have hfloor := hdata.2.1
  have hb := hdata.2.2.1
  have hε' := hdata.2.2.2.1
  have hε'ε := hdata.2.2.2.2.1
  have hB₀ := hdata.2.2.2.2.2.1
  have hfields := hdata.2.2.2.2.2.2
  obtain ⟨A, hApoly, degree, hrelative⟩ :=
    n04PositiveGeometry_exists_actual_relative_root_polynomial n
  obtain ⟨B₁, hB₁, hpacked⟩ := n04PositiveGeometry_polynomial_sample_pack A B₀ degree
  let B : ℝ := max 1 B₁
  have hBone : 1 ≤ B := le_max_left _ _
  have hB₁B : B₁ ≤ B := le_max_right _ _
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have href' : (C.referenceState, 0) ∈ stateNeighborhood S C newBase ε' :=
    reference_mem_stateNeighborhood S C newBase hε'
  have hsref : stateSector S C.referenceState := hN.1.1.2.2.1.stateSector
  refine ⟨C0, newBase, ε', B, hC0, hfloor, hb, hε', hε'ε, hBone, ?_⟩
  intro z hz hs m j hhost hoptical side
  let W : ℝ := C0 * T.E0 (T.sample j)
  let M₀ : ℝ := B₀ * W ^ B₀
  let M₁ : ℝ := A * M₀ ^ degree
  let M : ℝ := B * W ^ B
  have hW : 1 ≤ W := hfloor j
  have hM₀ : 1 ≤ M₀ := one_le_mul_of_one_le_of_one_le hB₀
    (Real.one_le_rpow hW (zero_le_one.trans hB₀))
  have hM₁ : 1 ≤ M₁ := one_le_mul_of_one_le_of_one_le hApoly (one_le_pow₀ hM₀)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hBone
    (Real.one_le_rpow hW (zero_le_one.trans hBone))
  have hcost : M₁ ≤ M := (hpacked W hW).trans
    (mul_le_mul hB₁B (Real.rpow_le_rpow_of_exponent_le hW hB₁B)
      (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hBone))
  have hzold := stateNeighborhood_mono S C hb hε'ε hz
  have hroot := hrelative hA hB.1 href hsref z hzold hs m side M₀ hM₀
    (hfields (C.referenceState, 0) href' hsref m j hhost hoptical side)
    (hfields z hz hs m j hhost hoptical side)
  exact ⟨hM, hroot.mono (inv_anti₀ (zero_lt_one.trans_le hM₁) hcost) hcost hcost⟩

end ContinuousFlexibility.Analysis
