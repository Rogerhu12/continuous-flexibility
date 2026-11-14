import ContinuousFlexibility.Analysis.N04RealizationRootJacobianKernel
import ContinuousFlexibility.Analysis.N01RootOddCoefficientMaterialValues
import ContinuousFlexibility.Analysis.N03ControlledRootUnitIdentification
import ContinuousFlexibility.Analysis.RootAffineOrdinaryJets
import ContinuousFlexibility.Analysis.RootChartExtensionGeometry
import ContinuousFlexibility.Analysis.N04FlowJetsProof

/-!
# A sample material cost for the same actual root Jacobian

The unit odd coefficient already has a controlled reciprocal. Its
two-thirds power and the actual angular label lower bound therefore
control the reciprocal determinant. The original controlled flow and
the original stored atlas are identified before removing the inward
orientation. Neither a chosen collar width nor an arbitrary component
constant is assigned a material cost.

This draft depends on the source-owned material value and unit
identification leaves listed in the accompanying dependency manifest.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- The same actual chart has one reciprocal-Jacobian material cost,
uniform over states, components, endpoint signs, angles, and any supplied
actual containing cell with the displayed optical lower condition. -/
def N04RealizationRootJacobianMaterialBound
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base : ℕ) (ε K₀ C0 B : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
    (∀ x ∈ Ioo (C.left m) (C.right m),
      K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) * min (x - C.left m) (C.right m - x) ≤
        -deriv D.w x / (x * D.w x)) →
    ∀ side : Bool, ∀ θ : ℝ,
      let r : ℝ := n01ComponentRoot C m side
      let i : ℕ := if side then (K.cutPair m).2 else (K.cutPair m).1
      (r, θ) ∈ physicalPieceClosed S K z i ∧
        |planeJacobian (K.chart z i) (r, θ)|⁻¹ ≤
          B * (C0 * T.E0 (T.sample j)) ^ B

theorem n04Realization_rootJacobian_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε K₀ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hK : 0 < K₀) :
    ∃ C0 B : ℝ, ∃ newBase : ℕ, ∃ η : ℝ,
      1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧ 1 ≤ B ∧
      base ≤ newBase ∧ 0 < η ∧ η ≤ ε ∧
      N04RealizationRootJacobianMaterialBound D T S C K newBase η K₀ C0 B := by
  obtain ⟨rootBase, flowLoss, ρ, hb, hρ, hρε, hflow, hinputs⟩ :=
    n01_exists_common_root_inputs n04FlowJetsTarget_proof hS hT hN.1.1
  have hsub := stateNeighborhood_mono S C hb hρε
  have hN' := nonlinearPropertiesThrough03_restrict hT hN hb le_rfl hρ hρε
  have hA' := n04PartA_restrict hA hb hρε
  have hB' := n04PartB_restrict hB hb hρε
  have hfield' : N04bFieldRegularity D S C L rootBase ρ :=
    { smooth_coefficients := fun z hz => hfield.smooth_coefficients z (hsub hz)
      periodic_coefficients := fun z hz => hfield.periodic_coefficients z (hsub hz)
      positive_a := fun z hz => hfield.positive_a z (hsub hz)
      reference_flow := hfield.reference_flow
      negative_discriminant := fun z hz => hfield.negative_discriminant z (hsub hz) }
  obtain ⟨C0, low, P, hC0, hfloor, hP, hvalues⟩ :=
    n01_rootOddCoefficient_unit_material_values_of_component_optical
      hS hT hN'.1.1 hflow hK
  let η : ℝ := min ρ (1 / 2)
  have hη : 0 < η := lt_min hρ (by norm_num)
  have hηρ : η ≤ ρ := min_le_left _ _
  refine ⟨C0, 4 * P, max rootBase low, η, hC0, hfloor,
    by linarith only [hP], hb.trans (le_max_left _ _), hη, hηρ.trans hρε, ?_⟩
  intro z hz hs m j hhost hoptical side θ
  have hzroot : z ∈ stateNeighborhood S C rootBase ρ :=
    stateNeighborhood_mono S C (le_max_left _ _) hηρ hz
  have hzlow : z ∈ stateNeighborhood S C low η :=
    stateNeighborhood_mono S C (le_max_right _ _) le_rfl hz
  have hlow : pairGrading (stateGrading S) realGrading low
      (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hzlow).trans (by
      have hηhalf : η ≤ 1 / 2 := min_le_right _ _
      linarith only [hηhalf])
  obtain ⟨g, R, hR, κ, hg, _, hκ, hfactor, hgeometry, hflows⟩ := hinputs m side
  obtain ⟨δ, A, hδ, _, _, hApos, hfamily⟩ := hflows 1 zero_lt_one
  have hstrip := (hgeometry.1 z hzroot hs).1
  obtain ⟨Θ, hΘ, hident⟩ := n03_controlledRootInput_unit_identification
    hS hT hN' hfield' hA' hB' hzroot hs m side hg hR hκ hδ hApos hstrip
    (hfamily z hzroot hs)
  let r : ℝ := n01ComponentRoot C m side
  let σ : ℝ := n01ComponentRootOrientation side
  let i : ℕ := if side then (K.cutPair m).2 else (K.cutPair m).1
  let d : PolarPoint → ℝ := localizedRootDrift D S C r σ hR z
  let c : PolarPoint → ℝ := localizedRootSpeed D S C g r σ hR z
  let Θ₁ : (ℝ × ℝ) → ℝ → ℝ → ℝ := rootFlowParameterUnscale Θ δ
  let l : ℝ → ℝ := n01RootLabel S C z m side
  let G : ℝ × ℝ × ℝ → ℝ := rootInverseCoordinate Θ₁ l
  let W : ℝ := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hfloor j
  have hM : 1 ≤ P * W ^ P := one_le_mul_of_one_le_of_one_le hP
    (Real.one_le_rpow hW (zero_le_one.trans hP))
  have hvalue := hvalues z hzroot hs hlow m j hhost hoptical side g hg hfactor
    R hR hstrip δ hδ.ne' Θ hΘ θ
  have hΘ₁ : N04FlowEquations (rootRegularizedField d c) Θ₁ :=
    rootFlowParameterUnscale_equations hδ.ne' hΘ
  have hregular := (hgeometry.1 z hzroot hs).2
  have hperiod := hgeometry.2 z
  have hunit := n04Realization_rootUnit_jacobian_cost hregular.1 hregular.2 hperiod.1 hperiod.2
    hΘ₁ (n01RootLabel_contDiff hS hT hN'.1.1 hzroot hs m side)
    (n01RootLabel_period_add hN'.1.1 hzroot hs m side)
    (n01RootLabel_deriv_mem_quarter_four hN'.1.1 hflow hzroot hs m side θ).1
    hM hvalue.1 hvalue.2.2
  obtain ⟨hclosed, hFregular, _, _, hFjet, _⟩ := hident θ
  have hD : fderiv ℝ (fun p => K.chart z i (rootProfileShift r σ p)) (0, θ) =
      fderiv ℝ (extendedRootEvenOddChart G) (0, θ) :=
    root_fderiv_eq_of_firstJet_eq hFregular hunit.1 (hFjet 1)
  have hJ : planeJacobian (extendedRootEvenOddChart G) (0, θ) =
      planeJacobian (fun p => K.chart z i (rootProfileShift r σ p)) (0, θ) := by
    unfold planeJacobian
    rw [hD]
  have hσ : σ = 1 ∨ σ = -1 := n01ComponentRootOrientation_eq side
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσne : σ ≠ 0 := by
    rcases hσ with h | h <;> rw [h] <;> norm_num
  have hpoint : rootProfileShift r σ (0, θ) = (r, θ) := by
    simp only [rootProfileShift, mul_zero, add_zero]
  have hF : DifferentiableAt ℝ (K.chart z i) (rootProfileShift r σ (0, θ)) := by
    simpa only [hpoint] using
      (((hA'.boundary z hzroot hs i).2.2.2.2.1 (r, θ) hclosed).1.differentiableAt (by simp))
  have hJlower : planeJacobian (extendedRootEvenOddChart G) (0, θ) ≤
      |planeJacobian (K.chart z i) (r, θ)| := by
    simpa only [hσabs, div_one, hpoint] using
      planeJacobian_unscale_rootProfile_lower r σ hσne hF (le_of_eq hJ)
  refine ⟨hclosed, (inv_anti₀ hunit.2.1 hJlower).trans (hunit.2.2.trans ?_)⟩
  calc
    4 * (P * W ^ P) = (4 * P) * W ^ P := by ring
    _ ≤ (4 * P) * W ^ (4 * P) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hW (by linarith only [hP]))
        (by linarith only [hP])

end ContinuousFlexibility.Analysis
