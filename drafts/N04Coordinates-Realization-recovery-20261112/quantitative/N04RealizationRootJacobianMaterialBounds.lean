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

private theorem rootJacobian_inverse_le_of_odd_inverse
    {χ a M : ℝ} (hχ : 0 < χ) (ha : (1 / 4 : ℝ) ≤ a)
    (hM : 1 ≤ M) (hinverse : χ⁻¹ ≤ M) :
    (((3 / 2 : ℝ) * χ) ^ (2 / 3 : ℝ) * a)⁻¹ ≤ 4 * M := by
  have hc : 0 < (3 / 2 : ℝ) * χ := mul_pos (by norm_num) hχ
  have hcinv : ((3 / 2 : ℝ) * χ)⁻¹ ≤ M :=
    (inv_anti₀ hχ (by nlinarith only [hχ])).trans hinverse
  have hr : (((3 / 2 : ℝ) * χ) ^ (2 / 3 : ℝ))⁻¹ ≤ M := by
    rw [← Real.inv_rpow hc.le]
    exact (Real.rpow_le_rpow (inv_nonneg.mpr hc.le) hcinv
      (by norm_num : (0 : ℝ) ≤ 2 / 3)).trans
      (Real.rpow_le_self_of_one_le hM (by norm_num : (2 / 3 : ℝ) ≤ 1))
  have hai : a⁻¹ ≤ 4 := by
    have hh := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) ha
    norm_num at hh
    exact hh
  rw [mul_inv_rev]
  exact mul_le_mul hai hr
    (inv_nonneg.mpr (Real.rpow_nonneg hc.le _)) (by norm_num)

private theorem rootUnit_jacobian_cost
    {d c : PolarPoint → ℝ} {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    {l : ℝ → ℝ} {θ M : ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ x, Function.Periodic (fun η => d (x, η)) Real.pi)
    (hcperiod : ∀ x, Function.Periodic (fun η => c (x, η)) Real.pi)
    (hΘ : N04FlowEquations (rootRegularizedField d c) Θ)
    (hl : ContDiff ℝ ∞ l) (hlperiod : ∀ η, l (η + Real.pi) = l η + Real.pi)
    (hlower : (1 / 4 : ℝ) ≤ deriv l θ) (hM : 1 ≤ M)
    (hχ : 0 < extendedRootOddCoefficient (rootInverseCoordinate Θ l) (0, θ))
    (hinverse : (extendedRootOddCoefficient (rootInverseCoordinate Θ l) (0, θ))⁻¹ ≤ M) :
    let G : ℝ × ℝ × ℝ → ℝ := rootInverseCoordinate Θ l
    ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) (0, θ) ∧
      0 < planeJacobian (extendedRootEvenOddChart G) (0, θ) ∧
      (planeJacobian (extendedRootEvenOddChart G) (0, θ))⁻¹ ≤ 4 * M := by
  let G : ℝ × ℝ × ℝ → ℝ := rootInverseCoordinate Θ l
  have hfield := contDiff_rootRegularizedField hd hc
  have hperiod := rootRegularizedField_periodic hdperiod hcperiod
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hEndpoint : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => Θ q.1 1 q.2) :=
    n04Flow_contDiff_slice hfield hperiod hΘ ht
  have hpositive : ∀ p η, 0 < deriv (fun ζ => Θ p 1 ζ) η :=
    fun p η => n04Flow_angular_deriv_pos hfield hperiod hΘ ht p η
  have hEndpointPeriod : ∀ p η, Θ p 1 (η + Real.pi) = Θ p 1 η + Real.pi :=
    fun p η => n04Flow_period_add hfield hperiod hΘ p η ht
  have hG : ContDiff ℝ ∞ G :=
    contDiff_rootInverseCoordinate Real.pi_ne_zero hEndpoint hpositive hEndpointPeriod hl
  have hGperiod : ∀ x ζ η, G (x, ζ, η + Real.pi) = G (x, ζ, η) + Real.pi :=
    rootInverseCoordinate_period_add Real.pi_ne_zero hEndpoint hpositive hEndpointPeriod hlperiod
  have hχperiod : ∀ r, 0 ≤ r →
      Function.Periodic (fun η => rootOddCoefficient G (r, η)) Real.pi :=
    fun r _ => rootOddCoefficient_periodic hGperiod r
  have hφperiod : ∀ r, 0 ≤ r → ∀ η,
      rootEven G (r, η + Real.pi) = rootEven G (r, η) + Real.pi :=
    fun r _ => rootEven_period_add hGperiod r
  have hzero : ∀ η, G (0, 0, η) = l η :=
    rootInverseCoordinate_zero Real.pi_ne_zero hΘ.1 hΘ.2 hEndpoint hEndpointPeriod
  have hχraw : 0 < rootOddCoefficient G (0, θ) := by
    simpa only [extendedRootOddCoefficient_of_nonneg G le_rfl] using hχ
  have hJ : planeJacobian (extendedRootEvenOddChart G) (0, θ) =
      ((3 / 2 : ℝ) * extendedRootOddCoefficient G (0, θ)) ^ (2 / 3 : ℝ) *
        deriv l θ := by
    rw [planeJacobian_extendedRootEvenOddChart_zero hG Real.pi_ne_zero
      hχperiod hφperiod hzero (hl.differentiable (by simp) θ).hasDerivAt hχraw.ne']
    simp only [rootRadialFactor, extendedRootOddCoefficient_of_nonneg G le_rfl]
  refine ⟨contDiffAt_extendedRootEvenOddChart_of_ne_zero hG Real.pi_ne_zero
    hχperiod hφperiod hχ.ne', ?_, ?_⟩
  · rw [hJ]
    exact mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hχ) _)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hlower)
  · rw [hJ]
    exact rootJacobian_inverse_le_of_odd_inverse hχ hlower hM hinverse

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
  have hunit := rootUnit_jacobian_cost hregular.1 hregular.2 hperiod.1 hperiod.2
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
