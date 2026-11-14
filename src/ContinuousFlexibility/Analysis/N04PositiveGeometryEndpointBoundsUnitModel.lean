module

public import ContinuousFlexibility.Analysis.N03ControlledRootUnitIdentification
public import ContinuousFlexibility.Analysis.N06RootBoundaryFiniteFormulas
public import ContinuousFlexibility.Analysis.RootCharacteristicReflection

/-!
# The boundary formulas of the same unit root model

The normalized flow already used to identify the stored atlas satisfies
the root-coordinate contract with its forward angular label. Thus the
eight finite formulas apply to that very unit model. Localization has no
effect on any of its raw coefficient traces at the axis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem rootFlow_coordinate_properties
    {d c : PolarPoint → ℝ} {β : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hdodd : ∀ r θ, d (r, -θ) = -d (r, θ))
    (hceven : ∀ r θ, c (r, -θ) = c (r, θ))
    (hcpos : ∀ θ, 0 < c (0, θ))
    (hβ : ContDiff ℝ ∞ β) (hβpos : ∀ θ, 0 < deriv β θ)
    (hβperiod : ∀ θ, β (θ + Real.pi) = β θ + Real.pi)
    (hβodd : ∀ θ, β (-θ) = -β θ)
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations (rootRegularizedField d c) Θ) :
    N04bRootCoordinateProperties d c β
      (fun θ x => Θ (x, x ^ (3 / 2 : ℝ)) 1 θ) 1 1 (rootInverseCoordinate Θ β) := by
  let G := rootInverseCoordinate Θ β
  have hfield := contDiff_rootRegularizedField hd hc
  have hperiod := rootRegularizedField_periodic hdperiod hcperiod
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hEndpoint : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) :=
    n04Flow_contDiff_slice hfield hperiod hΘ ht
  have hpositive : ∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ :=
    fun p θ => n04Flow_angular_deriv_pos hfield hperiod hΘ ht p θ
  have hEndpointPeriod : ∀ p θ, Θ p 1 (θ + Real.pi) = Θ p 1 θ + Real.pi :=
    fun p θ => n04Flow_period_add hfield hperiod hΘ p θ ht
  have hodd (θ : ℝ) : rootOddCoefficient G (0, θ) =
      (2 / 3 : ℝ) * c (0, θ) * deriv β θ :=
    rootOddCoefficient_rootInverseCoordinate_zero Real.pi_ne_zero hc hΘ.1 hΘ.2
      (n04Flow_joint_continuousOn hfield hperiod hΘ)
      hEndpoint hpositive hEndpointPeriod hβ θ
  refine {
    label_smooth := hβ
    label_positive := hβpos
    label_period := hβperiod
    label_odd := hβodd
    smooth := contDiff_rootInverseCoordinate Real.pi_ne_zero
      hEndpoint hpositive hEndpointPeriod hβ
    zero_section := rootInverseCoordinate_zero Real.pi_ne_zero hΘ.1 hΘ.2
      hEndpoint hEndpointPeriod
    period := rootInverseCoordinate_period_add Real.pi_ne_zero
      hEndpoint hpositive hEndpointPeriod hβperiod
    reflection := rootInverseCoordinate_reflect_of_rootFlow Real.pi_ne_zero hd hc
      hdperiod hcperiod hdodd hceven hΘ.1 hΘ.2 hEndpoint hpositive hEndpointPeriod hβodd
    odd_zero := hodd
    odd_positive := fun θ => (hodd θ).symm ▸
      mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2 / 3) (hcpos θ)) (hβpos θ)
    stored_footpoint := ?_
    reflected_footpoint := ?_
    angular_positive := fun s x θ hx =>
      rootInverseCoordinate_characteristic_angularPartial_pos Real.pi_ne_zero
        hEndpoint hpositive hEndpointPeriod hβ hβpos s hx θ
    transport := fun s x θ hx =>
      rootInverseCoordinate_characteristic_transport Real.pi_ne_zero hd hc
        hdperiod hcperiod hΘ.1 hΘ.2 hEndpoint hpositive hEndpointPeriod hβ s hx θ }
  · intro x _ θ
    change β (invFun (fun η => Θ (x, x ^ (3 / 2 : ℝ)) 1 η) θ) =
      β (invFun (fun η => Θ (x, 1 * x ^ (3 / 2 : ℝ)) 1 η) θ)
    rw [one_mul]
  · intro x _ θ
    have he (η : ℝ) : -Θ (x, x ^ (3 / 2 : ℝ)) 1 (-η) =
        Θ (x, -(x ^ (3 / 2 : ℝ))) 1 η := by
      have h := rootRegularizedFlow_reflect Real.pi_ne_zero hd hc hdperiod hcperiod
        hdodd hceven hΘ.1 hΘ.2 x (x ^ (3 / 2 : ℝ)) (-η) ht
      simpa only [neg_neg] using h.symm
    change β (invFun (fun η => -Θ (x, x ^ (3 / 2 : ℝ)) 1 (-η)) θ) =
      β (invFun (fun η => Θ (x, (-1) * x ^ (3 / 2 : ℝ)) 1 η) θ)
    simp only [he, neg_one_mul]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n04PositiveGeometry_actual_unitRootCoordinate_properties
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) {R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m side)
      (n01ComponentRootOrientation side) R)
    {δ : ℝ} (hδ : δ ≠ 0) (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hΘ : N04FlowEquations (rootRescaledField
      (localizedRootDrift D S C (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR z)
      (localizedRootSpeed D S C g (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR z) δ) Θ) :
    let d := localizedRootDrift D S C (n01ComponentRoot C m side)
      (n01ComponentRootOrientation side) hR z
    let c := localizedRootSpeed D S C g (n01ComponentRoot C m side)
      (n01ComponentRootOrientation side) hR z
    let Θ₁ := rootFlowParameterUnscale Θ δ
    N04bRootCoordinateProperties d c (n01RootLabel S C z m side)
      (fun θ x => Θ₁ (x, x ^ (3 / 2 : ℝ)) 1 θ) 1 1
      (rootInverseCoordinate Θ₁ (n01RootLabel S C z m side)) := by
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  have hreflect := localizedRootFields_reflect hS C g r σ hR z
  have hpos (θ : ℝ) : 0 < localizedRootSpeed D S C g r σ hR z (0, θ) := by
    have hzero : ((0, θ) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) :=
      ⟨⟨by linarith only [hR], by linarith only [hR]⟩, mem_univ _⟩
    have hb := hstrip (0, θ) hzero
    have he := rootFieldLocalization_eqOn (F := factoredCharacteristicSpeed D.w g
      (stateProfile D S C z.1) (stateHeight D S C z) r σ) hR
      (show ((0, θ) : PolarPoint) ∈ Ioo (-(R / 2)) (R / 2) ×ˢ univ from
        ⟨⟨by linarith only [hR], by linarith only [hR]⟩, mem_univ _⟩)
    change 0 < rootFieldLocalization (factoredCharacteristicSpeed D.w g
      (stateProfile D S C z.1) (stateHeight D S C z) r σ) hR (0, θ)
    rw [he]
    exact factoredCharacteristicSpeed_pos hb.1 hb.2.1 hb.2.2.1
      hb.2.2.2.1 hb.2.2.2.2.1
  exact rootFlow_coordinate_properties hregular.1 hregular.2 hperiod.1 hperiod.2
    (fun x θ => (hreflect x θ).1) (fun x θ => (hreflect x θ).2) hpos
    (n01RootLabel_contDiff hS hT hN hz hs m side)
    (fun θ => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
      (n01RootLabel_deriv_mem_quarter_four hN hflow hz hs m side θ).1)
    (n01RootLabel_period_add hN hz hs m side) (n01RootLabel_odd hN hz hs m side)
    (rootFlowParameterUnscale_equations hδ hΘ)

theorem n04PositiveGeometry_radialBoundaryJet_localization
    (F : PolarPoint → ℝ) {R : ℝ} (hR : 0 < R) (j : ℕ) :
    radialBoundaryJet (rootFieldLocalization F hR) 0 j = radialBoundaryJet F 0 j := by
  funext θ
  have he : (fun x => rootFieldLocalization F hR (x, θ)) =ᶠ[𝓝 0]
      (fun x => F (x, θ)) := by
    filter_upwards [Ioo_mem_nhds (neg_neg_of_pos (half_pos hR)) (half_pos hR)] with x hx
    exact rootFieldLocalization_eqOn hR ⟨hx, mem_univ _⟩
  exact he.iteratedDeriv_eq j

theorem n04PositiveGeometry_localizedRoot_boundaryInputs_eq
    (g : ℝ → ℝ) (r σ : ℝ) {R : ℝ} (hR : 0 < R)
    (z : AnnularState S × ℝ) (β : ℝ → ℝ) :
    n06RootBoundaryInputs (localizedRootDrift D S C r σ hR z)
      (localizedRootSpeed D S C g r σ hR z) β =
    n06RootBoundaryInputs
      (orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) r σ)
      (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ) β := by
  unfold n06RootBoundaryInputs localizedRootDrift localizedRootSpeed
  simp only [n04PositiveGeometry_radialBoundaryJet_localization]

end ContinuousFlexibility.Analysis
