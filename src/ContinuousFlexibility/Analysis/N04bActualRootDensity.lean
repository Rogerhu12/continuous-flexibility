import ContinuousFlexibility.Analysis.N04bActualTravelChart
import ContinuousFlexibility.Analysis.N04bConstructedRootDensity

/-!
# The actual corrected field in a pasted characteristic root chart

The characteristic PDEs, positive angular derivatives, and coefficient
factorization are derived from the cumulative construction. A chart which
agrees near the physical point with the actual root chart, with the actual
height value, therefore has principal density (1, 0, -ξ).
This is the local calculation used after constructing the literal atlas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n04b_actualRootDensity_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool)
    {F : PolarPoint → PolarPoint} {height : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (ht : 0 < n04bTravelOrientation (C.travel m) side
      (n04bActualTravelChart S C L z m x).1)
    (hF : F =ᶠ[𝓝 x]
      n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side)
    (hh : height x =
      n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) side x) :
    (coordinatePrincipalDensity (L.coefficients z) F height).a x = 1 ∧
      (coordinatePrincipalDensity (L.coefficients z) F height).b x = 0 ∧
      (coordinatePrincipalDensity (L.coefficients z) F height).c x = -(F x).1 := by
  let Φ : PolarPoint → ℝ := fun p => L.minusFlow z m p.1 p.2
  let hL : ℝ → ℝ := stateLeftChart S z.1 m
  let U : PolarPoint → ℝ := n04bPlusFirstIntegral Φ hL
  let V : PolarPoint → ℝ := n04bMinusFirstIntegral Φ hL
  let d : PolarPoint → ℝ := n04bCharacteristicDrift (L.coefficients z)
  let v : PolarPoint → ℝ := n04bCharacteristicHalfGap (L.coefficients z)
  let scale : PolarPoint → ℝ :=
    n04bRootDifferentialScale (characteristicTravelChart U V) (C.travel m) side
  have hΦ : N04bCircleFlowRegularity Φ (C.left m) (C.right m) Real.pi :=
    n04b_actualMinusFlow_regular h03 hS hT hfield hz hs m
  have hhL : ContDiff ℝ ∞ hL :=
    stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))
  have hleft := h03.1.1.2.2.2.2.2.2.2.1 z hz hs m
  have hLpos : ∀ θ, 0 < deriv hL θ :=
    fun θ => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hleft θ).1
  have hflow : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
      HasDerivAt (fun s => Φ (s, θ))
        (d (r, Φ (r, θ)) - v (r, Φ (r, θ))) r := by
    intro r hr θ
    exact (h03.2.2.2.2.2.1 z hz hs m θ).2.2.1 r hr
  have hdodd : ∀ p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      d (p.1, -p.2) = -d p :=
    fun p _ => (n04b_actualCharacteristic_reflection h03 hz hs p).1
  have hveven : ∀ p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      v (p.1, -p.2) = v p :=
    fun p _ => (n04b_actualCharacteristic_reflection h03 hz hs p).2
  have hU : DifferentiableAt ℝ U x :=
    ((n04b_plusFirstIntegral_smooth hΦ Real.pi_ne_zero hhL).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx)).differentiableAt (by simp)
  have hV : DifferentiableAt ℝ V x :=
    ((n04b_minusFirstIntegral_smooth hΦ Real.pi_ne_zero hhL).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx)).differentiableAt (by simp)
  have hUr : radialPartial U x = -(d x + v x) * angularPartial U x :=
    n04b_plusFirstIntegral_transport hΦ Real.pi_ne_zero hhL hflow hdodd hveven hx
  have hVr : radialPartial V x = -(d x - v x) * angularPartial V x :=
    n04b_minusFirstIntegral_transport hΦ Real.pi_ne_zero hhL hflow hx
  have hUθ : 0 < angularPartial U x :=
    n04b_plusFirstIntegral_angularPartial_pos hΦ Real.pi_ne_zero hhL hLpos hx
  have hVθ : 0 < angularPartial V x :=
    n04b_minusFirstIntegral_angularPartial_pos hΦ Real.pi_ne_zero hhL hLpos hx
  have hcontrol : controlGeometryConditions D S C := h03.1.1.2.2.2.1
  have hxD : x ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hx.1.1, hx.1.2.trans (hcontrol.1 m).2.2⟩,
      mem_univ _⟩
  have ha : 0 < (L.coefficients z).a x := hfield.positive_a z hz hs x hxD
  have hv : 0 < v x := n04b_actualCharacteristic_halfGap_pos h03 hfield hz hs m hx
  have hcoeff := n04b_characteristic_coefficients (L.coefficients z) ha.ne'
    (hfield.negative_discriminant z hz hs m x hx).le
  have hTravel : DifferentiableAt ℝ (characteristicTravelChart U V) x :=
    n04b_differentiableAt_characteristicTravelChart hU hV
  have ht' : 0 < n04bTravelOrientation (C.travel m) side
      (characteristicTravelChart U V x).1 := ht
  have hFgerm : F =ᶠ[𝓝 x]
      n04bRootPhysicalChart (characteristicTravelChart U V) (C.travel m) side := hF
  have hD : fderiv ℝ F x =
      fderiv ℝ (n04bRootPhysicalChart (characteristicTravelChart U V)
        (C.travel m) side) x := hFgerm.fderiv_eq
  have hpoint : F x =
      n04bRootPhysicalChart (characteristicTravelChart U V) (C.travel m) side x :=
    hFgerm.self_of_nhds
  have hroot : |scale x| ^ 2 * (F x).1 = 1 := by
    rw [hpoint]
    exact n04bRootDifferentialScale_normalization ht'
  have hheight : height x = n04bSignedRootHeight (L.coefficients z) v scale x :=
    hh.trans (n04bRootPhysicalHeight_eq_signed ht')
  refine n04b_coordinatePrincipalDensity_signedRoot (L.coefficients z)
    height d v scale hU hV hUr hVr hcoeff.1 hcoeff.2 ha hv
    (n04bRootDifferentialScale_ne_zero ht') hUθ hVθ ?_ ?_ hroot hheight
  · rw [hD]
    exact n04b_fderiv_rootPhysicalChart_apply hTravel ht' (1, 0)
  · rw [hD]
    exact n04b_fderiv_rootPhysicalChart_apply hTravel ht' (0, 1)

end ContinuousFlexibility.Analysis
