import ContinuousFlexibility.Analysis.N04bConstructedRootDensity
import ContinuousFlexibility.Analysis.N04bActualAtlasGerms

/-!
# The actual negative atlas has the common Airy principal density

The coefficient factorization is computed from the corrected field.
The characteristic equations and positive angular derivatives come from
the actual forward flow and its actual inverse labels.  The stored atlas
has these chart and height germs on the whole open negative component.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n04Coordinates_actualAtlas_negativePrincipalDensity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    (coordinatePrincipalDensity (L.coefficients z) (K.chart z k) (K.height z k)).a p = 1 ∧
      (coordinatePrincipalDensity (L.coefficients z) (K.chart z k) (K.height z k)).b p = 0 ∧
      (coordinatePrincipalDensity (L.coefficients z) (K.chart z k) (K.height z k)).c p =
        -(K.chart z k p).1 := by
  let Φ : PolarPoint → ℝ := fun q => L.minusFlow z m q.1 q.2
  let hL : ℝ → ℝ := stateLeftChart S z.1 m
  let d : PolarPoint → ℝ := n04bCharacteristicDrift (L.coefficients z)
  let v : PolarPoint → ℝ := n04bCharacteristicHalfGap (L.coefficients z)
  let U : PolarPoint → ℝ := n04bPlusFirstIntegral Φ hL
  let V : PolarPoint → ℝ := n04bMinusFirstIntegral Φ hL
  have hΦ : N04bCircleFlowRegularity Φ (C.left m) (C.right m) Real.pi :=
    n04b_actualMinusFlow_regular hN hS hT hfield hz hs m
  have hLsmooth : ContDiff ℝ ∞ hL :=
    stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))
  have hleft := hN.1.1.2.2.2.2.2.2.2.1 z hz hs m
  have hLpos : ∀ θ, 0 < deriv hL θ :=
    fun θ => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hleft θ).1
  have hflowRaw := hN.2.2.2.2.2.1 z hz hs m
  have hflow : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
      HasDerivAt (fun s => Φ (s, θ))
        (d (r, Φ (r, θ)) - v (r, Φ (r, θ))) r :=
    fun r hr θ => (hflowRaw θ).2.2.1 r hr
  have hdodd : ∀ q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      d (q.1, -q.2) = -d q :=
    fun q _ => (n04b_actualCharacteristic_reflection hN hz hs q).1
  have hveven : ∀ q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      v (q.1, -q.2) = v q :=
    fun q _ => (n04b_actualCharacteristic_reflection hN hz hs q).2
  have hU : DifferentiableAt ℝ U p :=
    ((n04b_plusFirstIntegral_smooth hΦ Real.pi_ne_zero hLsmooth).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hV : DifferentiableAt ℝ V p :=
    ((n04b_minusFirstIntegral_smooth hΦ Real.pi_ne_zero hLsmooth).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hUr : radialPartial U p = -(d p + v p) * angularPartial U p :=
    n04b_plusFirstIntegral_transport hΦ Real.pi_ne_zero hLsmooth hflow hdodd hveven hp
  have hVr : radialPartial V p = -(d p - v p) * angularPartial V p :=
    n04b_minusFirstIntegral_transport hΦ Real.pi_ne_zero hLsmooth hflow hp
  have hUθ : 0 < angularPartial U p :=
    n04b_plusFirstIntegral_angularPartial_pos hΦ Real.pi_ne_zero hLsmooth hLpos hp
  have hVθ : 0 < angularPartial V p :=
    n04b_minusFirstIntegral_angularPartial_pos hΦ Real.pi_ne_zero hLsmooth hLpos hp
  have hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hC.1 m).1.trans hp.1.1, hp.1.2.trans (hC.1 m).2.2⟩, mem_univ _⟩
  have ha := hfield.positive_a z hz hs p hpD
  have hv : 0 < v p := n04b_actualCharacteristic_halfGap_pos hN hfield hz hs m hp
  have hbc := n04b_characteristic_coefficients (L.coefficients z) ha.ne'
    (hfield.negative_discriminant z hz hs m p hp).le
  have horient : 0 < n04bTravelOrientation (C.travel m) side
      (characteristicTravelChart U V p).1 :=
    n04b_travelOrientation_pos_of_fullStrip side
      ((n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m).mapsTo hp).1
  have hraw :
      (coordinatePrincipalDensity (L.coefficients z)
        (n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side)
        (n04bRootPhysicalHeight (L.coefficients z) v
          (n04bActualTravelChart S C L z m) (C.travel m) side)).a p = 1 ∧
      (coordinatePrincipalDensity (L.coefficients z)
        (n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side)
        (n04bRootPhysicalHeight (L.coefficients z) v
          (n04bActualTravelChart S C L z m) (C.travel m) side)).b p = 0 ∧
      (coordinatePrincipalDensity (L.coefficients z)
        (n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side)
        (n04bRootPhysicalHeight (L.coefficients z) v
          (n04bActualTravelChart S C L z m) (C.travel m) side)).c p =
          -(n04bRootPhysicalChart (n04bActualTravelChart S C L z m)
            (C.travel m) side p).1 :=
    n04b_coordinatePrincipalDensity_constructedRoot (L.coefficients z) d v
      (C.travel m) side hU hV hUr hVr hbc.1 hbc.2 ha hv hUθ hVθ horient
  have hg := n04bActualTypedAtlas_negative_component_germs
    hT hS hN hfield e hz hs k m side hi hp
  have hD := hg.1.fderiv_eq (𝕜 := ℝ)
  have hh := hg.2.self_of_nhds
  have hpoint := hg.1.self_of_nhds
  simpa only [coordinatePrincipalDensity, coefficientQuadratic, planeJacobian,
    hD, hh, hpoint] using hraw

end ContinuousFlexibility.Analysis
