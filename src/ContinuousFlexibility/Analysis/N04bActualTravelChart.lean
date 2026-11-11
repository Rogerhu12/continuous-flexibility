import ContinuousFlexibility.Analysis.N04bCharacteristicFlowField
import ContinuousFlexibility.Analysis.N04bCharacteristicFirstIntegralsChart
import ContinuousFlexibility.Analysis.ReturnChartDifferentiation
import ContinuousFlexibility.Analysis.TravelStripInverseSymmetry

/-!
# The actual corrected travel chart

Every input below belongs to the cumulative N01--N03 witness or the raw
coefficient regularity construction. The forward flow regularity is
derived from that witness, and the first integrals use its literal angular
inverse. The exact return identity proves the global travel-strip
bijection and its actual smooth inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def n04bActualTravelChart (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (z : AnnularState S × ℝ) (m : ℕ) :
    PolarPoint → PolarPoint :=
  n04bCharacteristicTravelChart (fun p => L.minusFlow z m p.1 p.2)
    (stateLeftChart S z.1 m)

def n04bActualTravelInverse (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (z : AnnularState S × ℝ) (m : ℕ) :
    PolarPoint → PolarPoint :=
  Function.invFunOn (n04bActualTravelChart S C L z m)
    (Ioo (C.left m) (C.right m) ×ˢ univ)

section Actual

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hfield : N04bFieldRegularity D S C L base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1) (m : ℕ)

include hN hz hsector in
theorem n04b_actualCharacteristic_reflection (p : PolarPoint) :
    n04bCharacteristicDrift (L.coefficients z) (p.1, -p.2) =
        -n04bCharacteristicDrift (L.coefficients z) p ∧
      n04bCharacteristicHalfGap (L.coefficients z) (p.1, -p.2) =
        n04bCharacteristicHalfGap (L.coefficients z) p := by
  have hs := hN.2.2.2.2.1 z hz hsector p.1 p.2
  have h := n04b_characteristic_reflection (L.coefficients z) p.1 p.2
    hs.1 hs.2.1 hs.2.2
  exact ⟨h.1, h.2.1⟩

include hN hfield hz hsector in
theorem n04b_actualCharacteristic_halfGap_pos
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    0 < n04bCharacteristicHalfGap (L.coefficients z) p := by
  have hcontrol : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hp.1.1, hp.1.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  exact n04b_characteristic_halfGap_pos (L.coefficients z)
    (hfield.positive_a z hz hsector p hpD)
    (hfield.negative_discriminant z hz hsector m p hp)

include hN hS hT hfield hz hsector in
theorem n04b_actualTravelChart_continuous :
    ContinuousOn (n04bActualTravelChart S C L z m)
      (Icc (C.left m) (C.right m) ×ˢ univ) :=
  n04b_characteristicTravelChart_continuous
    (n04b_actualMinusFlow_regular hN hS hT hfield hz hsector m) Real.pi_ne_zero
    (stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))).continuous

include hN hS hT hfield hz hsector in
theorem n04b_actualTravelChart_smooth :
    ContDiffOn ℝ ∞ (n04bActualTravelChart S C L z m)
      (Ioo (C.left m) (C.right m) ×ˢ univ) :=
  n04b_characteristicTravelChart_smooth
    (n04b_actualMinusFlow_regular hN hS hT hfield hz hsector m) Real.pi_ne_zero
    (stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ)))

include hN hS hT hfield hz hsector in
theorem n04b_actualTravelChart_bijOn :
    BijOn (n04bActualTravelChart S C L z m)
      (Ioo (C.left m) (C.right m) ×ˢ univ)
      (Ioo 0 (C.travel m) ×ˢ univ) := by
  have hN01 : N01Properties D T S C base loss ε := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hleft := hN01.2.2.2.2.2.2.2.1 z hz hsector m
  have hflow := hN.2.2.2.2.2.1 z hz hsector m
  apply n04b_characteristicTravelChart_bijOn
    (d := n04bCharacteristicDrift (L.coefficients z))
    (v := n04bCharacteristicHalfGap (L.coefficients z))
    (hR := rightChartCandidate S C z m)
    (n04b_actualMinusFlow_regular hN hS hT hfield hz hsector m)
    Real.pi_ne_zero (hcontrol.1 m).2.1
    (stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ)))
    (fun θ => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hleft θ).1)
    (fun θ => (hleft θ).2.2.1) (fun θ => (hleft θ).2.2.2)
    (rightChartCandidate_odd S C z m)
    (strictMono_of_deriv_pos (N01Properties.rightChart_deriv_pos S C z m hN01 hz hsector))
    (fun θ => (hflow θ).1) (fun θ => (hflow θ).2.2.2.1)
  · intro r hr θ
    exact (hflow θ).2.2.1 r hr
  · intro p _
    exact (n04b_actualCharacteristic_reflection hN hz hsector p).1
  · intro p _
    exact (n04b_actualCharacteristic_reflection hN hz hsector p).2
  · intro p hp
    exact n04b_actualCharacteristic_halfGap_pos hN hfield hz hsector m hp

include hN hS hT hfield hz hsector in
theorem n04b_actualTravel_positive : 0 < C.travel m := by
  have hcontrol : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hab := (hcontrol.1 m).2.1
  have hp : ((C.left m + C.right m) / 2, (0 : ℝ)) ∈
      Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  have himage := (n04b_actualTravelChart_bijOn hN hS hT hfield hz hsector m).mapsTo hp
  exact himage.1.1.trans himage.1.2

include hN hS hT hfield hz hsector in
theorem n04b_actualTravelChart_jacobian_pos
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    0 < planeJacobian (n04bActualTravelChart S C L z m) p := by
  have hleft := hN.1.1.2.2.2.2.2.2.2.1 z hz hsector m
  have hflow := hN.2.2.2.2.2.1 z hz hsector m
  exact n04b_characteristicTravelChart_jacobian_pos
    (n04b_actualMinusFlow_regular hN hS hT hfield hz hsector m) Real.pi_ne_zero
    (stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ)))
    (fun θ => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hleft θ).1)
    (fun r hr θ => (hflow θ).2.2.1 r hr)
    (fun p _ => (n04b_actualCharacteristic_reflection hN hz hsector p).1)
    (fun p _ => (n04b_actualCharacteristic_reflection hN hz hsector p).2)
    hp (n04b_actualCharacteristic_halfGap_pos hN hfield hz hsector m hp)

include hN hS hT hfield hz hsector in
theorem n04b_actualTravelInverse_spec :
    MapsTo (n04bActualTravelInverse S C L z m)
      (Ioo 0 (C.travel m) ×ˢ univ) (Ioo (C.left m) (C.right m) ×ˢ univ) ∧
      LeftInvOn (n04bActualTravelInverse S C L z m)
        (n04bActualTravelChart S C L z m) (Ioo (C.left m) (C.right m) ×ˢ univ) ∧
      RightInvOn (n04bActualTravelInverse S C L z m)
        (n04bActualTravelChart S C L z m) (Ioo 0 (C.travel m) ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (n04bActualTravelInverse S C L z m)
        (Ioo 0 (C.travel m) ×ˢ univ) := by
  have hBij := n04b_actualTravelChart_bijOn hN hS hT hfield hz hsector m
  refine ⟨hBij.surjOn.mapsTo_invFunOn, hBij.injOn.leftInvOn_invFunOn,
    hBij.surjOn.rightInvOn_invFunOn, ?_⟩
  exact contDiffOn_planar_invFunOn_of_bijOn (isOpen_Ioo.prod isOpen_univ)
    (isOpen_Ioo.prod isOpen_univ)
    (n04b_actualTravelChart_smooth hN hS hT hfield hz hsector m)
    (fun p hp => (n04b_actualTravelChart_jacobian_pos
      hN hS hT hfield hz hsector m hp).ne') hBij

include hN hS hT hfield hz hsector in
theorem n04b_actualTravelChart_period_add
    {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    n04bActualTravelChart S C L z m (r, θ + Real.pi) =
      n04bActualTravelChart S C L z m (r, θ) + (0, Real.pi) := by
  have hleft := hN.1.1.2.2.2.2.2.2.2.1 z hz hsector m
  exact n04b_characteristicTravelChart_period_add
    (n04b_actualMinusFlow_regular hN hS hT hfield hz hsector m) Real.pi_ne_zero
    (fun θ => (hleft θ).2.2.1) hr θ

theorem n04b_actualTravelChart_reflection (p : PolarPoint) :
    n04bActualTravelChart S C L z m (p.1, -p.2) =
      ((n04bActualTravelChart S C L z m p).1,
        -(n04bActualTravelChart S C L z m p).2) :=
  n04b_characteristicTravelChart_reflection _ _ p

include hN hS hT hfield hz hsector in
theorem n04b_actualTravelInverse_symmetries
    {p : PolarPoint} (hp : p ∈ Ioo 0 (C.travel m) ×ˢ (univ : Set ℝ)) :
    n04bActualTravelInverse S C L z m (p + (0, Real.pi)) =
        n04bActualTravelInverse S C L z m p + (0, Real.pi) ∧
      n04bActualTravelInverse S C L z m (p.1, -p.2) =
        ((n04bActualTravelInverse S C L z m p).1,
          -(n04bActualTravelInverse S C L z m p).2) := by
  have hBij := n04b_actualTravelChart_bijOn hN hS hT hfield hz hsector m
  constructor
  · apply travelStrip_invFunOn_periodic hBij _ hp
    rintro ⟨r, θ⟩ hq
    simpa only [Prod.mk_add_mk, add_zero] using
      n04b_actualTravelChart_period_add hN hS hT hfield hz hsector m
        ⟨hq.1.1.le, hq.1.2.le⟩ θ
  · exact travelStrip_invFunOn_reflection hBij
      (fun q _ => n04b_actualTravelChart_reflection m q) hp

include hN hS hT hfield hz hsector in
theorem n04b_actualTravelChart_endpoints (θ : ℝ) :
    n04bActualTravelChart S C L z m (C.left m, θ) =
        (0, stateLeftChart S z.1 m θ) ∧
      n04bActualTravelChart S C L z m (C.right m, θ) =
        (C.travel m, rightChartCandidate S C z m θ) := by
  let Φ : PolarPoint → ℝ := fun p => L.minusFlow z m p.1 p.2
  let hL := stateLeftChart S z.1 m
  let hR := rightChartCandidate S C z m
  have hΦ := n04b_actualMinusFlow_regular hN hS hT hfield hz hsector m
  have hcontrol : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hab := (hcontrol.1 m).2.1.le
  have hleft := hN.1.1.2.2.2.2.2.2.2.1 z hz hsector m
  have hflow := hN.2.2.2.2.2.1 z hz hsector m
  have hinit : ∀ t, Φ (C.left m, t) = t := fun t => (hflow t).1
  have hreturn : ∀ t, hR (Φ (C.right m, t)) = hL t - C.travel m :=
    fun t => (hflow t).2.2.2.1
  have hVL : n04bMinusFirstIntegral Φ hL (C.left m, θ) = hL θ :=
    n04b_minusFirstIntegral_left hΦ hab hinit hL θ
  have hUL : n04bPlusFirstIntegral Φ hL (C.left m, θ) = hL θ :=
    n04b_plusFirstIntegral_left hΦ hab hinit (fun t => (hleft t).2.2.2) θ
  have hVR : n04bMinusFirstIntegral Φ hL (C.right m, θ) = hR θ + C.travel m :=
    n04b_minusFirstIntegral_right hΦ Real.pi_ne_zero hab hreturn θ
  have hUR : n04bPlusFirstIntegral Φ hL (C.right m, θ) = hR θ - C.travel m :=
    n04b_plusFirstIntegral_right hΦ Real.pi_ne_zero hab hreturn
      (rightChartCandidate_odd S C z m) θ
  change characteristicTravelChart (n04bPlusFirstIntegral Φ hL)
      (n04bMinusFirstIntegral Φ hL) (C.left m, θ) = (0, hL θ) ∧
    characteristicTravelChart (n04bPlusFirstIntegral Φ hL)
      (n04bMinusFirstIntegral Φ hL) (C.right m, θ) = (C.travel m, hR θ)
  simp only [characteristicTravelChart, hVL, hUL, hVR, hUR]
  constructor <;> congr 1 <;> ring

end Actual
end ContinuousFlexibility.Analysis
