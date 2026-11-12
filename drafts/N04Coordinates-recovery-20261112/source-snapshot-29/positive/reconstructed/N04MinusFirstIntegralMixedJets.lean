import ContinuousFlexibility.Analysis.N04bActualTravelChart
import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus

/-!
# Actual radial mixed jets of the inverse-flow first integral

The stored N03 flow equation gives the first integral's radial transport
equation. Differentiating that genuine equation on the open component
reduces every positive radial order to lower radial orders of the same
first integral and actual mixed jets of the corrected characteristic
speed. There is no supplied radial-jet tower or radius-dependent inverse
selection in this identity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem mixedDerivative_radial_succ_of_transport
    {U : Set PolarPoint} (hU : IsOpen U) {F V : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hV : ContDiffOn ℝ ∞ V U)
    (htransport : EqOn (radialPartial V) (fun q => F q * angularPartial V q) U)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    mixedDerivative (a + 1) b V p =
      ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          mixedDerivative i j F p * mixedDerivative (a - i) (b - j + 1) V p := by
  have hangle : ContDiffOn ℝ ∞ (angularPartial V) U := by
    intro q hq
    exact (contDiffAt_angularPartial (hV.contDiffAt (hU.mem_nhds hq))
      (by simp)).contDiffWithinAt
  rw [← mixedDerivative_radialPartial hU hV a b hp,
    n07a_mixedDerivative_eqOn hU htransport a b hp,
    n07a_mixedDerivative_mul_on hU hF hangle a b hp]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [mixedDerivative_angularPartial hU hV (a - i) (b - j) hp]

/-- A finite identity for the actual first integral at every interior point.
The first-integral factors on the right have radial order at most `a`. -/
theorem n04b_actualMinusFirstIntegral_mixed_radial_succ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m a b : ℕ)
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let V := n04bMinusFirstIntegral (fun q => L.minusFlow z m q.1 q.2)
      (stateLeftChart S z.1 m)
    mixedDerivative (a + 1) b V p =
      ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          mixedDerivative i j (fun q => -minusCharacteristicSpeed (L.coefficients z) q) p *
            mixedDerivative (a - i) (b - j + 1) V p := by
  let V := n04bMinusFirstIntegral (fun q => L.minusFlow z m q.1 q.2)
    (stateLeftChart S z.1 m)
  have hopen : IsOpen (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  have hΦ := n04b_actualMinusFlow_regular hN hS hT hfield hz hs m
  have hleft := stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))
  have hV : ContDiffOn ℝ ∞ V (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :=
    n04b_minusFirstIntegral_smooth hΦ Real.pi_ne_zero hleft
  have hF : ContDiffOn ℝ ∞ (fun q => -minusCharacteristicSpeed (L.coefficients z) q)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
    intro q hq
    exact ((n04b_corrected_characteristics_contDiffAt hN hfield hz hs m hq).2.2.1.neg).contDiffWithinAt
  apply mixedDerivative_radial_succ_of_transport hopen hF hV _ a b hp
  intro q hq
  exact n04b_minusFirstIntegral_transport
    (d := n04bCharacteristicDrift (L.coefficients z))
    (v := n04bCharacteristicHalfGap (L.coefficients z)) hΦ Real.pi_ne_zero hleft
    (fun r hr θ => (hN.2.2.2.2.2.1 z hz hs m θ).2.2.1 r hr) hq

end ContinuousFlexibility.Analysis
