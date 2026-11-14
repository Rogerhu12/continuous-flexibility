module

public import ContinuousFlexibility.Analysis.N04bCharacteristicFirstIntegralsTransport
public import ContinuousFlexibility.Analysis.CharacteristicTravelStrip

/-!
# The full travel strip of an actual characteristic flow

The first integrals are the actual inverse minus flow and its reflection.
The full-strip bijection and smooth actual inverse follow from their proved
regularity, transport equations, and exact endpoint normalizations. This
module does not identify fixed radial halves with travel-time halves.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n04bCharacteristicTravelChart (Φ : PolarPoint → ℝ) (hL : ℝ → ℝ) :
    PolarPoint → PolarPoint :=
  characteristicTravelChart (n04bPlusFirstIntegral Φ hL) (n04bMinusFirstIntegral Φ hL)

theorem n04b_characteristicTravelChart_continuous
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : Continuous hL) :
    ContinuousOn (n04bCharacteristicTravelChart Φ hL) (Icc a b ×ˢ univ) := by
  have hU := n04b_plusFirstIntegral_continuous hΦ hP hhL
  have hV := n04b_minusFirstIntegral_continuous hΦ hP hhL
  exact (continuousOn_const.mul (hV.sub hU)).prodMk
    (continuousOn_const.mul (hU.add hV))

theorem n04b_characteristicTravelChart_smooth
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : ContDiff ℝ ∞ hL) :
    ContDiffOn ℝ ∞ (n04bCharacteristicTravelChart Φ hL) (Ioo a b ×ˢ univ) := by
  have hU := n04b_plusFirstIntegral_smooth hΦ hP hhL
  have hV := n04b_minusFirstIntegral_smooth hΦ hP hhL
  exact (contDiffOn_const.mul (hV.sub hU)).prodMk
    (contDiffOn_const.mul (hU.add hV))

/-- Reflection exchanges the two actual first integrals. -/
theorem n04b_characteristicTravelChart_reflection
    (Φ : PolarPoint → ℝ) (hL : ℝ → ℝ) (p : PolarPoint) :
    n04bCharacteristicTravelChart Φ hL (p.1, -p.2) =
      ((n04bCharacteristicTravelChart Φ hL p).1,
        -(n04bCharacteristicTravelChart Φ hL p).2) := by
  simp only [n04bCharacteristicTravelChart, characteristicTravelChart,
    n04bPlusFirstIntegral, neg_neg]
  congr 1 <;> ring

theorem n04b_characteristicTravelChart_period_add
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hLperiod : ∀ θ, hL (θ + P) = hL θ + P)
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    n04bCharacteristicTravelChart Φ hL (r, θ + P) =
      n04bCharacteristicTravelChart Φ hL (r, θ) + (0, P) := by
  simp only [n04bCharacteristicTravelChart, characteristicTravelChart,
    n04b_plusFirstIntegral_period_add hΦ hP hLperiod hr θ,
    n04b_minusFirstIntegral_period_add hΦ hP hLperiod hr θ, Prod.mk_add_mk]
  congr 1 <;> ring

theorem n04b_characteristicTravelChart_jacobian_pos
    {Φ d v : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : ContDiff ℝ ∞ hL) (hLpos : ∀ θ, 0 < deriv hL θ)
    (hflow : ∀ r ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun s => Φ (s, θ))
        (d (r, Φ (r, θ)) - v (r, Φ (r, θ))) r)
    (hdodd : ∀ p ∈ Ioo a b ×ˢ univ, d (p.1, -p.2) = -d p)
    (hveven : ∀ p ∈ Ioo a b ×ˢ univ, v (p.1, -p.2) = v p)
    {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ univ) (hv : 0 < v p) :
    0 < planeJacobian (n04bCharacteristicTravelChart Φ hL) p := by
  have hUd : DifferentiableAt ℝ (n04bPlusFirstIntegral Φ hL) p :=
    ((n04b_plusFirstIntegral_smooth hΦ hP hhL).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hVd : DifferentiableAt ℝ (n04bMinusFirstIntegral Φ hL) p :=
    ((n04b_minusFirstIntegral_smooth hΦ hP hhL).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  exact planeJacobian_characteristicTravelChart_pos hUd hVd
    (n04b_plusFirstIntegral_transport hΦ hP hhL hflow hdodd hveven hp)
    (n04b_minusFirstIntegral_transport hΦ hP hhL hflow hp) hv
    (n04b_plusFirstIntegral_angularPartial_pos hΦ hP hhL hLpos hp)
    (n04b_minusFirstIntegral_angularPartial_pos hΦ hP hhL hLpos hp)

/-- The exact return identity of the given flow produces the full travel strip. -/
theorem n04b_characteristicTravelChart_bijOn
    {Φ d v : PolarPoint → ℝ} {hL hR : ℝ → ℝ} {a b P W : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0) (hab : a < b)
    (hhL : ContDiff ℝ ∞ hL) (hLpos : ∀ θ, 0 < deriv hL θ)
    (hLperiod : ∀ θ, hL (θ + P) = hL θ + P)
    (hLodd : ∀ θ, hL (-θ) = -hL θ) (hRodd : ∀ θ, hR (-θ) = -hR θ)
    (hRm : StrictMono hR)
    (hleft : ∀ θ, Φ (a, θ) = θ)
    (hreturn : ∀ θ, hR (Φ (b, θ)) = hL θ - W)
    (hflow : ∀ r ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun s => Φ (s, θ))
        (d (r, Φ (r, θ)) - v (r, Φ (r, θ))) r)
    (hdodd : ∀ p ∈ Ioo a b ×ˢ univ, d (p.1, -p.2) = -d p)
    (hveven : ∀ p ∈ Ioo a b ×ˢ univ, v (p.1, -p.2) = v p)
    (hv : ∀ p ∈ Ioo a b ×ˢ univ, 0 < v p) :
    BijOn (n04bCharacteristicTravelChart Φ hL)
      (Ioo a b ×ˢ univ) (Ioo 0 W ×ˢ univ) := by
  exact characteristicTravelChart_bijOn hab hP
    (n04b_plusFirstIntegral_continuous hΦ hP hhL.continuous)
    (n04b_minusFirstIntegral_continuous hΦ hP hhL.continuous)
    (n04b_plusFirstIntegral_smooth hΦ hP hhL)
    (n04b_minusFirstIntegral_smooth hΦ hP hhL)
    (fun _ hp => n04b_plusFirstIntegral_transport hΦ hP hhL hflow hdodd hveven hp)
    (fun _ hp => n04b_minusFirstIntegral_transport hΦ hP hhL hflow hp) hv
    (fun _ hp => n04b_plusFirstIntegral_angularPartial_pos hΦ hP hhL hLpos hp)
    (fun _ hp => n04b_minusFirstIntegral_angularPartial_pos hΦ hP hhL hLpos hp)
    (fun _ hr θ => n04b_plusFirstIntegral_period_add hΦ hP hLperiod hr θ)
    (fun _ hr θ => n04b_minusFirstIntegral_period_add hΦ hP hLperiod hr θ)
    (strictMono_of_deriv_pos hLpos) hRm
    (n04b_plusFirstIntegral_left hΦ hab.le hleft hLodd)
    (n04b_minusFirstIntegral_left hΦ hab.le hleft hL)
    (n04b_plusFirstIntegral_right hΦ hP hab.le hreturn hRodd)
    (n04b_minusFirstIntegral_right hΦ hP hab.le hreturn)

/-- The actual set-theoretic inverse of this flow-built chart is smooth.
The bijection may be supplied by the preceding actual-flow theorem. -/
theorem n04b_characteristicTravelChart_inverse_spec
    {Φ d v : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P W : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : ContDiff ℝ ∞ hL) (hLpos : ∀ θ, 0 < deriv hL θ)
    (hflow : ∀ r ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun s => Φ (s, θ))
        (d (r, Φ (r, θ)) - v (r, Φ (r, θ))) r)
    (hdodd : ∀ p ∈ Ioo a b ×ˢ univ, d (p.1, -p.2) = -d p)
    (hveven : ∀ p ∈ Ioo a b ×ˢ univ, v (p.1, -p.2) = v p)
    (hv : ∀ p ∈ Ioo a b ×ˢ univ, 0 < v p)
    (hBij : BijOn (n04bCharacteristicTravelChart Φ hL)
      (Ioo a b ×ˢ univ) (Ioo 0 W ×ˢ univ)) :
    let Γ := n04bCharacteristicTravelChart Φ hL
    let G := Function.invFunOn Γ (Ioo a b ×ˢ univ)
    MapsTo G (Ioo 0 W ×ˢ univ) (Ioo a b ×ˢ univ) ∧
      LeftInvOn G Γ (Ioo a b ×ˢ univ) ∧
      RightInvOn G Γ (Ioo 0 W ×ˢ univ) ∧
      ContDiffOn ℝ ∞ G (Ioo 0 W ×ˢ univ) := by
  refine ⟨hBij.surjOn.mapsTo_invFunOn, hBij.injOn.leftInvOn_invFunOn,
    hBij.surjOn.rightInvOn_invFunOn, ?_⟩
  exact contDiffOn_planar_invFunOn_of_bijOn (isOpen_Ioo.prod isOpen_univ)
    (isOpen_Ioo.prod isOpen_univ) (n04b_characteristicTravelChart_smooth hΦ hP hhL)
    (fun p hp => (n04b_characteristicTravelChart_jacobian_pos
      hΦ hP hhL hLpos hflow hdodd hveven hp (hv p hp)).ne') hBij

end ContinuousFlexibility.Analysis
