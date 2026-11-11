import ContinuousFlexibility.Radial.InnerSelectedDirichletEstimates
import ContinuousFlexibility.Radial.InnerSelectedCouplingBound
import ContinuousFlexibility.Radial.InnerSelectedInverseConstants

/-!
# Both weighted bounds for the same selected inner inverse

The localized multiplier is exactly the prescribed output loss times
the actual weight. The genuine local Dirichlet bounds pay exponent
thirty-seven; the same Poisson-adjoint correction pays no coefficient
loss. All constants are fixed before the band, mode and weight exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)
  {a CC KC CM KM η : ℝ}
  (hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η)
  (hMorseFamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
  (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀)
  (K q : ℕ) (hq : 1 ≤ q)
  (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q))

local notation "A" => P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
local notation "H" => InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))

/-- The actual coefficient loss has the fixed exponent 37, and the
same inverse is bounded independently of the number of retained cells. -/
theorem inverse_localized_bound
    (hS : IsUnit (A).fluxMatrix)
    (ha : 0 ≤ a) (hN : 4096 ≤ S.chain.index)
    (hNa : 64 * a ≤ (S.chain.index : ℝ))
    (hCC : 0 ≤ CC) (hCM : 0 < CM)
    (hη : 0 ≤ η) (hηsmall : η < 1 / 4) {γ : ℝ} (hγ : |γ| ≤ 1) :
    ‖innerMorseInnerSupportedLocalizedWeight S.chain.index K a γ (P.chain K) A 37
          (by norm_num : (0 : ℝ) ≤ 37) ∘L
        P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS ∘L
        ((innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A).symm :
          H →L[ℝ] H)‖ ≤ P.inverseLocalizedConstant CC CM := by
  let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
  let L := innerMorseInnerSupportedLoss S.chain.index K (P.chain K) (decide (q = 1)) 37
    (by norm_num : (0 : ℝ) ≤ 37)
  have hD₀ := P.dirichlet_localized_bound hCentralFamily hMorseFamily hX hsupport
    K q hq hband hCC hCM.le ha hN hNa γ hγ
  rw [innerMorseInnerSupportedLocalizedWeight_eq_loss_comp] at hD₀
  have hD :
      ‖L ∘L ((innerHilbertWeight W true : H →L[ℝ] H) ∘L
        (A).dirichlet P.geometry.2.2.1.1 ∘L
        (innerHilbertWeight W (!true) : H →L[ℝ] H))‖ ≤
      P.dirichletConstant CC CM * radialE S.chain.index ^ (37 : ℝ) := by
    simpa only [L, W, innerHilbertWeight, Bool.not_true, Bool.false_eq_true,
      ite_true, ite_false, ContinuousLinearMap.comp_assoc] using hD₀
  have h := (P.inverse_localized_bound_of_dirichlet hCentralFamily hMorseFamily
    hX hsupport K q hq hband hS ha hN hNa hCM hη hηsmall hγ L
    (innerMorseInnerSupportedLoss_norm_le_one S.chain.index K (P.chain K) (decide (q = 1))
      37 (by norm_num)) true hD).trans
        (add_le_add_left (inner_selected_even_correction_le P.poissonConstant hq) _)
  simpa only [innerMorseInnerSupportedLocalizedWeight_eq_loss_comp, L, W,
    innerHilbertWeight, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    ContinuousLinearMap.comp_assoc, inverseLocalizedConstant] using h

/-- Both reciprocal conjugations of that same inverse are bounded by
one fixed power of the transition coefficient. -/
theorem inverse_coarse_bound
    (hS : IsUnit (A).fluxMatrix)
    (ha : 0 ≤ a) (hN : 4096 ≤ S.chain.index)
    (hNa : 64 * a ≤ (S.chain.index : ℝ))
    (hCC : 0 ≤ CC) (hCM : 0 < CM)
    (hη : 0 ≤ η) (hηsmall : η < 1 / 4) {γ : ℝ} (hγ : |γ| ≤ 1) (sign : Bool) :
    let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
    ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L
        P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS ∘L
        (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ ≤
      radialE (S.chain.index + K) ^ P.inverseCoarseExponent CC CM := by
  exact (P.inverse_bound_of_dirichlet hCentralFamily hMorseFamily hX hsupport
    K q hq hband hS ha hN hNa hCM hη hηsmall hγ sign
    (P.dirichlet_coarse_bound hCentralFamily hMorseFamily hX hsupport
      K q hq hband hCC hCM.le ha hN hNa γ hγ sign)).trans
        (P.coarse_cost_and_correction CC CM K q hq)

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
