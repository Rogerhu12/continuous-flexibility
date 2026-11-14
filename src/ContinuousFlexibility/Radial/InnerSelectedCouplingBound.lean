module

public import ContinuousFlexibility.Radial.InnerSelectedInterfaceEstimates
public import ContinuousFlexibility.Radial.InnerSelectedPhysicalInverse
public import ContinuousFlexibility.Radial.InnerRadialWeightedInverse

/-!
# The coupling correction for the same selected inverse

The two actual Poisson bounds and the proved interface error bounds
control the actual Poisson-adjoint correction. This term has no
coefficient loss. A contraction on the output preserves this estimate;
only the actual Dirichlet part remains to be bounded.
-/

@[expose] public section

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

/-- The same full flux inverse and the same physical Poisson operator
give the lossless correction for both reciprocal signs. -/
theorem coupling_weighted_bound
    (ha : 0 ≤ a) (hN : 4096 ≤ S.chain.index)
    (hNa : 64 * a ≤ (S.chain.index : ℝ)) (hCM : 0 < CM)
    (hη : 0 ≤ η) (hηsmall : η < 1 / 4) {γ : ℝ} (hγ : |γ| ≤ 1) (sign : Bool) :
    let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
    ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L
        innerCouplingCorrection ((A).poisson P.geometry.2.2.1.1)
          (Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ)
            (A).fluxMatrix⁻¹) ∘L
        (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ ≤
      2 * P.poissonConstant ^ 2 / ((2 : ℝ) * q) ^ 2 := by
  have hj : 0 < (2 : ℝ) * q := by
    exact_mod_cast (show 0 < 2 * q by omega)
  exact innerCoupling_bound_from_interface (A).referenceMatrix
    (Matrix.diagonal (innerMorseInnerInterfaceWeight S.chain.index K a γ)) (A).errorMatrix
    (P.actualChain_reference_posDef hCentralFamily hMorseFamily hX hsupport K q hq hband)
    (Matrix.posDef_diagonal_iff.mpr (innerMorseInnerInterfaceWeight_pos S.chain.index K a γ))
    (P.actualChain_reference_commute hCentralFamily hMorseFamily hX hsupport K q hq hband γ)
    (P.actualChain_normalized_error hCentralFamily hMorseFamily hX hsupport K q hq hband
      hη hηsmall hγ)
    (innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A)
    ((A).poisson P.geometry.2.2.1.1)
    (innerMorseInnerSupportedWeightEquiv_selfAdjoint S.chain.index K a γ (P.chain K) A)
    P.poissonConstant_pos.le hj
    (P.actualChain_poisson_bound hCentralFamily hMorseFamily hX hsupport K q hq hband
      ha hN hNa hCM hγ) sign

/-- The coarse estimate reduces to the Dirichlet estimate for the
same signed weight, with a correction uniform in the number of cells. -/
theorem inverse_bound_of_dirichlet
    (hS : IsUnit (A).fluxMatrix)
    (ha : 0 ≤ a) (hN : 4096 ≤ S.chain.index)
    (hNa : 64 * a ≤ (S.chain.index : ℝ)) (hCM : 0 < CM)
    (hη : 0 ≤ η) (hηsmall : η < 1 / 4) {γ : ℝ} (hγ : |γ| ≤ 1) (sign : Bool)
    {d : ℝ}
    (hD :
      let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
      ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L
          (A).dirichlet P.geometry.2.2.1.1 ∘L
          (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ ≤ d) :
    let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
    ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L
        P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS ∘L
        (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ ≤
      d + 2 * P.poissonConstant ^ 2 / ((2 : ℝ) * q) ^ 2 := by
  have hcor := P.coupling_weighted_bound hCentralFamily hMorseFamily hX hsupport K q hq hband
    ha hN hNa hCM hη hηsmall hγ sign
  dsimp only at hD hcor ⊢
  rw [inverse, (A).inverse_eq_glued P.geometry.2.2.1.1 hS]
  simp only [innerGluedInverse, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  exact (norm_add_le _ _).trans (add_le_add hD hcor)

/-- An actual output contraction leaves the same correction bound
unchanged. The only remaining input is its actual Dirichlet cost. -/
theorem inverse_localized_bound_of_dirichlet
    (hS : IsUnit (A).fluxMatrix)
    (ha : 0 ≤ a) (hN : 4096 ≤ S.chain.index)
    (hNa : 64 * a ≤ (S.chain.index : ℝ)) (hCM : 0 < CM)
    (hη : 0 ≤ η) (hηsmall : η < 1 / 4) {γ : ℝ} (hγ : |γ| ≤ 1)
    (L : H →L[ℝ] H) (hL : ‖L‖ ≤ 1) (sign : Bool) {d : ℝ}
    (hD :
      let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
      ‖L ∘L ((innerHilbertWeight W sign : H →L[ℝ] H) ∘L
          (A).dirichlet P.geometry.2.2.1.1 ∘L
          (innerHilbertWeight W (!sign) : H →L[ℝ] H))‖ ≤ d) :
    let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
    ‖L ∘L ((innerHilbertWeight W sign : H →L[ℝ] H) ∘L
        P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS ∘L
        (innerHilbertWeight W (!sign) : H →L[ℝ] H))‖ ≤
      d + 2 * P.poissonConstant ^ 2 / ((2 : ℝ) * q) ^ 2 := by
  let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
  let C := innerCouplingCorrection ((A).poisson P.geometry.2.2.1.1)
    (Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ) (A).fluxMatrix⁻¹)
  have hcor := P.coupling_weighted_bound hCentralFamily hMorseFamily hX hsupport K q hq hband
    ha hN hNa hCM hη hηsmall hγ sign
  have hloss :
      ‖L ∘L ((innerHilbertWeight W sign : H →L[ℝ] H) ∘L C ∘L
        (innerHilbertWeight W (!sign) : H →L[ℝ] H))‖ ≤
      2 * P.poissonConstant ^ 2 / ((2 : ℝ) * q) ^ 2 := by
    calc
      _ ≤ ‖L‖ * ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L C ∘L
          (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (2 * P.poissonConstant ^ 2 / ((2 : ℝ) * q) ^ 2) :=
        mul_le_mul hL hcor (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  dsimp only at hD ⊢
  rw [inverse, (A).inverse_eq_glued P.geometry.2.2.1.1 hS]
  simp only [innerGluedInverse, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  exact (norm_add_le _ _).trans (add_le_add hD hloss)

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
