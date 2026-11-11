import ContinuousFlexibility.Radial.InnerSelectedDirichletCosts
import ContinuousFlexibility.Radial.InnerMorseInnerSupportedWeights

/-!
# Both coefficient estimates for the selected physical Dirichlet sum

All weights are the canonical multipliers on the same supported source.
The actual cell comparisons and the proved local Dirichlet costs give
loss thirty-seven. The coarse estimate uses the largest retained-band
coefficient and holds for both signs of one weight equivalence.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

theorem innerSignedWeight_not_apply {α : Type*} (W : α → ℝ) (sign : Bool) (x : α) :
    innerSignedWeight W (!sign) x = (innerSignedWeight W sign x)⁻¹ := by
  cases sign <;>
    simp only [innerSignedWeight, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true, inv_inv]

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)
  {a CC KC CM KM η : ℝ}
  (hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η)
  (hMorseFamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
  (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀)
  (K q : ℕ) (hq : 1 ≤ q)
  (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q))

/-- The fixed output loss acts on the actual physical Dirichlet sum.
Its bound is independent of the finite truncation, mode and weight. -/
theorem dirichlet_localized_bound
    (hCC : 0 ≤ CC) (hCM : 0 ≤ CM) (ha : 0 ≤ a)
    (hN : 4096 ≤ S.chain.index) (hNa : 64 * a ≤ (S.chain.index : ℝ))
    (γ : ℝ) (hγ : |γ| ≤ 1) :
    let A := P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
    let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
    ‖innerMorseInnerSupportedLocalizedWeight S.chain.index K a γ (P.chain K) A 37
          (by norm_num : (0 : ℝ) ≤ 37) ∘L A.dirichlet P.geometry.2.2.1.1 ∘L
        (W.symm : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) →L[ℝ]
          InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)))‖ ≤
      P.dirichletConstant CC CM * radialE S.chain.index ^ (37 : ℝ) := by
  dsimp only
  let A := P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
  have hlocalW : ∀ p x, x ∈ Ioo ((P.chain K).left p) ((P.chain K).right p) →
      |innerMorseInnerLocalizedWeight S.chain.index K a γ (P.chain K) A 37 x| ≤
        innerCoefficientLoss S.chain.index 37 (innerMorseInnerPieceIndex S.chain.index K p) *
          sqrt (radialE (innerMorseInnerPieceIndex S.chain.index K p)) *
            innerMorseInnerPieceBase S.chain.index K a γ 1 p := by
    intro p x hx
    simpa only [innerMorseInnerLocalizedWeight, rpow_one, mul_comm] using
      innerMorseInnerWeight_localized_piece_bound
        (a := a) (γ := γ) (σ := 1) (ℓ := 37)
        S.chain.index K (P.chain K) ha hγ (by norm_num) hN hNa
        A.leftWall A.rightWall p hx
  have hlocalV : ∀ p x, x ∈ Ioo ((P.chain K).left p) ((P.chain K).right p) →
      |(innerMorseInnerWeight S.chain.index K a γ (P.chain K) A.leftWall A.rightWall x)⁻¹| ≤
        sqrt (radialE (innerMorseInnerPieceIndex S.chain.index K p)) /
          innerMorseInnerPieceBase S.chain.index K a γ 1 p := by
    intro p x hx
    simpa only [rpow_one] using
      (innerMorseInnerWeight_piece_bounds (a := a) (γ := γ) (σ := 1)
        S.chain.index K ha hγ (by norm_num) hN hNa (P.chain K)
        A.leftWall A.rightWall p hx).2
  have hbound := A.dirichlet_localized_coefficient_bound P.geometry.2.2.1.1
    (innerMorseInnerLocalizedWeight S.chain.index K a γ (P.chain K) A 37)
    (fun x => (innerMorseInnerWeight S.chain.index K a γ
      (P.chain K) A.leftWall A.rightWall x)⁻¹)
    (innerMorseInnerLocalizedWeight_measurable S.chain.index K a γ (P.chain K) A 37)
    (innerMorseInnerWeight_measurable S.chain.index K a γ
      (P.chain K) A.leftWall A.rightWall).inv
    (innerMorseInnerWeightBound S.chain.index K a γ (P.chain K) A)
    (innerMorseInnerWeightBound S.chain.index K a γ (P.chain K) A)
    (innerMorseInnerLocalizedWeight_abs_le S.chain.index K a γ (P.chain K) A
      (by norm_num : (0 : ℝ) ≤ 37))
    (innerMorseInnerWeight_inv_abs_le S.chain.index K a γ (P.chain K) A)
    (innerMorseInnerPieceIndex S.chain.index K) S.chain.index
    (fun p => (innerMorseInnerPieceIndex_bounds S.chain.index K p).1)
    (by rw [innerMorseInnerPieceIndex_model, innerMorseInnerModelIndex_center])
    (innerMorseInnerPieceBase S.chain.index K a γ 1)
    (innerMorseInnerPieceBase_pos S.chain.index K a γ 1)
    (innerMorseInnerPieceBase_center S.chain.index K a γ 1)
    hlocalW hlocalV (P.dirichletConstant_nonneg CC CM)
    (P.actualChain_piece_dirichlet_bound hCentralFamily hMorseFamily hX hsupport
      K q hq hband hCC hCM)
  rw [innerMorseInnerSupportedWeightEquiv_symm_toCLM]
  simpa only [innerMorseInnerSupportedLocalizedWeight, innerRadialSupportedMultiplier, A] using
    hbound

/-- Both signs of the same canonical weight have the coarse cost of
the largest band coefficient. The operator dictionary is unchanged. -/
theorem dirichlet_coarse_bound
    (hCC : 0 ≤ CC) (hCM : 0 ≤ CM) (ha : 0 ≤ a)
    (hN : 4096 ≤ S.chain.index) (hNa : 64 * a ≤ (S.chain.index : ℝ))
    (γ : ℝ) (hγ : |γ| ≤ 1) (sign : Bool) :
    let A := P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
    let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
    ‖(innerHilbertWeight W sign :
          InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) →L[ℝ]
            InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))) ∘L
        A.dirichlet P.geometry.2.2.1.1 ∘L
        (innerHilbertWeight W (!sign) :
          InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) →L[ℝ]
            InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)))‖ ≤
      P.dirichletConstant CC CM * radialE (S.chain.index + K) ^ (37 : ℝ) := by
  dsimp only
  let A := P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
  let W := innerMorseInnerWeight S.chain.index K a γ (P.chain K) A.leftWall A.rightWall
  let σ : ℝ := if sign then 1 else -1
  have hσ : |σ| ≤ 1 := by cases sign <;> norm_num [σ]
  have hlocalW : ∀ p x, x ∈ Ioo ((P.chain K).left p) ((P.chain K).right p) →
      |innerSignedWeight W sign x| ≤
        sqrt (radialE (innerMorseInnerPieceIndex S.chain.index K p)) *
          innerMorseInnerPieceBase S.chain.index K a γ σ p := by
    intro p x hx
    rw [innerSignedWeight_eq_rpow]
    exact (innerMorseInnerWeight_piece_bounds (a := a) (γ := γ) (σ := σ)
      S.chain.index K ha hγ hσ hN hNa (P.chain K) A.leftWall A.rightWall p hx).1
  have hlocalV : ∀ p x, x ∈ Ioo ((P.chain K).left p) ((P.chain K).right p) →
      |innerSignedWeight W (!sign) x| ≤
        sqrt (radialE (innerMorseInnerPieceIndex S.chain.index K p)) /
          innerMorseInnerPieceBase S.chain.index K a γ σ p := by
    intro p x hx
    rw [innerSignedWeight_not_apply, innerSignedWeight_eq_rpow]
    exact (innerMorseInnerWeight_piece_bounds (a := a) (γ := γ) (σ := σ)
      S.chain.index K ha hγ hσ hN hNa (P.chain K) A.leftWall A.rightWall p hx).2
  have hbound := A.dirichlet_coarse_coefficient_bound P.geometry.2.2.1.1
    (innerSignedWeight W sign) (innerSignedWeight W (!sign))
    (innerSignedWeight_measurable W
      (innerMorseInnerWeight_measurable S.chain.index K a γ
        (P.chain K) A.leftWall A.rightWall) sign)
    (innerSignedWeight_measurable W
      (innerMorseInnerWeight_measurable S.chain.index K a γ
        (P.chain K) A.leftWall A.rightWall) (!sign))
    (innerMorseInnerWeightBound S.chain.index K a γ (P.chain K) A)
    (innerMorseInnerWeightBound S.chain.index K a γ (P.chain K) A)
    (innerMorseInnerSignedWeight_abs_le S.chain.index K a γ (P.chain K) A sign)
    (innerMorseInnerSignedWeight_abs_le S.chain.index K a γ (P.chain K) A (!sign))
    (innerMorseInnerPieceIndex S.chain.index K) (S.chain.index + K)
    (fun p => (innerMorseInnerPieceIndex_bounds S.chain.index K p).2)
    (innerMorseInnerPieceBase S.chain.index K a γ σ)
    (innerMorseInnerPieceBase_pos S.chain.index K a γ σ)
    (innerMorseInnerPieceBase_center S.chain.index K a γ σ)
    hlocalW hlocalV (P.dirichletConstant_nonneg CC CM)
    (P.actualChain_piece_dirichlet_bound hCentralFamily hMorseFamily hX hsupport
      K q hq hband hCC hCM)
  simp only [innerMorseInnerSupportedWeightEquiv_signed_toCLM]
  simpa only [innerRadialSupportedMultiplier, W, A] using hbound

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
