module

public import ContinuousFlexibility.Radial.InnerSelectedMorseEstimates
public import ContinuousFlexibility.Radial.InnerMorseInnerSupportedWeights
public import ContinuousFlexibility.Radial.InnerMorseInnerInterfaceEstimates

/-!
# Uniform weighted estimates for the selected physical models

The central and tail cases use the same model array and the actual
piecewise multiplier at its stored physical walls. The constants do
not depend on the number of retained cells, the even frequency, or
the weight exponent. No local column bound is an input here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

def innerSelectedModelPoissonConstant : ℝ :=
  max innerMorsePoissonConstant innerCentralPoissonConstant

theorem innerSelectedModelPoissonConstant_pos : 0 < innerSelectedModelPoissonConstant :=
  innerMorsePoissonConstant_pos.trans_le (le_max_left _ _)

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)
  {a CC KC CM KM η : ℝ}
  (hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η)
  (hMorseFamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
  (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀)
  (K q : ℕ) (hq : 1 ≤ q)
  (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q))

/-- The actual array inherits both weighted error signs from its one
selected central model and its original selected tail models. -/
theorem models_error_le {γ : ℝ} (hγ : |γ| ≤ 1)
    (p : Fin (2 * K + 1)) (sign : Bool) :
    ‖innerTwoCutWeightedError
      (P.models hCentralFamily hMorseFamily hX hsupport K q hq hband p).kappa
      (innerMorseInnerModelWeight S.chain.index K a γ p)
      (P.models hCentralFamily hMorseFamily hX hsupport K q hq hband p).errorMatrix sign‖ ≤ η := by
  rcases innerMorseInnerModel_cases K p with rfl | ⟨side, p, rfl⟩
  · have hw : innerMorseInnerModelWeight S.chain.index K a γ (innerMorseInnerCenter K) =
        fun _ => 1 := funext (innerMorseInnerModelWeight_center S.chain.index K a γ)
    rw [P.models_center, hw]
    exact P.centralModel_error_le hCentralFamily hX hsupport (P.chain K)
      (innerModelChainPiece (innerMorseInnerCenter K)) q hq
      (P.center_left_cut K) (P.center_right_cut K) sign
  · have hw : innerMorseInnerModelWeight S.chain.index K a γ
        (innerMorseInnerTailSlot K side p) =
        innerMorseCutWeight S.chain.index a γ side
          (innerMorseInnerTailIndex S.chain.index K side p) :=
      funext (innerMorseInnerModelWeight_tail S.chain.index K a γ side p)
    rw [P.models_tail, hw]
    exact P.tailModel_error_le hMorseFamily hsupport K q hq hband side p hγ sign

section Columns

variable (ha : 0 ≤ a) (hN : 4096 ≤ S.chain.index)
  (hNa : 64 * a ≤ (S.chain.index : ℝ)) (hCM : 0 < CM)
  (γ : ℝ) (hγ : |γ| ≤ 1)

include ha hN hNa hCM hγ

local notation "A" => P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
local notation "W" => innerMorseInnerWeight S.chain.index K a γ (P.chain K) (InnerRadialActualChain.leftWall A) (InnerRadialActualChain.rightWall A)

/-- Both signed actual weights satisfy the normalized column estimate
on every model slot. The bound is uniform in the entire finite chain. -/
theorem models_column_norm_le (sign : Bool)
    (CW : ℝ) (hWC : ∀ r, |innerSignedWeight W sign r| ≤ CW)
    (p : Fin (2 * K + 1)) (i : Fin 2) :
    ‖(innerSignedWeight (innerMorseInnerModelWeight S.chain.index K a γ p) sign i *
        Real.sqrt ((P.models hCentralFamily hMorseFamily hX hsupport K q hq hband p).kappa i))⁻¹ •
      innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) (innerSignedWeight W sign)
          (innerSignedWeight_measurable W
            (innerMorseInnerWeight_measurable S.chain.index K a γ
              (P.chain K) (A).leftWall (A).rightWall) sign) CW hWC)
        ((P.models hCentralFamily hMorseFamily hX hsupport K q hq hband p).column i)‖ ≤
          innerSelectedModelPoissonConstant / ((2 : ℝ) * q) := by
  have hj : 0 < (2 : ℝ) * q := by
    exact_mod_cast (show 0 < 2 * q by omega)
  rcases innerMorseInnerModel_cases K p with rfl | ⟨side, p, rfl⟩
  · have hmiddle : ∀ x ∈ Icc (-X₀) X₀,
        innerSignedWeight W sign (centralRadius x) = 1 := by
      intro x hx
      apply innerMorseInnerWeight_actual_signed_on_center
        S.chain.index K a γ (P.chain K) A sign
      rw [P.center_left_cut K, P.center_right_cut K]
      exact ⟨strictMono_centralRadius.monotone hx.1, strictMono_centralRadius.monotone hx.2⟩
    have hwcut : innerSignedWeight
        (innerMorseInnerModelWeight S.chain.index K a γ (innerMorseInnerCenter K)) sign i = 1 := by
      simp only [innerSignedWeight, innerMorseInnerModelWeight_center, inv_one, ite_self]
    rw [hwcut, one_mul, P.models_center]
    exact (P.centralModel_column_norm_le hCentralFamily hX hsupport (P.chain K)
      (innerModelChainPiece (innerMorseInnerCenter K)) q hq
      (P.center_left_cut K) (P.center_right_cut K)
      (innerSignedWeight W sign)
      (innerSignedWeight_measurable W
        (innerMorseInnerWeight_measurable S.chain.index K a γ
          (P.chain K) (A).leftWall (A).rightWall) sign) CW hWC hmiddle i).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) hj.le)
  · let M := P.tailModel hMorseFamily hsupport K q hq hband side p
    have hp : (A).piece (innerModelChainPiece (innerMorseInnerTailSlot K side p)) = Sum.inl M := by
      rw [P.actualChain_model, P.models_tail]
    have hinterp : ∀ r ∈
        Icc ((P.chain K).left (innerModelChainPiece (innerMorseInnerTailSlot K side p)))
          ((P.chain K).right (innerModelChainPiece (innerMorseInnerTailSlot K side p))),
        innerSignedWeight W sign r =
          (innerMorseInterpolatedWeight S.chain.index a γ side
            (innerMorseInnerTailIndex S.chain.index K side p) M.leftWall M.rightWall r) ^
              (if sign then (1 : ℝ) else -1) := by
      intro r hr
      exact innerMorseInnerWeight_actual_signed_on_tail
        S.chain.index K a γ (P.chain K) A side p M hp sign hr
    have hsign : |if sign then (1 : ℝ) else -1| ≤ 1 := by
      cases sign <;> norm_num
    have hwcut : innerSignedWeight
        (innerMorseInnerModelWeight S.chain.index K a γ (innerMorseInnerTailSlot K side p))
          sign i =
        (innerMorseCutWeight S.chain.index a γ side
          (innerMorseInnerTailIndex S.chain.index K side p) i) ^
            (if sign then (1 : ℝ) else -1) := by
      rw [innerSignedWeight_eq_rpow, innerMorseInnerModelWeight_tail]
    rw [hwcut, P.models_tail]
    exact (P.tailModel_column_norm_le hMorseFamily hsupport K q hq hband side p
      ha hN hNa hCM γ (if sign then 1 else -1) hγ hsign
      (innerSignedWeight W sign)
      (innerSignedWeight_measurable W
        (innerMorseInnerWeight_measurable S.chain.index K a γ
          (P.chain K) (A).leftWall (A).rightWall) sign) CW hWC hinterp i).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) hj.le)

end Columns

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
