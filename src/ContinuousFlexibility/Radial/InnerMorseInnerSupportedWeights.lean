module

public import ContinuousFlexibility.Radial.InnerMorseInnerWeightInterfaces
public import ContinuousFlexibility.Radial.InnerMorseInnerWeightCosts
public import ContinuousFlexibility.Radial.InnerSupportedWeightProducts

/-!
# Canonical supported weights and coefficient loss on the actual chain

The spatial weight is the existing physical interpolation at the walls
of the same actual chain. Its finite bounds, including the reciprocal
bound, are chosen from the proved finite-piece estimate. No boundedness
or operator-norm assumption is needed to construct the equivalence.

The coefficient loss gives an actual contraction on the supported
source. Multiplication by the localized output weight is exactly this
loss composed with the same weight equivalence. Each construction
retains the single scalar coordinate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements

section InterfaceWeight

/-- The boundary equivalence is the positive diagonal of the existing
internal cut values. It is independent of the actual local inverses. -/
def innerMorseInnerInterfaceEquiv (N K : ℕ) (a γ : ℝ) :
    EuclideanSpace ℝ (Fin (2 * (2 * K + 1))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2 * (2 * K + 1))) :=
  innerMatrixEquiv (Matrix.diagonal (innerMorseInnerInterfaceWeight N K a γ))
    (Matrix.PosDef.isUnit (Matrix.posDef_diagonal_iff.mpr
      (innerMorseInnerInterfaceWeight_pos N K a γ)))

theorem innerMorseInnerInterfaceEquiv_toCLM (N K : ℕ) (a γ : ℝ) :
    (innerMorseInnerInterfaceEquiv N K a γ :
      EuclideanSpace ℝ (Fin (2 * (2 * K + 1))) →L[ℝ]
        EuclideanSpace ℝ (Fin (2 * (2 * K + 1)))) =
      innerBoundaryDiagonal (innerMorseInnerInterfaceWeight N K a γ) :=
  innerMatrixEquiv_toCLM
    (Matrix.diagonal (innerMorseInnerInterfaceWeight N K a γ))
    (Matrix.PosDef.isUnit (Matrix.posDef_diagonal_iff.mpr
      (innerMorseInnerInterfaceWeight_pos N K a γ)))

theorem innerMorseInnerInterfaceEquiv_signed_inverse_toCLM
    (N K : ℕ) (a γ : ℝ) (sign : Bool) :
    (innerHilbertWeight (innerMorseInnerInterfaceEquiv N K a γ) (!sign) :
      EuclideanSpace ℝ (Fin (2 * (2 * K + 1))) →L[ℝ]
        EuclideanSpace ℝ (Fin (2 * (2 * K + 1)))) =
      innerBoundaryDiagonal
        (fun i => (innerSignedWeight (innerMorseInnerInterfaceWeight N K a γ) sign i)⁻¹) :=
  innerMatrixEquiv_signed_inverse_toCLM
    (innerMorseInnerInterfaceWeight N K a γ)
    (innerMorseInnerInterfaceWeight_pos N K a γ) sign

end InterfaceWeight

section ActualWeight

variable {D : ReferenceData} (N K : ℕ) (a γ : ℝ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  {bordered : Bool} {j : ℝ} {central : Fin (2 * (2 * K + 1) + 1)}
  {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

/-- One auxiliary finite bound controls the actual weight and its
reciprocal. It is used only to construct their continuous operators. -/
def innerMorseInnerWeightBound : ℝ :=
  Classical.choose
    (innerMorseInnerWeight_finite_bounds N K a γ G C.leftWall C.rightWall)

theorem innerMorseInnerWeightBound_spec :
    1 ≤ innerMorseInnerWeightBound N K a γ G C ∧
      ∀ x, |innerMorseInnerWeight N K a γ G C.leftWall C.rightWall x| ≤
          innerMorseInnerWeightBound N K a γ G C ∧
        |(innerMorseInnerWeight N K a γ G C.leftWall C.rightWall x)⁻¹| ≤
          innerMorseInnerWeightBound N K a γ G C :=
  Classical.choose_spec
    (innerMorseInnerWeight_finite_bounds N K a γ G C.leftWall C.rightWall)

theorem innerMorseInnerWeightBound_nonneg :
    0 ≤ innerMorseInnerWeightBound N K a γ G C :=
  zero_le_one.trans (innerMorseInnerWeightBound_spec N K a γ G C).1

theorem innerMorseInnerWeight_abs_le (x : ℝ) :
    |innerMorseInnerWeight N K a γ G C.leftWall C.rightWall x| ≤
      innerMorseInnerWeightBound N K a γ G C :=
  ((innerMorseInnerWeightBound_spec N K a γ G C).2 x).1

theorem innerMorseInnerWeight_inv_abs_le (x : ℝ) :
    |(innerMorseInnerWeight N K a γ G C.leftWall C.rightWall x)⁻¹| ≤
      innerMorseInnerWeightBound N K a γ G C :=
  ((innerMorseInnerWeightBound_spec N K a γ G C).2 x).2

theorem innerMorseInnerSignedWeight_abs_le (sign : Bool) (x : ℝ) :
    |innerSignedWeight
        (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall) sign x| ≤
      innerMorseInnerWeightBound N K a γ G C := by
  simpa only [ite_self] using
    innerSignedWeight_abs_le
      (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall)
      (innerMorseInnerWeightBound N K a γ G C)
      (innerMorseInnerWeightBound N K a γ G C)
      (innerMorseInnerWeight_abs_le N K a γ G C)
      (innerMorseInnerWeight_inv_abs_le N K a γ G C) sign x

/-- The same actual weight and reciprocal on the genuine supported
Hilbert source, with no extra global boundedness input. -/
def innerMorseInnerSupportedWeightEquiv :
    InnerRadialPhysicalSource D G bordered ≃L[ℝ]
      InnerRadialPhysicalSource D G bordered :=
  innerSupportedWeightEquiv (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerWeight_measurable N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerWeight_pos N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerWeightBound N K a γ G C)
    (innerMorseInnerWeightBound N K a γ G C)
    (innerMorseInnerWeight_abs_le N K a γ G C)
    (innerMorseInnerWeight_inv_abs_le N K a γ G C)

theorem innerMorseInnerSupportedWeightEquiv_toCLM :
    (innerMorseInnerSupportedWeightEquiv N K a γ G C :
      InnerRadialPhysicalSource D G bordered →L[ℝ]
        InnerRadialPhysicalSource D G bordered) =
      innerSupportedWeightMultiplier (radialHilbertMeasure D)
        (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
        (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall)
        (innerMorseInnerWeight_measurable N K a γ G C.leftWall C.rightWall)
        (innerMorseInnerWeightBound N K a γ G C)
        (innerMorseInnerWeight_abs_le N K a γ G C) :=
  innerSupportedWeightEquiv_toCLM (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerWeight_measurable N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerWeight_pos N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerWeightBound N K a γ G C)
    (innerMorseInnerWeightBound N K a γ G C)
    (innerMorseInnerWeight_abs_le N K a γ G C)
    (innerMorseInnerWeight_inv_abs_le N K a γ G C)

theorem innerMorseInnerSupportedWeightEquiv_symm_toCLM :
    ((innerMorseInnerSupportedWeightEquiv N K a γ G C).symm :
      InnerRadialPhysicalSource D G bordered →L[ℝ]
        InnerRadialPhysicalSource D G bordered) =
      innerSupportedWeightMultiplier (radialHilbertMeasure D)
        (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
        (fun x => (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall x)⁻¹)
        (innerMorseInnerWeight_measurable N K a γ G C.leftWall C.rightWall).inv
        (innerMorseInnerWeightBound N K a γ G C)
        (innerMorseInnerWeight_inv_abs_le N K a γ G C) :=
  innerSupportedWeightEquiv_symm_toCLM (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerWeight_measurable N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerWeight_pos N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerWeightBound N K a γ G C)
    (innerMorseInnerWeightBound N K a γ G C)
    (innerMorseInnerWeight_abs_le N K a γ G C)
    (innerMorseInnerWeight_inv_abs_le N K a γ G C)

theorem innerMorseInnerSupportedWeightEquiv_selfAdjoint :
    IsSelfAdjoint (innerMorseInnerSupportedWeightEquiv N K a γ G C :
      InnerRadialPhysicalSource D G bordered →L[ℝ]
        InnerRadialPhysicalSource D G bordered) := by
  rw [innerMorseInnerSupportedWeightEquiv_toCLM]
  exact innerSupportedWeightMultiplier_selfAdjoint (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerWeight_measurable N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerWeightBound N K a γ G C)
    (innerMorseInnerWeight_abs_le N K a γ G C)

/-- Both signs of this one equivalence are the signed actual field
multipliers used by the Poisson estimate. -/
theorem innerMorseInnerSupportedWeightEquiv_signed_toCLM (sign : Bool) :
    (innerHilbertWeight (innerMorseInnerSupportedWeightEquiv N K a γ G C) sign :
      InnerRadialPhysicalSource D G bordered →L[ℝ]
        InnerRadialPhysicalSource D G bordered) =
      innerSupportedWeightMultiplier (radialHilbertMeasure D)
        (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
        (innerSignedWeight
          (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall) sign)
        (innerSignedWeight_measurable
          (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall)
          (innerMorseInnerWeight_measurable N K a γ G C.leftWall C.rightWall) sign)
        (innerMorseInnerWeightBound N K a γ G C)
        (innerMorseInnerSignedWeight_abs_le N K a γ G C sign) := by
  simpa only [innerMorseInnerSupportedWeightEquiv, ite_self] using
    innerSupportedWeightEquiv_signed_toCLM (radialHilbertMeasure D)
      (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
      (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall)
      (innerMorseInnerWeight_measurable N K a γ G C.leftWall C.rightWall)
      (innerMorseInnerWeight_pos N K a γ G C.leftWall C.rightWall)
      (innerMorseInnerWeightBound N K a γ G C)
      (innerMorseInnerWeightBound N K a γ G C)
      (innerMorseInnerWeight_abs_le N K a γ G C)
      (innerMorseInnerWeight_inv_abs_le N K a γ G C) sign

end ActualWeight

section CoefficientLoss

variable {D : ReferenceData} (N K : ℕ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1))) (bordered : Bool)

/-- The actual coefficient loss on the supported source. Its scalar
coordinate remains the identity. -/
def innerMorseInnerSupportedLoss (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    InnerRadialPhysicalSource D G bordered →L[ℝ]
      InnerRadialPhysicalSource D G bordered :=
  innerSupportedWeightMultiplier (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (innerMorseInnerLoss N K G ℓ) (innerMorseInnerLoss_measurable N K G ℓ) 1
    (innerMorseInnerLoss_le_one N K G hℓ)

theorem innerMorseInnerSupportedLoss_norm_le_one (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ‖innerMorseInnerSupportedLoss N K G bordered ℓ hℓ‖ ≤ 1 :=
  norm_innerSupportedCoefficientLoss_le_one (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (innerMorseInnerLoss N K G ℓ) (innerMorseInnerLoss_measurable N K G ℓ)
    (innerMorseInnerLoss_le_one N K G hℓ)

theorem innerMorseInnerSupportedLoss_selfAdjoint (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    IsSelfAdjoint (innerMorseInnerSupportedLoss N K G bordered ℓ hℓ) :=
  innerSupportedWeightMultiplier_selfAdjoint (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (innerMorseInnerLoss N K G ℓ) (innerMorseInnerLoss_measurable N K G ℓ) 1
    (innerMorseInnerLoss_le_one N K G hℓ)

theorem innerMorseInnerSupportedLoss_scalar (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (F : InnerRadialPhysicalSource D G bordered) :
    (innerMorseInnerSupportedLoss N K G bordered ℓ hℓ F).val.snd = F.val.snd :=
  innerSupportedWeightMultiplier_scalar (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (innerMorseInnerLoss N K G ℓ) (innerMorseInnerLoss_measurable N K G ℓ) 1
    (innerMorseInnerLoss_le_one N K G hℓ) F

end CoefficientLoss

section LocalizedWeight

variable {D : ReferenceData} (N K : ℕ) (a γ : ℝ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  {bordered : Bool} {j : ℝ} {central : Fin (2 * (2 * K + 1) + 1)}
  {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

/-- The localized output weight is the same spatial weight multiplied
by the prescribed coefficient loss. -/
def innerMorseInnerLocalizedWeight (ℓ : ℝ) : ℝ → ℝ :=
  fun x => innerMorseInnerWeight N K a γ G C.leftWall C.rightWall x *
    innerMorseInnerLoss N K G ℓ x

theorem innerMorseInnerLocalizedWeight_eq_coefficient (ℓ x : ℝ) :
    innerMorseInnerLocalizedWeight N K a γ G C ℓ x =
      innerMorseInnerWeight N K a γ G C.leftWall C.rightWall x *
        (innerMorseInnerCoefficient N K G x / radialE N) ^ (-ℓ) := by
  simp only [innerMorseInnerLocalizedWeight, innerMorseInnerLoss_eq_coefficient]

theorem innerMorseInnerLocalizedWeight_measurable (ℓ : ℝ) :
    Measurable (innerMorseInnerLocalizedWeight N K a γ G C ℓ) :=
  (innerMorseInnerWeight_measurable N K a γ G C.leftWall C.rightWall).mul
    (innerMorseInnerLoss_measurable N K G ℓ)

theorem innerMorseInnerLocalizedWeight_pos (ℓ x : ℝ) :
    0 < innerMorseInnerLocalizedWeight N K a γ G C ℓ x :=
  mul_pos (innerMorseInnerWeight_pos N K a γ G C.leftWall C.rightWall x)
    (innerMorseInnerLoss_pos N K G ℓ x)

theorem innerMorseInnerLocalizedWeight_abs_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (x : ℝ) :
    |innerMorseInnerLocalizedWeight N K a γ G C ℓ x| ≤
      innerMorseInnerWeightBound N K a γ G C := by
  calc
    |innerMorseInnerLocalizedWeight N K a γ G C ℓ x| =
        |innerMorseInnerWeight N K a γ G C.leftWall C.rightWall x| *
          |innerMorseInnerLoss N K G ℓ x| := abs_mul _ _
    _ ≤ innerMorseInnerWeightBound N K a γ G C * 1 :=
      mul_le_mul (innerMorseInnerWeight_abs_le N K a γ G C x)
        (innerMorseInnerLoss_le_one N K G hℓ x) (abs_nonneg _)
        (innerMorseInnerWeightBound_nonneg N K a γ G C)
    _ = innerMorseInnerWeightBound N K a γ G C := mul_one _

def innerMorseInnerSupportedLocalizedWeight (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    InnerRadialPhysicalSource D G bordered →L[ℝ]
      InnerRadialPhysicalSource D G bordered :=
  innerSupportedWeightMultiplier (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (innerMorseInnerLocalizedWeight N K a γ G C ℓ)
    (innerMorseInnerLocalizedWeight_measurable N K a γ G C ℓ)
    (innerMorseInnerWeightBound N K a γ G C)
    (innerMorseInnerLocalizedWeight_abs_le N K a γ G C hℓ)

/-- The prescribed output weight is exactly the loss operator after
the same actual weight equivalence. This also identifies its action
on the sole scalar coordinate. -/
theorem innerMorseInnerSupportedLocalizedWeight_eq_loss_comp (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    innerMorseInnerSupportedLocalizedWeight N K a γ G C ℓ hℓ =
      innerMorseInnerSupportedLoss N K G bordered ℓ hℓ ∘L
        (innerMorseInnerSupportedWeightEquiv N K a γ G C :
          InnerRadialPhysicalSource D G bordered →L[ℝ]
            InnerRadialPhysicalSource D G bordered) := by
  rw [innerMorseInnerSupportedWeightEquiv_toCLM]
  unfold innerMorseInnerSupportedLocalizedWeight innerMorseInnerSupportedLoss
  have hproduct := innerSupportedWeightMultiplier_product (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (innerMorseInnerLoss N K G ℓ)
    (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall)
    (innerMorseInnerLoss_measurable N K G ℓ)
    (innerMorseInnerWeight_measurable N K a γ G C.leftWall C.rightWall)
    1 (innerMorseInnerWeightBound N K a γ G C) zero_le_one
    (innerMorseInnerWeightBound_nonneg N K a γ G C)
    (innerMorseInnerLoss_le_one N K G hℓ)
    (innerMorseInnerWeight_abs_le N K a γ G C)
  refine Eq.trans ?_ hproduct
  apply innerSupportedWeightMultiplier_congr
  intro x
  dsimp only [innerMorseInnerLocalizedWeight]
  exact mul_comm _ _

end LocalizedWeight

end ContinuousFlexibility.Radial
