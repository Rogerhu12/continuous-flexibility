import ContinuousFlexibility.Radial.InnerCouplingBound
import ContinuousFlexibility.Radial.InnerPiecewiseWeights
import ContinuousFlexibility.Radial.InnerCoefficientCosts

/-!
# The localized coefficient loss does not enlarge the Poisson correction

The loss multiplier has norm at most one. Applying it to the same Schur
inverse therefore leaves the frequency-decaying correction bound intact.
Only the local Dirichlet part pays the fixed coefficient exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory

section ActualMultipliers

variable {α : Type*} [MeasurableSpace α]

/-- Actual multiplication of two bounded weights is composition on L². -/
theorem innerWeightMultiplier_product (μ : Measure α)
    (W V : α → ℝ) (hW : Measurable W) (hV : Measurable V)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hWC : ∀ x, |W x| ≤ C) (hVD : ∀ x, |V x| ≤ D) :
    innerWeightMultiplier μ (fun x => W x * V x) (hW.mul hV) (C * D)
      (fun x => (abs_mul _ _).trans_le
        (mul_le_mul (hWC x) (hVD x) (abs_nonneg _) hC)) =
      innerWeightMultiplier μ W hW C hWC ∘L innerWeightMultiplier μ V hV D hVD := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [innerWeightMultiplier_ae μ (fun x => W x * V x) (hW.mul hV) (C * D)
      (fun x => (abs_mul _ _).trans_le
        (mul_le_mul (hWC x) (hVD x) (abs_nonneg _) hC)) f,
    innerWeightMultiplier_ae μ W hW C hWC (innerWeightMultiplier μ V hV D hVD f),
    innerWeightMultiplier_ae μ V hV D hVD f] with x hprod houter hinner
  change innerWeightMultiplier μ (fun x => W x * V x) (hW.mul hV) (C * D) _ f x =
    innerWeightMultiplier μ W hW C hWC (innerWeightMultiplier μ V hV D hVD f) x
  rw [hprod, houter, hinner]
  ring

end ActualMultipliers

section HilbertBound

variable {H B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

/-- The same inverse has the localized bound, with the loss multiplier
acting only on the output. The two Poisson signs are both used through
the actual opposite-sign adjoint factorization. -/
theorem innerGluedInverse_localized_bound
    (W : H ≃L[ℝ] H) (Ω : B ≃L[ℝ] B) (L D : H →L[ℝ] H)
    (T : B →L[ℝ] H) (J K : B →L[ℝ] B) (N : Bool → B →L[ℝ] B)
    (hW : IsSelfAdjoint (W : H →L[ℝ] H))
    (hΩ : IsSelfAdjoint (Ω : B →L[ℝ] B)) (hJ : IsSelfAdjoint J)
    (hfactor : ∀ sign : Bool,
      (innerHilbertWeight Ω sign : B →L[ℝ] B) ∘L K ∘L
        (innerHilbertWeight Ω (!sign) : B →L[ℝ] B) = J ∘L N sign ∘L J)
    {C j d : ℝ} (hC : 0 ≤ C) (hj : 0 < j)
    (hP : ∀ sign : Bool, ‖innerWeightedPoisson W Ω T J sign‖ ≤ C / j)
    (hN : ∀ sign : Bool, ‖N sign‖ ≤ 2) (hL : ‖L‖ ≤ 1) (sign : Bool)
    (hD : ‖L ∘L ((innerHilbertWeight W sign : H →L[ℝ] H) ∘L D ∘L
      (innerHilbertWeight W (!sign) : H →L[ℝ] H))‖ ≤ d) :
    ‖L ∘L ((innerHilbertWeight W sign : H →L[ℝ] H) ∘L innerGluedInverse D T K ∘L
      (innerHilbertWeight W (!sign) : H →L[ℝ] H))‖ ≤ d + 2 * C ^ 2 / j ^ 2 := by
  have hcorrection := innerCoupling_weighted_bound W Ω T J K N hW hΩ hJ hfactor
    hC hj hP hN sign
  have hcorrectionLoss :
      ‖L ∘L ((innerHilbertWeight W sign : H →L[ℝ] H) ∘L innerCouplingCorrection T K ∘L
        (innerHilbertWeight W (!sign) : H →L[ℝ] H))‖ ≤ 2 * C ^ 2 / j ^ 2 := by
    calc
      _ ≤ ‖L‖ * ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L innerCouplingCorrection T K ∘L
          (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (2 * C ^ 2 / j ^ 2) :=
        mul_le_mul hL hcorrection (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  simp only [innerGluedInverse, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  exact (norm_add_le _ _).trans (add_le_add hD hcorrectionLoss)

end HilbertBound

end ContinuousFlexibility.Radial
