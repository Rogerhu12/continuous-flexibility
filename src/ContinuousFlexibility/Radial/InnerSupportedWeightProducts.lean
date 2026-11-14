module

public import ContinuousFlexibility.Radial.InnerSupportedWeights
public import ContinuousFlexibility.Radial.InnerLocalizedInverseBound

/-!
# Products of actual weights on the supported physical source

The coefficient loss acts on the output of the same physical inverse.
These identities identify that composition with multiplication by the
pointwise product, including the unchanged scalar coordinate. The
auxiliary bounds used to construct a multiplier do not change its value.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (s : Set α) (hs : MeasurableSet s) (bordered : Bool)

/-- Pointwise equal weights give the same actual operator, independently
of the bounds used to construct their bounded multipliers. -/
theorem innerSupportedWeightMultiplier_congr
    (W V : α → ℝ) (hW : Measurable W) (hV : Measurable V)
    (C D : ℝ) (hWC : ∀ x, |W x| ≤ C) (hVD : ∀ x, |V x| ≤ D)
    (hWV : ∀ x, W x = V x) :
    innerSupportedWeightMultiplier μ s hs bordered W hW C hWC =
      innerSupportedWeightMultiplier μ s hs bordered V hV D hVD := by
  apply ContinuousLinearMap.ext
  intro F
  apply Subtype.ext
  rw [innerSupportedWeightMultiplier_apply, innerSupportedWeightMultiplier_apply,
    innerBorderFieldMap_apply, innerBorderFieldMap_apply]
  apply congrArg (fun f : Lp ℝ 2 μ =>
    (WithLp.toLp 2 (f, F.val.snd) : InnerBorderL2 μ))
  apply Lp.ext
  filter_upwards [innerWeightMultiplier_ae μ W hW C hWC F.val.fst,
    innerWeightMultiplier_ae μ V hV D hVD F.val.fst] with x hleft hright
  rw [hleft, hright, hWV x]

/-- Multiplication by the product is exactly composition on the genuine
supported source; no ambient-space norm comparison is required. -/
theorem innerSupportedWeightMultiplier_product
    (W V : α → ℝ) (hW : Measurable W) (hV : Measurable V)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hWC : ∀ x, |W x| ≤ C) (hVD : ∀ x, |V x| ≤ D) :
    innerSupportedWeightMultiplier μ s hs bordered
        (fun x => W x * V x) (hW.mul hV) (C * D)
        (fun x => (abs_mul _ _).trans_le
          (mul_le_mul (hWC x) (hVD x) (abs_nonneg _) hC)) =
      innerSupportedWeightMultiplier μ s hs bordered W hW C hWC ∘L
        innerSupportedWeightMultiplier μ s hs bordered V hV D hVD := by
  apply ContinuousLinearMap.ext
  intro F
  apply Subtype.ext
  simp only [ContinuousLinearMap.comp_apply, innerSupportedWeightMultiplier_apply]
  rw [innerWeightMultiplier_product μ W V hW hV C D hC hD hWC hVD,
    innerBorderFieldMap_comp, ContinuousLinearMap.comp_apply]

end ContinuousFlexibility.Radial
