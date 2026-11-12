import ContinuousFlexibility.Radial.InnerSupportedWeights
import ContinuousFlexibility.Radial.InnerChainDiagonal

/-!
# Unit weights on the actual inner source and cut spaces

These identities remove constant physical weights through the public
application lemmas. The scalar coordinate and supported source are preserved.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory Filter

theorem innerChainScalarRestriction_one (n : ℕ) (p : Fin (n + 1)) :
    innerChainScalarRestriction n p (fun _ => 1) 1 = fun _ => 1 := by
  funext i
  simp [innerChainScalarRestriction]

theorem innerBoundaryDiagonal_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    innerBoundaryDiagonal (fun _ : ι => (1 : ℝ)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply PiLp.ext
  intro i
  simp only [innerBoundaryDiagonal_apply, ContinuousLinearMap.id_apply, one_mul]

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem innerWeightMultiplier_one (hW : Measurable (fun _ : α => (1 : ℝ)))
    (C : ℝ) (hbound : ∀ _ : α, |(1 : ℝ)| ≤ C) :
    innerWeightMultiplier μ (fun _ => 1) hW C hbound =
      ContinuousLinearMap.id ℝ (Lp ℝ 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [innerWeightMultiplier_ae μ (fun _ => 1) hW C hbound f] with x hx
  simpa only [ContinuousLinearMap.id_apply, one_mul] using hx

theorem innerBorderFieldMap_weight_one
    (hW : Measurable (fun _ : α => (1 : ℝ)))
    (C : ℝ) (hbound : ∀ _ : α, |(1 : ℝ)| ≤ C) :
    innerBorderFieldMap μ (innerWeightMultiplier μ (fun _ => 1) hW C hbound) =
      ContinuousLinearMap.id ℝ (InnerBorderL2 μ) := by
  rw [innerWeightMultiplier_one]
  apply ContinuousLinearMap.ext
  intro F
  simp only [innerBorderFieldMap_apply, ContinuousLinearMap.id_apply]
  exact WithLp.toLp_ofLp 2 F

theorem innerSupportedWeightMultiplier_one (s : Set α) (hs : MeasurableSet s)
    (bordered : Bool) (hW : Measurable (fun _ : α => (1 : ℝ)))
    (C : ℝ) (hbound : ∀ _ : α, |(1 : ℝ)| ≤ C) :
    innerSupportedWeightMultiplier μ s hs bordered (fun _ => 1) hW C hbound =
      ContinuousLinearMap.id ℝ ↥(innerSupportedAdmissibleSource μ s bordered) := by
  apply ContinuousLinearMap.ext
  intro F
  apply Subtype.ext
  simp only [innerSupportedWeightMultiplier_apply, innerBorderFieldMap_weight_one,
    ContinuousLinearMap.id_apply]

end ContinuousFlexibility.Radial
