import ContinuousFlexibility.Radial.InnerSupportedWeights
import ContinuousFlexibility.Radial.InnerChainDiagonal

/-!
# Unit weights on the original physical and boundary spaces

The existing multipliers and boundary restrictions become the identity
when their actual weight is one. These equalities are shared by the
unweighted specialization and the local weighted estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

/-- Constant cut weights have constant two-endpoint restrictions. -/
theorem innerChainScalarRestriction_one (n : ℕ) (p : Fin (n + 1)) :
    innerChainScalarRestriction n p (fun _ => (1 : ℝ)) 1 = fun _ => 1 := by
  funext i
  unfold innerChainScalarRestriction
  split_ifs <;> rfl

/-- The unit diagonal is the identity on the same Euclidean cut space. -/
theorem innerBoundaryDiagonal_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    innerBoundaryDiagonal (fun _ : ι => (1 : ℝ)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply PiLp.ext
  intro i
  simp only [innerBoundaryDiagonal_apply, ContinuousLinearMap.id_apply, one_mul]

section Physical

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Unit multiplication fixes both the physical field and its scalar. -/
theorem innerBorderFieldMap_weight_one :
    innerBorderFieldMap μ (innerWeightMultiplier μ (fun _ => (1 : ℝ))
      measurable_const 1 (fun _ => by norm_num)) =
        ContinuousLinearMap.id ℝ (InnerBorderL2 μ) := by
  apply ContinuousLinearMap.ext
  intro F
  rw [ContinuousLinearMap.id_apply, innerBorderFieldMap_apply]
  have hfield : innerWeightMultiplier μ (fun _ => (1 : ℝ))
      measurable_const 1 (fun _ => by norm_num) F.fst = F.fst := by
    apply Lp.ext
    filter_upwards [innerWeightMultiplier_ae μ (fun _ => (1 : ℝ))
      measurable_const 1 (fun _ => by norm_num) F.fst] with x hx
    simpa only [one_mul] using hx
  rw [hfield]
  exact WithLp.toLp_ofLp 2 F

/-- The constant physical weight is exactly the identity on the original
supported space, including its scalar coordinate. -/
theorem innerSupportedWeightMultiplier_one (s : Set α) (hs : MeasurableSet s)
    (bordered : Bool) :
    innerSupportedWeightMultiplier μ s hs bordered (fun _ => (1 : ℝ))
      measurable_const 1 (fun _ => by norm_num) =
        ContinuousLinearMap.id ℝ ↥(innerSupportedAdmissibleSource μ s bordered) := by
  apply ContinuousLinearMap.ext
  intro F
  apply Subtype.ext
  rw [ContinuousLinearMap.id_apply, innerSupportedWeightMultiplier_apply,
    innerBorderFieldMap_apply]
  have hfield : innerWeightMultiplier μ (fun _ => (1 : ℝ))
      measurable_const 1 (fun _ => by norm_num) F.val.fst = F.val.fst := by
    apply Lp.ext
    filter_upwards [innerWeightMultiplier_ae μ (fun _ => (1 : ℝ))
      measurable_const 1 (fun _ => by norm_num) F.val.fst] with x hx
    simpa only [one_mul] using hx
  rw [hfield]
  exact WithLp.toLp_ofLp 2 F.val

end Physical

end ContinuousFlexibility.Radial
