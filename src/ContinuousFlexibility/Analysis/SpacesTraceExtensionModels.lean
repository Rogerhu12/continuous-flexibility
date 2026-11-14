module

public import ContinuousFlexibility.Analysis.SpacesTraceExtension

/-!
# The split tame trace between the exact models

The concrete interpolating packets define a continuous linear right inverse
on the even circle subspace. Both maps satisfy grading estimates with fixed
loss three, for every exact choice of the physical and circle models.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {γ : ℝ}
variable (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
variable (hH : IsSobolevModel D T γ (S.height γ)) (hC : IsCircleModel T γ (S.circle γ))

include hD hT hH hC in
private theorem spacesEvenExtension_exists (u : EvenCircleAt S γ) :
    ∃ v : (S.height γ).Space, (S.height γ).decode v =
      spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode u.val) :=
  hH.2.2.2.2.1 _ (spacesTraceExtensionRawLinear_heightMember hD hT
    (hC.2.2.2.1 u.val) u.property)

def spacesEvenExtensionFun (u : EvenCircleAt S γ) : (S.height γ).Space :=
  Classical.choose (spacesEvenExtension_exists hD hT hH hC u)

theorem spacesEvenExtensionFun_decode (u : EvenCircleAt S γ) :
    (S.height γ).decode (spacesEvenExtensionFun hD hT hH hC u) =
      spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode u.val) :=
  Classical.choose_spec (spacesEvenExtension_exists hD hT hH hC u)

theorem spacesEvenExtensionFun_add (u v : EvenCircleAt S γ) :
    spacesEvenExtensionFun hD hT hH hC (u + v) =
      spacesEvenExtensionFun hD hT hH hC u + spacesEvenExtensionFun hD hT hH hC v := by
  apply hH.2.2.2.2.2.1
  calc
    (S.height γ).decode (spacesEvenExtensionFun hD hT hH hC (u + v)) =
        spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode (u + v).val) :=
      spacesEvenExtensionFun_decode hD hT hH hC _
    _ = spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode u.val) +
        spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode v.val) := by
      exact (congrArg (spacesTraceExtensionRawLinear hD hT γ)
        ((S.circle γ).decode.map_add u.val v.val)).trans
          ((spacesTraceExtensionRawLinear hD hT γ).map_add _ _)
    _ = (S.height γ).decode (spacesEvenExtensionFun hD hT hH hC u) +
        (S.height γ).decode (spacesEvenExtensionFun hD hT hH hC v) :=
      congrArg₂ (fun f g : PolarPoint → ℝ => f + g)
        (spacesEvenExtensionFun_decode hD hT hH hC u).symm
        (spacesEvenExtensionFun_decode hD hT hH hC v).symm
    _ = _ := ((S.height γ).decode.map_add _ _).symm

theorem spacesEvenExtensionFun_smul (c : ℝ) (u : EvenCircleAt S γ) :
    spacesEvenExtensionFun hD hT hH hC (c • u) = c • spacesEvenExtensionFun hD hT hH hC u := by
  apply hH.2.2.2.2.2.1
  calc
    (S.height γ).decode (spacesEvenExtensionFun hD hT hH hC (c • u)) =
        spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode (c • u).val) :=
      spacesEvenExtensionFun_decode hD hT hH hC _
    _ = c • spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode u.val) := by
      exact (congrArg (spacesTraceExtensionRawLinear hD hT γ)
        ((S.circle γ).decode.map_smul c u.val)).trans
          ((spacesTraceExtensionRawLinear hD hT γ).map_smul c _)
    _ = c • (S.height γ).decode (spacesEvenExtensionFun hD hT hH hC u) :=
      congrArg (fun f : PolarPoint → ℝ => c • f) (spacesEvenExtensionFun_decode hD hT hH hC u).symm
    _ = _ := ((S.height γ).decode.map_smul c _).symm

def spacesEvenExtensionLinear : EvenCircleAt S γ →ₗ[ℝ] (S.height γ).Space where
  toFun := spacesEvenExtensionFun hD hT hH hC
  map_add' := spacesEvenExtensionFun_add hD hT hH hC
  map_smul' := spacesEvenExtensionFun_smul hD hT hH hC

theorem spacesEvenExtensionLinear_decode (u : EvenCircleAt S γ) :
    (S.height γ).decode (spacesEvenExtensionLinear hD hT hH hC u) =
      spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode u.val) :=
  spacesEvenExtensionFun_decode hD hT hH hC u

theorem spacesEvenExtensionLinear_isTame :
    IsTameLinear (evenCircleGradingAt S γ) (S.height γ).grading
      (spacesEvenExtensionLinear hD hT hH hC) 3 0 := by
  obtain ⟨constants, hnonneg, hbound⟩ := spacesTraceExtensionRawLinear_norm_bound hD hT
  intro s _
  have hsum : 0 ≤ ∑ i ∈ Finset.Iic s, constants i :=
    Finset.sum_nonneg (fun i _ => hnonneg i)
  refine ⟨⟨∑ i ∈ Finset.Iic s, constants i, hsum⟩, fun u => ?_⟩
  apply (gradedSeminorm_le_iff _ _ s _ (mul_nonneg hsum (apply_nonneg _ _))).mpr
  intro i hi
  have hn := hbound γ ((S.circle γ).decode u.val) (hC.2.2.2.1 u.val) i
  have hCi : constants i ≤ ∑ j ∈ Finset.Iic s, constants j :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_Iic.mpr hi)
  have hout : ‖(spacesEvenExtensionLinear hD hT hH hC u).val i‖ =
      physicalNorm T γ i (spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode u.val)) :=
    (hH.2.2.2.2.2.2.2 _ i).trans
      (congrArg (physicalNorm T γ i) (spacesEvenExtensionLinear_decode hD hT hH hC u))
  calc
    ‖(spacesEvenExtensionLinear hD hT hH hC u).val i‖ =
        physicalNorm T γ i (spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode u.val)) := hout
    _ ≤ constants i * circleNorm T γ (i + 3) ((S.circle γ).decode u.val) := hn
    _ = constants i * ‖u.val.val (i + 3)‖ :=
      congrArg (constants i * ·) (hC.2.2.2.2.2.2.2 u.val (i + 3)).symm
    _ ≤ (∑ j ∈ Finset.Iic s, constants j) * evenCircleGradingAt S γ (s + 3) u :=
      mul_le_mul hCi (norm_coordinate_le_graded _ _ (by omega) u.val) (norm_nonneg _) hsum

theorem spacesEvenCircle_withSeminorms : WithSeminorms (evenCircleGradingAt S γ) :=
  (evenCircleSubmoduleAt S γ).subtype.withSeminorms_induced (withSeminorms_graded _ _)

/-- The actual continuous linear interpolating extension on the even circle subspace. -/
def spacesEvenExtensionMap : EvenCircleAt S γ →L[ℝ] (S.height γ).Space :=
  (spacesEvenExtensionLinear_isTame hD hT hH hC).toContinuousLinearMap
    spacesEvenCircle_withSeminorms (withSeminorms_graded _ _) (gradedSeminorm_monotone _ _)

theorem spacesEvenExtensionMap_decode (u : EvenCircleAt S γ) :
    (S.height γ).decode (spacesEvenExtensionMap hD hT hH hC u) =
      spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode u.val) :=
  spacesEvenExtensionLinear_decode hD hT hH hC u

theorem spacesEvenExtensionMap_isTame :
    IsTameLinear (evenCircleGradingAt S γ) (S.height γ).grading
      (spacesEvenExtensionMap hD hT hH hC).toLinearMap 3 0 :=
  spacesEvenExtensionLinear_isTame hD hT hH hC

theorem spacesEvenExtensionMap_rightInverse (u : EvenCircleAt S γ) :
    spacesEvenTrace hD hT hH hC (spacesEvenExtensionMap hD hT hH hC u) = u := by
  apply Subtype.ext
  apply hC.2.2.2.2.2.1
  funext m θ
  calc
    (S.circle γ).decode (spacesEvenTrace hD hT hH hC
        (spacesEvenExtensionMap hD hT hH hC u)).val m θ =
        (S.height γ).decode (spacesEvenExtensionMap hD hT hH hC u) (T.sample m, θ) :=
      spacesEvenTrace_decode hD hT hH hC _ m θ
    _ = spacesTraceExtensionRawLinear hD hT γ ((S.circle γ).decode u.val) (T.sample m, θ) :=
      congrFun (spacesEvenExtensionMap_decode hD hT hH hC u) (T.sample m, θ)
    _ = (S.circle γ).decode u.val m θ := spacesTraceExtensionRawLinear_sample hD hT γ _ m θ

include hD hT hH hC in
/-- The complete trace and right-inverse clause of `IsPhysicalSpaces`. -/
theorem spaces_trace_split_tame :
    ∃ trace : (S.height γ).Space →L[ℝ] EvenCircleAt S γ,
      (∀ u m θ, (S.circle γ).decode (trace u).val m θ =
        (S.height γ).decode u (T.sample m, θ)) ∧
      (∃ loss base, IsTameLinear (S.height γ).grading (evenCircleGradingAt S γ)
        trace.toLinearMap loss base) ∧
      ∃ extend : EvenCircleAt S γ →L[ℝ] (S.height γ).Space,
        (∀ u, trace (extend u) = u) ∧
        (∃ loss base, IsTameLinear (evenCircleGradingAt S γ) (S.height γ).grading
          extend.toLinearMap loss base) :=
  ⟨spacesEvenTrace hD hT hH hC, spacesEvenTrace_decode hD hT hH hC,
    ⟨3, 0, spacesEvenTrace_isTame hD hT hH hC⟩,
    spacesEvenExtensionMap hD hT hH hC, spacesEvenExtensionMap_rightInverse hD hT hH hC,
    ⟨3, 0, spacesEvenExtensionMap_isTame hD hT hH hC⟩⟩

end ContinuousFlexibility.Statements
