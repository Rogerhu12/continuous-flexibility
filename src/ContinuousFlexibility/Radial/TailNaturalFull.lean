module

public import ContinuousFlexibility.Radial.TailNaturalUniqueness
public import ContinuousFlexibility.Radial.TailFundamentalStates
public import ContinuousFlexibility.Radial.TailFundamentalNodeBounds
public import ContinuousFlexibility.Radial.TailFundamentalGreenBounds
public import ContinuousFlexibility.Radial.TailFundamentalGreenRepresentation

/-!
# The natural line and the localized kernel of the actual tail resolvent

The natural state is constructed from the canonical physical edge problem.
A normalized Dirichlet left state gives a single symmetric kernel. Its
classical representation is identified with the supplied Friedrichs
resolvent, and the same two states give the localized product estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem tailNaturalLineAndGreenKernel {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    (hI : TailFormIdentification T T.endpoint)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (hG : ∀ f, TailFriedrichsGraph T T.endpoint (G f) (f + T.Λ • G f)) :
    TailNaturalLineAndKernel T ∧ TailGreenKernel T G := by
  obtain ⟨u, q, hu, huc, hqc, hus, huInt, hu₀, hune, hnonzero, hstep, hua⟩ :=
    exists_tailNaturalSolution hT hη hK
  have hUnique : ∀ v, TailNaturalEquation T v → ∃ c : ℝ,
      ∀ x ∈ Ioo T.entrance T.endpoint, v x = c * u x := by
    intro v hv
    exact ⟨v (T.node 0) / u (T.node 0), tailNaturalEquation_eq_mul hT hη hK hu hv hune⟩
  obtain ⟨w, z, hwc, _, hws, hwa, hW⟩ :=
    exists_tailDirichletLeftState hT huc hqc hus hu₀ hua
  have hwcont : ContinuousOn w (Ico T.entrance T.endpoint) :=
    hwc.continuousOn.mono (fun _ hx => hx.2)
  have hcross := tailActualState_discrete_wronskian hT hus hws hW
  obtain ⟨B, hB, hΓ⟩ := exists_tailFundamentalNode_bound
    (a := fun n => u (T.node n)) (w := fun n => w (T.node n)) hT hη hK hune
    (tailNaturalEquation_node_recurrence hT hu) hstep hcross
  refine ⟨⟨u, hu, hnonzero, hUnique, ⟨8, by norm_num, hstep⟩⟩,
    ⟨tailFundamentalGreenKernel T.entrance T.endpoint w u 1,
      measurable_tailFundamentalGreenKernel
        (hwcont.mono Ioo_subset_Ico_self) hu.2.1.continuousOn, ?_,
      tailFundamentalGreen_representation hT hI G hG hu hua hUnique huInt hwcont hus hws hwa hW,
      ?_, tailFundamentalGreenKernel_bound hT hη hK hus hws hB hΓ hcross⟩⟩
  · intro ψ hψ hc _
    exact Eventually.of_forall fun x => tailFundamentalGreenKernel_mul_integrable_test
      (deepTail_contDiffOn hT).continuousOn (fun y hy => (deepTail_pos hT y hy).le)
      hwcont huInt hψ.continuous hc x
  · intro x y
    exact tailFundamentalGreenKernel_symm T.entrance T.endpoint 1 x y w u

end ContinuousFlexibility.Radial
