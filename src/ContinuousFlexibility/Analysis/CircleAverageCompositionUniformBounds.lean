module

public import ContinuousFlexibility.Analysis.CircleAverageCompositionSmoothTame
public import ContinuousFlexibility.Analysis.CircleCompositionUniformBounds
public import ContinuousFlexibility.Analysis.UniformUnitIntegralLinearFamily

/-!
# Uniform one-high bounds for the actual averaged composition

The tower below is obtained by integrating the actual composition
tower. For every parameter order, a common low order and loss are
fixed before the low-seminorm radius and output order. This uniformity
is retained when the base point subsequently ranges over a family of
physical radius selectors.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance circleAverageCompositionUniformBoundsPairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem exists_circleAverageComposeLinear_uniform_oneHigh
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    ∃ J : SmoothDirections univ
      (fun x : S.Space × S.Space =>
        circleAverageComposeLinear hS hT hD hγ travel x.1 x.2),
      ∀ n, ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x, pairGrading S.grading S.grading base x ≤ K →
          ∀ v : Fin n → S.Space × S.Space,
            S.grading s (J.D n x v) ≤
              C * tameJetSize (pairGrading S.grading S.grading) n s loss base x v := by
  letI : ∀ n, CompleteSpace (S.level n) :=
    fun n => (hS.2.1 n).isComplete.completeSpace_coe
  let h := exists_circleChartComposition_uniform_oneHigh hS hT hD hγ hinterp travel
  let f : S.Space × S.Space → S.Space := fun x =>
    circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2
  let J : SmoothDirections univ f := h.choose
  let L : ℝ → (S.Space × S.Space) →L[ℝ] S.Space × S.Space := fun a => pairScaleFirst a
  have hL : Continuous (fun z : ℝ × (S.Space × S.Space) => L z.1 z.2) :=
    continuous_pairScaleFirst
  let Javg := smoothDirectionsUnitIntegralLinearFamily J L hL
  have heq (x : S.Space × S.Space) (hx : x ∈ (univ : Set (S.Space × S.Space))) :
      projectiveUnitIntegral (fun a => f (L a x))
          ((continuous_smoothDirections_univ J).comp
            (hL.comp (continuous_id.prodMk continuous_const))) =
        circleAverageComposeLinear hS hT hD hγ travel x.1 x.2 :=
    (circleAverageComposeLinear_eq_unitIntegral hS hT hD hγ travel x _).symm
  refine ⟨Javg.congr heq, ?_⟩
  exact uniformOneHigh_unitIntegralLinearFamily J h.choose_spec.2 L hL
    (fun a ha s x => pairScaleFirst_grading_le S.grading S.grading ha s x)

end ContinuousFlexibility.Statements
