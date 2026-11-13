import ContinuousFlexibility.Analysis.TameForwardJetUniformBounds
import ContinuousFlexibility.Analysis.CoupledCircleCompositionCurveDerivative
import ContinuousFlexibility.Analysis.CircleTranslationUniformBounds
import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Fixed low-base bounds for the actual shifted forward family

The ordered derivatives of the given genuine tower are the existing
composition kernels. Only the source is normalized; parameter increments
stay in one fixed low-seminorm ball. Translation costs no grading order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped BigOperators Topology

local instance circleShiftedForwardFixedBasePairSMul (M : CircleModelData) :
    SMul ℝ (M.Space × M.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

private theorem circleShiftedChartCompose_zero_kernel
    (travel : ℕ → ℝ) (e y : M.Space) :
    circleShiftedChartComposeContinuousLinear hM hT hD hγ travel e y =
      coupledCircleKernel hD hT hγ hM hI 0 0 e
        (circleTranslationContinuousLinear hM hT hD hγ travel y) Fin.elim0 := by
  apply hM.2.2.2.2.2.1
  funext m θ
  have hc := circleShiftedChartComposeContinuousLinear_apply hM hT hD hγ travel e y
  have hl := circleShiftedChartComposeLinear_decode hM hT hD hγ travel e y m θ
  have ht := congrFun (congrFun
    (circleTranslationContinuousLinear_decode hM hT hD hγ travel y) m)
    (θ + M.decode e m θ)
  have hk := coupledCircleKernel_decode_apply hD hT hγ hM hI 0 0 e
    (circleTranslationContinuousLinear hM hT hD hγ travel y) Fin.elim0 m θ
  calc
    _ = M.decode (circleShiftedChartComposeLinear hM hT hD hγ travel e y) m θ :=
      congrArg (fun z : M.Space => M.decode z m θ) hc
    _ = M.decode y m (θ + travel m + M.decode e m θ) := hl
    _ = M.decode y m ((θ + M.decode e m θ) + travel m) :=
      congrArg (M.decode y m) (by ring)
    _ = M.decode (circleTranslationContinuousLinear hM hT hD hγ travel y) m
        (θ + M.decode e m θ) := ht.symm
    _ = _ := by
      simpa only [iteratedDeriv_zero, Fin.prod_univ_zero, mul_one] using hk.symm

/-- The existing ordered tower has the literal shifted kernel as its jet. -/
theorem circleShiftedChartCompose_orderedJet_eq_kernel
    (travel : ℕ → ℝ) {U : Set M.Space} (hU : IsOpen U)
    (J : SmoothDirections (U ×ˢ univ) (fun z : M.Space × M.Space =>
      circleShiftedChartComposeContinuousLinear hM hT hD hγ travel z.1 z.2))
    (n : ℕ) :
    ∀ e ∈ U, ∀ (v : Fin n → M.Space) (y : M.Space),
      inverseForwardJet J n e v y =
        coupledCircleKernel hD hT hγ hM hI n n e
          (circleTranslationContinuousLinear hM hT hD hγ travel y) v := by
  refine inverseForwardJet_eq_of_recurrence hU J
    (fun n e v y => coupledCircleKernel hD hT hγ hM hI n n e
      (circleTranslationContinuousLinear hM hT hD hγ travel y) v) ?_ ?_ n
  · intro e he y
    exact circleShiftedChartCompose_zero_kernel hD hT hγ hM hI travel e y
  · intro n e he v y h
    exact coupledCircleKernel_hasProjectiveLineDerivAt hD hT hγ hM hI
      n n e h (circleTranslationContinuousLinear hM hT hD hγ travel y) v

include hI in
/-- One base and loss precede every parameter order, spatial order and
travel. The source remains linear and the old tower is unchanged. -/
theorem circleShiftedChartCompose_orderedJets_fixedBase_bound :
    ∃ base loss : ℕ, ∀ (n : ℕ) (R : ℝ), 1 ≤ R →
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ (travel : ℕ → ℝ) (U : Set M.Space) (hU : IsOpen U)
          (J : SmoothDirections (U ×ˢ univ) (fun z : M.Space × M.Space =>
            circleShiftedChartComposeContinuousLinear hM hT hD hγ travel z.1 z.2)),
          ∀ e ∈ U, M.grading base e ≤ R → ∀ v : Fin n → M.Space,
            (∀ i, M.grading base (v i) ≤ R) → ∀ y : M.Space,
              M.grading s (inverseForwardJet J n e v y) ≤ C *
                ((1 + M.grading (s + (n + loss)) e +
                    ∑ i, M.grading (s + (n + loss)) (v i)) * M.grading base y +
                  M.grading (s + (n + loss)) y) := by
  refine inverseForwardJets_fixedBase_bound_of_kernel M.grading
    (circleShiftedChartComposeContinuousLinear hM hT hD hγ)
    (circleTranslationContinuousLinear hM hT hD hγ)
    (coupledCircleKernel hD hT hγ hM hI) ?_ ?_ ?_
  · intro travel U hU J n
    exact circleShiftedChartCompose_orderedJet_eq_kernel hD hT hγ hM hI travel hU J n
  · exact circleTranslationContinuousLinear_grading_le hM hT hD hγ
  · simpa only [coupledCircleKernelMajorant, multilinearTameSize] using
      coupled_circle_kernel_grading_bounds hD hT hγ hM hI

end ContinuousFlexibility.Statements
