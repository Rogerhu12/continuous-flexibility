import ContinuousFlexibility.Analysis.CircleUnitIntegral
import ContinuousFlexibility.Analysis.TameUnitIntegralLinearFamily
import ContinuousFlexibility.Analysis.CircleCompositionSmoothTame

/-!
# Joint smooth tameness of the actual averaged chart composition

The average is precisely the previously constructed circle operator.
Scaling the chart input by a parameter in the unit interval contracts
every input grade. Compact parameter integration of the genuine chart
composition tower therefore gives its full smooth tame dependence on
both the chart perturbation and the composed function.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [ContinuousSMul ℝ E]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

def pairScaleFirst (a : ℝ) : E × G →L[ℝ] E × G :=
  (a • ContinuousLinearMap.fst ℝ E G).prod (ContinuousLinearMap.snd ℝ E G)

theorem pairScaleFirst_apply (a : ℝ) (x : E × G) :
    pairScaleFirst a x = (a • x.1, x.2) := rfl

theorem continuous_pairScaleFirst :
    Continuous (fun z : ℝ × (E × G) => pairScaleFirst z.1 z.2) :=
  (continuous_fst.smul continuous_snd.fst).prodMk continuous_snd.snd

theorem pairScaleFirst_grading_le
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ G)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (s : ℕ) (x : E × G) :
    pairGrading p q s (pairScaleFirst a x) ≤ pairGrading p q s x := by
  rw [pairScaleFirst_apply, pairGrading_apply, pairGrading_apply, map_smul_eq_mul]
  have hnorm : ‖a‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg ha.1] using ha.2
  exact add_le_add (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hnorm (apply_nonneg (p s) x.1)) le_rfl

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis

local instance circleAverageCompositionSmoothTamePairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circleAverageComposeLinear_eq_unitIntegral
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (x : S.Space × S.Space)
    (hc : Continuous (fun a : ℝ =>
      circleShiftedChartComposeContinuousLinear hS hT hD hγ travel
        (pairScaleFirst a x).1 (pairScaleFirst a x).2)) :
    circleAverageComposeLinear hS hT hD hγ travel x.1 x.2 =
      circleUnitIntegral hS
        (fun a => circleShiftedChartComposeContinuousLinear hS hT hD hγ travel
          (pairScaleFirst a x).1 (pairScaleFirst a x).2) hc := by
  apply hS.2.2.2.2.2.1
  funext m θ
  rw [circleAverageComposeLinear_decode,
    circleUnitIntegral_decode hS (material_circle_sample_weights_pos hT hD).1
      (material_circle_sample_weights_pos hT hD).2]
  apply intervalIntegral.integral_congr
  intro a ha
  simp only [pairScaleFirst_apply]
  rw [circleShiftedChartComposeContinuousLinear_apply,
    circleShiftedChartComposeLinear_decode]
  simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]

theorem smoothTameOn_circleAverageComposeLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    SmoothTameOn (pairGrading S.grading S.grading) S.grading univ
      (fun x : S.Space × S.Space =>
        circleAverageComposeLinear hS hT hD hγ travel x.1 x.2) := by
  letI : ∀ n, CompleteSpace (S.level n) :=
    fun n => (hS.2.1 n).isComplete.completeSpace_coe
  let p := pairGrading S.grading S.grading
  have hp : Monotone p := tamePairGrading_monotone
    (gradedSeminorm_monotone (fun j => S.level j) S.bond)
    (gradedSeminorm_monotone (fun j => S.level j) S.bond)
  have ht : WithSeminorms p := withSeminorms_pairGrading
    (withSeminorms_graded (fun j => S.level j) S.bond)
    (withSeminorms_graded (fun j => S.level j) S.bond)
  have hcomp := smoothTameOn_circleChartComposition hS hT hD hγ hinterp travel
  let J := hcomp.choose
  have hJ : J.TameBounds p S.grading := hcomp.choose_spec
  have havg := smoothTameOn_unitIntegralLinearFamily hp ht J hJ
    (fun a : ℝ => (pairScaleFirst a : S.Space × S.Space →L[ℝ] S.Space × S.Space))
    continuous_pairScaleFirst
    (fun a ha s x => pairScaleFirst_grading_le S.grading S.grading ha s x)
  apply smoothTameOn_congr havg
  intro x hx
  exact (circleAverageComposeLinear_eq_unitIntegral hS hT hD hγ travel x _).symm

end ContinuousFlexibility.Statements
