import ContinuousFlexibility.Analysis.CoupledCircleCompositionSmoothTame
import ContinuousFlexibility.Analysis.CoupledCircleTranslation
import ContinuousFlexibility.Analysis.CircleUnitIntegral
import ContinuousFlexibility.Analysis.TameUnitIntegralLinearFamily

/-!
# Actual averaged circle composition with fixed travel

Fixed component translations act on the outer function. Scaling the chart
by a unit-interval parameter contracts each input grade. The genuine
projective integral of the resulting compositions therefore has the
required joint smooth tame tower and the exact scalar integral decoder.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

section Scaling

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [ContinuousSMul ℝ E]

def coupledCircleScaleFirst (a : ℝ) : E × E →L[ℝ] E × E :=
  (a • ContinuousLinearMap.fst ℝ E E).prod (ContinuousLinearMap.snd ℝ E E)

theorem coupledCircleScaleFirst_apply (a : ℝ) (x : E × E) :
    coupledCircleScaleFirst a x = (a • x.1, x.2) := by
  simp only [coupledCircleScaleFirst, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']

theorem coupledCircleScaleFirst_continuous :
    Continuous (fun z : ℝ × (E × E) => coupledCircleScaleFirst z.1 z.2) := by
  have h : Continuous (fun z : ℝ × (E × E) => (z.1 • z.2.1, z.2.2)) :=
    (continuous_fst.smul continuous_snd.fst).prodMk continuous_snd.snd
  simpa only [coupledCircleScaleFirst_apply] using h

theorem coupledCircleScaleFirst_grading_le (p : ℕ → Seminorm ℝ E)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (s : ℕ) (x : E × E) :
    pairGrading p p s (coupledCircleScaleFirst a x) ≤ pairGrading p p s x := by
  rw [coupledCircleScaleFirst_apply, pairGrading_apply, pairGrading_apply, map_smul_eq_mul]
  have ha' : ‖a‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg ha.1] using ha.2
  exact add_le_add (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right ha' (apply_nonneg (p s) x.1)) le_rfl

end Scaling

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

def coupledCircleShiftedCompose (travel : ℕ → ℝ) (ψ v : M.Space) : M.Space :=
  coupledCircleKernel hD hT hγ hM hI 0 0 ψ
    (coupledCircleTranslation hM travel v) Fin.elim0

theorem coupledCircleShiftedCompose_decode
    (travel : ℕ → ℝ) (ψ v : M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (coupledCircleShiftedCompose hD hT hγ hM hI travel ψ v) m θ =
      M.decode v m (θ + travel m + M.decode ψ m θ) := by
  have hcomp := coupled_circleComposition_decode hD hT hγ hM hI ψ
    (coupledCircleTranslation hM travel v) m θ
  have htranslation := coupledCircleTranslation_decode hM travel v m (θ + M.decode ψ m θ)
  exact hcomp.trans (htranslation.trans
    (congrArg (M.decode v m) (add_right_comm θ (M.decode ψ m θ) (travel m))))

private theorem coupled_circle_decode_smul (a : ℝ) (ψ : M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (a • ψ) m θ = a * M.decode ψ m θ := by
  have h := congrFun (congrFun (M.decode.map_smul a ψ) m) θ
  exact h

private theorem coupledCircleShiftedCompose_smul_decode
    (travel : ℕ → ℝ) (a : ℝ) (ψ v : M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (coupledCircleShiftedCompose hD hT hγ hM hI travel (a • ψ) v) m θ =
      M.decode v m (θ + travel m + a * M.decode ψ m θ) := by
  have hd := coupledCircleShiftedCompose_decode hD hT hγ hM hI travel (a • ψ) v m θ
  exact hd.trans (congrArg (fun t : ℝ => M.decode v m (θ + travel m + t))
    (coupled_circle_decode_smul (M := M) a ψ m θ))

theorem coupled_circleShiftedCompose_smoothTameOn (travel : ℕ → ℝ) :
    SmoothTameOn (pairGrading M.grading M.grading) M.grading univ
      (fun z : M.Space × M.Space =>
        coupledCircleShiftedCompose hD hT hγ hM hI travel z.1 z.2) := by
  let L : M.Space × M.Space →L[ℝ] M.Space × M.Space :=
    (ContinuousLinearMap.fst ℝ M.Space M.Space).prod
      ((coupledCircleTranslation hM travel).comp
        (ContinuousLinearMap.snd ℝ M.Space M.Space))
  have hb : ∀ s z, pairGrading M.grading M.grading s (L z) ≤
      1 * pairGrading M.grading M.grading s z := by
    intro s z
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', pairGrading_apply,
      coupledCircleTranslation_grading_eq, one_mul, le_refl]
  have h := solve_smoothTameOn_precomp
    (coupled_circleComposition_smoothTameOn hD hT hγ hM hI) L (A := 1) le_rfl hb
  simpa only [Set.preimage_univ, L, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', coupledCircleShiftedCompose] using h

private theorem coupled_circleShiftedCompose_continuous (travel : ℕ → ℝ) :
    Continuous (fun z : M.Space × M.Space =>
      coupledCircleShiftedCompose hD hT hγ hM hI travel z.1 z.2) := by
  letI : ∀ n, CompleteSpace (M.level n) :=
    fun n => (hM.2.1 n).isComplete.completeSpace_coe
  exact continuous_smoothDirections_univ
    (coupled_circleShiftedCompose_smoothTameOn hD hT hγ hM hI travel).choose

def coupledCircleAverageCompose (travel : ℕ → ℝ) (ψ v : M.Space) : M.Space :=
  circleUnitIntegral hM
    (fun a => coupledCircleShiftedCompose hD hT hγ hM hI travel (a • ψ) v)
    ((coupled_circleShiftedCompose_continuous hD hT hγ hM hI travel).comp
      ((continuous_id.smul continuous_const).prodMk continuous_const))

theorem coupledCircleAverageCompose_decode
    (travel : ℕ → ℝ) (ψ v : M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (coupledCircleAverageCompose hD hT hγ hM hI travel ψ v) m θ =
      ∫ a in (0 : ℝ)..1, M.decode v m (θ + travel m + a * M.decode ψ m θ) := by
  have hMpos : ∀ j, 0 < T.M (T.sample j) := fun j =>
    zero_lt_one.trans_le (hT.2.1 _ (spaces_trace_sample_mem hD hT j)).2.2.2
  have hHpos : ∀ j, 0 < T.H (T.sample j) := fun j =>
    (hT.2.1 _ (spaces_trace_sample_mem hD hT j)).2.1
  have hd := circleUnitIntegral_decode hM hMpos hHpos
    (fun a : ℝ => coupledCircleShiftedCompose hD hT hγ hM hI travel (a • ψ) v)
    ((coupled_circleShiftedCompose_continuous hD hT hγ hM hI travel).comp
      ((continuous_id.smul continuous_const).prodMk continuous_const)) m θ
  exact hd.trans (intervalIntegral.integral_congr (fun a _ =>
    coupledCircleShiftedCompose_smul_decode hD hT hγ hM hI travel a ψ v m θ))

/-- The integral retains a fixed loss before every output order. -/
theorem coupled_circleAverageCompose_smoothTameOn (travel : ℕ → ℝ) :
    SmoothTameOn (pairGrading M.grading M.grading) M.grading univ
      (fun z : M.Space × M.Space =>
        coupledCircleAverageCompose hD hT hγ hM hI travel z.1 z.2) := by
  letI : ∀ n, CompleteSpace (M.level n) :=
    fun n => (hM.2.1 n).isComplete.completeSpace_coe
  let p := pairGrading M.grading M.grading
  have hp : Monotone p := tamePairGrading_monotone
    (gradedSeminorm_monotone _ _) (gradedSeminorm_monotone _ _)
  have ht : WithSeminorms p :=
    withSeminorms_pairGrading (withSeminorms_graded _ _) (withSeminorms_graded _ _)
  have hcomp : SmoothTameOn p M.grading univ
      (fun z : M.Space × M.Space =>
        coupledCircleShiftedCompose hD hT hγ hM hI travel z.1 z.2) :=
    coupled_circleShiftedCompose_smoothTameOn hD hT hγ hM hI travel
  let J : SmoothDirections univ (fun z : M.Space × M.Space =>
      coupledCircleShiftedCompose hD hT hγ hM hI travel z.1 z.2) := hcomp.choose
  have hJ : J.TameBounds p M.grading := hcomp.choose_spec
  let L : ℝ → M.Space × M.Space →L[ℝ] M.Space × M.Space :=
    fun a => coupledCircleScaleFirst a
  have hL : Continuous (fun z : ℝ × (M.Space × M.Space) => L z.1 z.2) :=
    coupledCircleScaleFirst_continuous
  have h := smoothTameOn_unitIntegralLinearFamily
    (F := fun n => M.level n) (bond := M.bond) (p := p)
    (f := fun z : M.Space × M.Space =>
      coupledCircleShiftedCompose hD hT hγ hM hI travel z.1 z.2)
    hp ht J hJ L hL
    (fun a ha s x => coupledCircleScaleFirst_grading_le M.grading ha s x)
  change SmoothTameOn p M.grading univ
    (fun x : M.Space × M.Space => projectiveUnitIntegral
      (fun a => coupledCircleShiftedCompose hD hT hγ hM hI travel (L a x).1 (L a x).2)
      ((continuous_smoothDirections_univ J).comp
        (hL.comp (continuous_id.prodMk continuous_const)))) at h
  apply smoothTameOn_congr h
  intro x hx
  have hf : Continuous (fun a : ℝ =>
      coupledCircleShiftedCompose hD hT hγ hM hI travel (L a x).1 (L a x).2) :=
    (continuous_smoothDirections_univ J).comp
      (hL.comp (continuous_id.prodMk continuous_const))
  have hg : Continuous (fun a : ℝ =>
      coupledCircleShiftedCompose hD hT hγ hM hI travel (a • x.1) x.2) :=
    (coupled_circleShiftedCompose_continuous hD hT hγ hM hI travel).comp
      ((continuous_id.smul continuous_const).prodMk continuous_const)
  change projectiveUnitIntegral
      (fun a => coupledCircleShiftedCompose hD hT hγ hM hI travel (L a x).1 (L a x).2) hf =
    projectiveUnitIntegral
      (fun a => coupledCircleShiftedCompose hD hT hγ hM hI travel (a • x.1) x.2) hg
  apply projectiveUnitIntegral_congr hf hg
  intro a ha
  exact congrArg
    (fun z : M.Space × M.Space => coupledCircleShiftedCompose hD hT hγ hM hI travel z.1 z.2)
    (coupledCircleScaleFirst_apply a x)

end ContinuousFlexibility.Statements
