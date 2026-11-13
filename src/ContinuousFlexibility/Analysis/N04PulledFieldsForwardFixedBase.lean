import ContinuousFlexibility.Analysis.N04PulledFieldsKernelJointFixedBase
import ContinuousFlexibility.Analysis.CoupledCircleCompositionSmoothTame
import ContinuousFlexibility.Analysis.CircleTranslationUniformBounds
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine
import ContinuousFlexibility.Analysis.TameUnitIntegralLinearFamily

/-!
# Fixed-base bounds for both inputs of actual circle composition

The realized coupled kernels supply the genuine joint tower. Their common
low base survives all parameter orders. Travel is moved into the existing
circle translation, which contracts every grading, and uniqueness transfers
the estimate to every supplied tower of the actual shifted composition.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem n04PulledFields_precompJet_eq
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
    {f g : E → F} (J : SmoothDirections univ f) (K : SmoothDirections univ g)
    (L : E →L[ℝ] E) (heq : ∀ x, g x = f (L x))
    (n : ℕ) (x : E) (v : Fin n → E) :
    K.D n x v = J.D n (L x) (fun i => L (v i)) := by
  let hmap : MapsTo (fun y : E => 0 + L y) univ univ := fun _ _ => mem_univ _
  let A := J.compAffine L 0 isOpen_univ hmap
  let B : SmoothDirections univ g := A.congrOn (fun y _ => by
    change f (0 + L y) = g y
    rw [zero_add]
    exact (heq y).symm)
  have hb := congrArg (fun D : E [×n]→L[ℝ] F => D v) (K.unique B n x (mem_univ _))
  have ha := J.compAffine_apply L 0 isOpen_univ hmap n x v
  simp only [zero_add] at ha
  exact hb.trans ha

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

local instance n04PulledFieldsForwardFixedBasePairSMul (M : CircleModelData) :
    SMul ℝ (M.Space × M.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

private def n04PulledFields_circleKernelTower :
    SmoothDirections univ (fun z : M.Space × M.Space =>
      coupledCircleKernel hD hT hγ hM hI 0 0 z.1 z.2 Fin.elim0) := by
  let K : ∀ n : ℕ, M.Space → M.Space [×(n + 1)]→L[ℝ] M.Space :=
    fun n ψ => coupledCircleKernelContinuousMultilinear hD hT hγ hM hI n n ψ
  have hc : ∀ n, Continuous
      (fun z : M.Space × (Fin (n + 1) → M.Space) => K n z.1 z.2) := by
    intro n
    simpa only [K, coupledCircleKernelContinuousMultilinear_apply,
      coupledCircleKernelMultilinear_apply] using
      coupledCircleKernelMultilinear_continuous hD hT hγ hM hI n n
  have hl : ∀ n x v w u, HasProjectiveLineDerivAt
      (fun ψ => K n ψ (Fin.cons v w))
      (K (n + 1) x (Fin.cons v (Fin.cons u w))) x u := by
    intro n x v w u
    simpa only [K, coupledCircleKernelContinuousMultilinear_apply,
      Fin.cons_zero, Fin.tail_cons] using
      coupledCircleKernel_hasProjectiveLineDerivAt hD hT hγ hM hI n n x u v w
  exact (coupledKernelSmoothDirections K hc hl).congrOn (fun z _ => by
    simp only [K, coupledCircleKernelContinuousMultilinear_apply, Fin.cons_zero, Fin.tail_cons])

private theorem n04PulledFields_circleKernelTower_apply
    (n : ℕ) (z : M.Space × M.Space) (v : Fin n → M.Space × M.Space) :
    (n04PulledFields_circleKernelTower hD hT hγ hM hI).D n z v =
      coupledKernelJointJet
        (fun k ψ => coupledCircleKernelContinuousMultilinear hD hT hγ hM hI k k ψ) n z v := rfl

private theorem n04PulledFields_circleKernelMajorants :
    ∃ base loss : ℕ, ∀ n s R, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, M.grading base x ≤ R → ∀ u : Fin (n + 1) → M.Space,
        M.grading s (coupledCircleKernelContinuousMultilinear hD hT hγ hM hI n n x u) ≤
          C * multilinearTameSize (M.grading base) (M.grading (n + s + loss))
            (n + 1) (1 + M.grading (n + s + loss) x) u := by
  let data := coupled_circle_kernel_grading_bounds hD hT hγ hM hI
  refine ⟨data.choose, data.choose_spec.choose, fun n s R hR => ?_⟩
  let estimate := data.choose_spec.choose_spec n n s R hR
  refine ⟨estimate.choose, estimate.choose_spec.1, fun x hx u => ?_⟩
  rw [coupledCircleKernelContinuousMultilinear_apply]
  have h := estimate.choose_spec.2 x hx (u 0) (Fin.tail u)
  simp only [coupledCircleKernelMajorant, Fin.cons_self_tail] at h
  exact h

private theorem n04PulledFields_circleKernelTower_fixedBase :
    ∃ base loss : ℕ, ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : M.Space × M.Space, pairGrading M.grading M.grading base z ≤ R →
      ∀ v : Fin n → M.Space × M.Space,
        M.grading s ((n04PulledFields_circleKernelTower hD hT hγ hM hI).D n z v) ≤
          C * tameJetSize (pairGrading M.grading M.grading) n s (n + loss) base z v := by
  let data := n04PulledFields_circleKernelMajorants hD hT hγ hM hI
  let base : ℕ := data.choose
  let loss : ℕ := data.choose_spec.choose
  have hb := n04PulledFields_coupledKernelJointJet_fixedBase M.grading M.grading
    (gradedSeminorm_monotone _ _)
    (fun n ψ => coupledCircleKernelContinuousMultilinear hD hT hγ hM hI n n ψ)
    base loss data.choose_spec.choose_spec
  refine ⟨base, loss, fun n R hR s => ?_⟩
  let estimate := hb n R hR s
  refine ⟨estimate.choose, estimate.choose_spec.1, fun z hz v => ?_⟩
  rw [n04PulledFields_circleKernelTower_apply]
  exact estimate.choose_spec.2 z hz v

private def n04PulledFields_circleTranslationPair (travel : ℕ → ℝ) :
    (M.Space × M.Space) →L[ℝ] M.Space × M.Space :=
  (ContinuousLinearMap.fst ℝ M.Space M.Space).prod
    ((circleTranslationContinuousLinear hM hT hD hγ travel).comp
      (ContinuousLinearMap.snd ℝ M.Space M.Space))

private theorem n04PulledFields_circleTranslationPair_apply
    (travel : ℕ → ℝ) (z : M.Space × M.Space) :
    n04PulledFields_circleTranslationPair hD hT hγ hM travel z =
      (z.1, circleTranslationContinuousLinear hM hT hD hγ travel z.2) := by
  simp only [n04PulledFields_circleTranslationPair, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.fst_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.snd_apply]

private theorem n04PulledFields_circleTranslationPair_bound
    (travel : ℕ → ℝ) (s : ℕ) (z : M.Space × M.Space) :
    pairGrading M.grading M.grading s
        (n04PulledFields_circleTranslationPair hD hT hγ hM travel z) ≤
      pairGrading M.grading M.grading s z := by
  simp only [n04PulledFields_circleTranslationPair_apply, pairGrading_apply]
  exact add_le_add le_rfl (circleTranslationContinuousLinear_grading_le hM hT hD hγ travel s z.2)

private theorem n04PulledFields_zeroForward_eq_kernel (e y : M.Space) :
    circleShiftedChartComposeContinuousLinear hM hT hD hγ (fun _ => 0) e y =
      coupledCircleKernel hD hT hγ hM hI 0 0 e y Fin.elim0 := by
  apply hM.2.2.2.2.2.1
  funext m θ
  rw [circleShiftedChartComposeContinuousLinear_apply, circleShiftedChartComposeLinear_decode,
    coupled_circleComposition_decode]
  simp only [add_zero]

private theorem n04PulledFields_shiftedForward_eq_kernel
    (travel : ℕ → ℝ) (z : M.Space × M.Space) :
    circleShiftedChartComposeContinuousLinear hM hT hD hγ travel z.1 z.2 =
      coupledCircleKernel hD hT hγ hM hI 0 0
        (n04PulledFields_circleTranslationPair hD hT hγ hM travel z).1
        (n04PulledFields_circleTranslationPair hD hT hγ hM travel z).2 Fin.elim0 := by
  rw [n04PulledFields_circleTranslationPair_apply]
  exact (circleShiftedChartComposeContinuousLinear_apply hM hT hD hγ travel z.1 z.2).trans
    ((circleShiftedChartComposeLinear_eq_zero_travel hM hT hD hγ travel z.1 z.2).trans
      ((circleShiftedChartComposeContinuousLinear_apply hM hT hD hγ (fun _ => 0) z.1
        (circleTranslationContinuousLinear hM hT hD hγ travel z.2)).symm.trans
        (n04PulledFields_zeroForward_eq_kernel hD hT hγ hM hI z.1
          (circleTranslationContinuousLinear hM hT hD hγ travel z.2))))

include hI in
/-- Both inputs retain a single common low base before every parameter
order. Travel contributes no grading cost, and the estimate holds for
every genuine tower of the actual shifted forward composition. -/
theorem n04PulledFields_circleForward_fixedBase_oneHigh :
    ∃ base loss : ℕ, ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (travel : ℕ → ℝ)
        (J : SmoothDirections univ (fun z : M.Space × M.Space =>
          circleShiftedChartComposeContinuousLinear hM hT hD hγ travel z.1 z.2)),
      ∀ x : M.Space × M.Space, pairGrading M.grading M.grading base x ≤ R →
      ∀ v : Fin n → M.Space × M.Space,
        M.grading s (J.D n x v) ≤
          C * tameJetSize (pairGrading M.grading M.grading) n s (n + loss) base x v := by
  let data := n04PulledFields_circleKernelTower_fixedBase hD hT hγ hM hI
  let base : ℕ := data.choose
  let loss : ℕ := data.choose_spec.choose
  refine ⟨base, loss, fun n R hR s => ?_⟩
  let estimate := data.choose_spec.choose_spec n R hR s
  refine ⟨estimate.choose, estimate.choose_spec.1, fun travel J x hx v => ?_⟩
  let p := pairGrading M.grading M.grading
  let L := n04PulledFields_circleTranslationPair hD hT hγ hM travel
  have hL : ∀ t z, p t (L z) ≤ p t z :=
    n04PulledFields_circleTranslationPair_bound hD hT hγ hM travel
  have heq := n04PulledFields_precompJet_eq
    (n04PulledFields_circleKernelTower hD hT hγ hM hI) J L
    (n04PulledFields_shiftedForward_eq_kernel hD hT hγ hM hI travel) n x v
  have hb := estimate.choose_spec.2 (L x) ((hL base x).trans hx) (fun i => L (v i))
  have hw := tameJetSize_linear_contraction p L.toLinearMap hL n s (n + loss) base x v
  exact (congrArg (M.grading s) heq).le.trans
    (hb.trans (mul_le_mul_of_nonneg_left hw estimate.choose_spec.1))

end ContinuousFlexibility.Statements
