import ContinuousFlexibility.Analysis.N04PulledFieldsKernelJointFixedBase
import ContinuousFlexibility.Analysis.CoupledCircleCompositionSmoothTame
import ContinuousFlexibility.Analysis.CircleTranslationUniformBounds
import ContinuousFlexibility.Analysis.CircleShiftedForwardFixedBaseBounds
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

private theorem n04PulledFields_kernelMajorants_of_realization
    {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y)
    (raw : ∀ r k : ℕ, X → X → (Fin k → X) → Y)
    (K : ∀ n : ℕ, X → X [×(n + 1)]→L[ℝ] Y)
    (happly : ∀ n x u, K n x u = raw n n x (u 0) (Fin.tail u))
    (hraw : ∃ base loss : ℕ, ∀ r k s R, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ R → ∀ v (w : Fin k → X),
        q s (raw r k x v w) ≤ C *
          multilinearTameSize (p base) (p (r + s + loss)) (k + 1)
            (1 + p (r + s + loss) x) (Fin.cons v w)) :
    ∃ base loss : ℕ, ∀ n s R, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ R → ∀ u : Fin (n + 1) → X,
        q s (K n x u) ≤ C * multilinearTameSize (p base) (p (n + s + loss))
          (n + 1) (1 + p (n + s + loss) x) u := by
  obtain ⟨base, loss, h⟩ := hraw
  refine ⟨base, loss, fun n s R hR => ?_⟩
  obtain ⟨C, hC, hb⟩ := h n n s R hR
  refine ⟨C, hC, fun x hx u => ?_⟩
  rw [happly]
  have hbound := hb x hx (u 0) (Fin.tail u)
  simp only [Fin.cons_self_tail] at hbound
  exact hbound

private theorem n04PulledFields_kernelTower_bound_of_majorants
    {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsTopologicalAddGroup Y]
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y) (hp : Monotone p)
    (K : ∀ n : ℕ, X → X [×(n + 1)]→L[ℝ] Y)
    {f : X × X → Y} (J : SmoothDirections univ f)
    (hJ : ∀ n z v, J.D n z v = coupledKernelJointJet K n z v)
    (hK : ∃ base loss : ℕ, ∀ n s R, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ R → ∀ u : Fin (n + 1) → X,
        q s (K n x u) ≤ C * multilinearTameSize (p base) (p (n + s + loss))
          (n + 1) (1 + p (n + s + loss) x) u) :
    ∃ base loss : ℕ, ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : X × X, pairGrading p p base z ≤ R → ∀ v : Fin n → X × X,
        q s (J.D n z v) ≤ C * tameJetSize (pairGrading p p) n s (n + loss) base z v := by
  obtain ⟨base, loss, hb⟩ := hK
  refine ⟨base, loss, fun n R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ :=
    n04PulledFields_coupledKernelJointJet_fixedBase p q hp K base loss hb n R hR s
  refine ⟨C, hC, fun z hz v => ?_⟩
  rw [hJ]
  exact hc z hz v

private theorem n04PulledFields_precompFamily_fixedBase
    {I E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    {f : E → F} (J : SmoothDirections univ f)
    (L : I → E →L[ℝ] E) (g : I → E → F)
    (heq : ∀ i x, g i x = f (L i x))
    (hL : ∀ i s x, p s (L i x) ≤ p s x)
    (hJ : ∃ base loss : ℕ, ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ R → ∀ v : Fin n → E,
        q s (J.D n x v) ≤ C * tameJetSize p n s (n + loss) base x v) :
    ∃ base loss : ℕ, ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i (K : SmoothDirections univ (g i)), ∀ x, p base x ≤ R →
      ∀ v : Fin n → E,
        q s (K.D n x v) ≤ C * tameJetSize p n s (n + loss) base x v := by
  obtain ⟨base, loss, hb⟩ := hJ
  refine ⟨base, loss, fun n R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb n R hR s
  refine ⟨C, hC, fun i K x hx v => ?_⟩
  have hd := n04PulledFields_precompJet_eq J K (L i) (heq i) n x v
  have hbound := hc (L i x) ((hL i base x).trans hx) (fun j => L i (v j))
  have hsize := tameJetSize_linear_contraction p (L i).toLinearMap
    (hL i) n s (n + loss) base x v
  exact (congrArg (q s) hd).le.trans
    (hbound.trans (mul_le_mul_of_nonneg_left hsize hC))

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
  refine n04PulledFields_kernelMajorants_of_realization M.grading M.grading
    (coupledCircleKernel hD hT hγ hM hI)
    (fun n ψ => coupledCircleKernelContinuousMultilinear hD hT hγ hM hI n n ψ)
    (fun n x u => coupledCircleKernelContinuousMultilinear_apply hD hT hγ hM hI n n x u) ?_
  simpa only [coupledCircleKernelMajorant, multilinearTameSize] using
    coupled_circle_kernel_grading_bounds hD hT hγ hM hI

private theorem n04PulledFields_circleKernelTower_fixedBase :
    ∃ base loss : ℕ, ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : M.Space × M.Space, pairGrading M.grading M.grading base z ≤ R →
      ∀ v : Fin n → M.Space × M.Space,
        M.grading s ((n04PulledFields_circleKernelTower hD hT hγ hM hI).D n z v) ≤
          C * tameJetSize (pairGrading M.grading M.grading) n s (n + loss) base z v := by
  exact n04PulledFields_kernelTower_bound_of_majorants M.grading M.grading
    (gradedSeminorm_monotone _ _)
    (fun n ψ => coupledCircleKernelContinuousMultilinear hD hT hγ hM hI n n ψ)
    (n04PulledFields_circleKernelTower hD hT hγ hM hI)
    (n04PulledFields_circleKernelTower_apply hD hT hγ hM hI)
    (n04PulledFields_circleKernelMajorants hD hT hγ hM hI)

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
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd']

private theorem n04PulledFields_circleTranslationPair_bound
    (travel : ℕ → ℝ) (s : ℕ) (z : M.Space × M.Space) :
    pairGrading M.grading M.grading s
        (n04PulledFields_circleTranslationPair hD hT hγ hM travel z) ≤
      pairGrading M.grading M.grading s z := by
  simp only [n04PulledFields_circleTranslationPair_apply, pairGrading_apply]
  exact add_le_add le_rfl (circleTranslationContinuousLinear_grading_le hM hT hD hγ travel s z.2)

private theorem n04PulledFields_shiftedForward_eq_kernel
    (travel : ℕ → ℝ) (z : M.Space × M.Space) :
    circleShiftedChartComposeContinuousLinear hM hT hD hγ travel z.1 z.2 =
      coupledCircleKernel hD hT hγ hM hI 0 0
        (n04PulledFields_circleTranslationPair hD hT hγ hM travel z).1
        (n04PulledFields_circleTranslationPair hD hT hγ hM travel z).2 Fin.elim0 := by
  have hp := congrArg (fun w : M.Space × M.Space =>
      coupledCircleKernel hD hT hγ hM hI 0 0 w.1 w.2 Fin.elim0)
    (n04PulledFields_circleTranslationPair_apply hD hT hγ hM travel z)
  exact (circleShiftedChartCompose_zero_kernel hD hT hγ hM hI travel z.1 z.2).trans hp.symm

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
  exact n04PulledFields_precompFamily_fixedBase
    (pairGrading M.grading M.grading) M.grading
    (n04PulledFields_circleKernelTower hD hT hγ hM hI)
    (n04PulledFields_circleTranslationPair hD hT hγ hM)
    (fun travel z => circleShiftedChartComposeContinuousLinear hM hT hD hγ travel z.1 z.2)
    (n04PulledFields_shiftedForward_eq_kernel hD hT hγ hM hI)
    (n04PulledFields_circleTranslationPair_bound hD hT hγ hM)
    (n04PulledFields_circleKernelTower_fixedBase hD hT hγ hM hI)

end ContinuousFlexibility.Statements
