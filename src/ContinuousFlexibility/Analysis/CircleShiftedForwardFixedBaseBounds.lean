import ContinuousFlexibility.Analysis.TameForwardJetSourceBounds
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
  classical
  let kernelBounds := coupled_circle_kernel_grading_bounds
    (D := D) (T := T) (γ := γ) (M := M) hD hT hγ hM hI
  let base : ℕ := kernelBounds.choose
  let loss : ℕ := kernelBounds.choose_spec.choose
  have hkernel : ∀ (r k s : ℕ) (R : ℝ), 1 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : M.Space, M.grading base ψ ≤ R →
        ∀ (u : M.Space) (w : Fin k → M.Space),
          M.grading s (coupledCircleKernel hD hT hγ hM hI r k ψ u w) ≤
            C * coupledCircleKernelMajorant M base (r + s + loss) ψ (Fin.cons u w) :=
    kernelBounds.choose_spec.choose_spec
  refine ⟨base, loss, fun n R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hkernel n n s R hR
  have horder : n + s + loss = s + (n + loss) := by omega
  rw [horder] at hc
  let H : ℕ := s + (n + loss)
  have hP : 0 ≤ R ^ (n + 1) := pow_nonneg (zero_le_one.trans hR) _
  refine ⟨C * R ^ (n + 1), mul_nonneg hC hP,
    fun travel U hU J e he heR v hv y => ?_⟩
  let τ : M.Space →L[ℝ] M.Space :=
    circleTranslationContinuousLinear hM hT hD hγ travel
  let A : M.Space →L[ℝ] M.Space := inverseForwardJetLinear J n e v
  have hA (u : M.Space) : A u = inverseForwardJet J n e v u :=
    inverseForwardJetLinear_apply J n e v u
  have hsource (u : M.Space) :
      M.grading s (A u) ≤ C * multilinearTameSize
        (M.grading base) (M.grading H) (n + 1) (1 + M.grading H e)
          (Fin.cons (τ u) v) := by
    rw [hA u,
      circleShiftedChartCompose_orderedJet_eq_kernel hD hT hγ hM hI travel hU J n e he v u]
    exact hc e heR (τ u) v
  have hbound := linearMap_oneHigh_of_shiftedSourceKernel A (M.grading s)
    (M.grading base) (M.grading H) e v τ hC hR hv
    (circleTranslationContinuousLinear_grading_le hM hT hD hγ travel base)
    (circleTranslationContinuousLinear_grading_le hM hT hD hγ travel H) hsource y
  simpa only [hA] using hbound

end ContinuousFlexibility.Statements
