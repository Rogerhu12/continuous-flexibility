import ContinuousFlexibility.Analysis.N04PulledFieldsForwardFixedBase
import ContinuousFlexibility.Analysis.CircleAverageCompositionSmoothTame

/-!
# A common low base for the actual averaged circle composition

The genuine unit integral of linearly contracted forward-composition jets
preserves a specified low base, high loss, and constant. Applying this
fact to the common-base forward certificate keeps the low base before
every parameter order and the high loss before every spatial order.
The final statement concerns every tower of the original averaged map.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Compact averaging preserves each specified one-high bound, including
its low base, high loss, and constant. -/
theorem n04PulledFields_unitIntegral_oneHigh_of_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)]
    [∀ n, NormedSpace ℝ (F n)] [∀ n, CompleteSpace (F n)]
    {bond : ∀ n, F (n + 1) →L[ℝ] F n}
    (p : ℕ → Seminorm ℝ E) {f : E → ProjectiveLimit F bond}
    (J : SmoothDirections univ f) (L : ℝ → E →L[ℝ] E)
    (hL : Continuous (fun z : ℝ × E => L z.1 z.2))
    (hcontract : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s x, p s (L a x) ≤ p s x)
    (n s base loss : ℕ) (R C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, p base x ≤ R → ∀ v : Fin n → E,
      gradedSeminorm F bond s (J.D n x v) ≤
        C * tameJetSize p n s loss base x v)
    (x : E) (hx : p base x ≤ R) (v : Fin n → E) :
    gradedSeminorm F bond s
        ((smoothDirectionsUnitIntegralLinearFamily J L hL).D n x v) ≤
      C * tameJetSize p n s loss base x v := by
  rw [smoothDirectionsUnitIntegralLinearFamily_jet]
  apply projectiveUnitIntegral_grading_le _ s
    (mul_nonneg hC (tameJetSize_nonneg p n s loss base x v))
  intro a ha
  have hbase : p base (L a x) ≤ R := (hcontract a ha base x).trans hx
  have hsize := tameJetSize_linear_contraction p (L a).toLinearMap
    (hcontract a ha) n s loss base x v
  exact (hbound (L a x) hbase (fun i => L a (v i))).trans
    (mul_le_mul_of_nonneg_left hsize hC)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance n04PulledFieldsAverageFixedBasePairSMul (M : CircleModelData) :
    SMul ℝ (M.Space × M.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

include hI in
/-- Both inputs of the actual averaged composition retain a single low
base at every parameter order. The constant is uniform in travel and
in the supplied genuine tower. -/
theorem n04PulledFields_circleAverage_fixedBase_oneHigh :
    ∃ base loss : ℕ, ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (travel : ℕ → ℝ)
        (J : SmoothDirections univ (fun z : M.Space × M.Space =>
          circleAverageComposeLinear hM hT hD hγ travel z.1 z.2)),
      ∀ x : M.Space × M.Space, pairGrading M.grading M.grading base x ≤ R →
      ∀ v : Fin n → M.Space × M.Space,
        M.grading s (J.D n x v) ≤
          C * tameJetSize (pairGrading M.grading M.grading) n s (n + loss) base x v := by
  letI : ∀ n, CompleteSpace (M.level n) :=
    fun n => (hM.2.1 n).isComplete.completeSpace_coe
  let data := n04PulledFields_circleForward_fixedBase_oneHigh hD hT hγ hM hI
  let base : ℕ := data.choose
  let loss : ℕ := data.choose_spec.choose
  refine ⟨base, loss, fun n R hR s => ?_⟩
  let estimate := data.choose_spec.choose_spec n R hR s
  refine ⟨estimate.choose, estimate.choose_spec.1, fun travel J x hx v => ?_⟩
  let f : M.Space × M.Space → M.Space := fun z =>
    circleShiftedChartComposeContinuousLinear hM hT hD hγ travel z.1 z.2
  let JF : SmoothDirections univ f :=
    (smoothTameOn_circleChartComposition hM hT hD hγ hI travel).choose
  let L : ℝ → (M.Space × M.Space) →L[ℝ] M.Space × M.Space := fun a => pairScaleFirst a
  have hL : Continuous (fun z : ℝ × (M.Space × M.Space) => L z.1 z.2) :=
    continuous_pairScaleFirst
  let JA := smoothDirectionsUnitIntegralLinearFamily JF L hL
  have heq (z : M.Space × M.Space) (_hz : z ∈ (univ : Set (M.Space × M.Space))) :
      projectiveUnitIntegral (fun a => f (L a z))
          ((continuous_smoothDirections_univ JF).comp
            (hL.comp (continuous_id.prodMk continuous_const))) =
        circleAverageComposeLinear hM hT hD hγ travel z.1 z.2 :=
    (circleAverageComposeLinear_eq_unitIntegral hM hT hD hγ travel z _).symm
  let K : SmoothDirections univ (fun z : M.Space × M.Space =>
      circleAverageComposeLinear hM hT hD hγ travel z.1 z.2) := JA.congr heq
  have hjet : J.D n x v = JA.D n x v :=
    congrArg (fun A : (M.Space × M.Space) [×n]→L[ℝ] M.Space => A v)
      (J.unique K n x (mem_univ _))
  have hb := n04PulledFields_unitIntegral_oneHigh_of_bound
    (pairGrading M.grading M.grading) JF L hL
    (fun a ha t z => pairScaleFirst_grading_le M.grading M.grading ha t z)
    n s base (n + loss) R estimate.choose estimate.choose_spec.1
    (estimate.choose_spec.2 travel JF) x hx v
  exact (congrArg (M.grading s) hjet).le.trans hb

end ContinuousFlexibility.Statements
