module

public import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseComposition
public import ContinuousFlexibility.Analysis.N04PulledFieldsAverageFixedBase
public import ContinuousFlexibility.Analysis.CirclePositiveInverseFixedBaseBounds
public import ContinuousFlexibility.Analysis.CircleUniformFamilyOperations

/-!
# Fixed-base families for the actual circle operations

The forward map, positive inverse and averaged divided difference are the
existing circle-model objects. Their strong seed estimates are combined
through the genuine finite-partition tower, retaining one low base before
all parameter orders and all external selectors.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem n04PulledFields_fixedBase_binary_maps
    {I E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    {Y : ℕ → Type*} [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, CompleteSpace (Y n)] {bond : ∀ n, Y (n + 1) →L[ℝ] Y n}
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (r : ℕ → Seminorm ℝ (ProjectiveLimit Y bond))
    (op : I → F → F → ProjectiveLimit Y bond)
    (hop : N04PulledFieldsFixedBaseFamily (pairGrading q q) r univ
      (fun i z => op i z.1 z.2))
    {U : Set E} {f g : I → E → F}
    (hp : Monotone p) (hPI : HasInterpolation (pairGrading realGrading p))
    (hU : IsOpen U) (hf : N04PulledFieldsFixedBaseFamily p q U f)
    (hg : N04PulledFieldsFixedBaseFamily p q U g) :
    N04PulledFieldsFixedBaseFamily p r U (fun i x => op i (f i x) (g i x)) := by
  exact hop.comp hp hPI (hf.prodMk hp hg) hU isOpen_univ (fun _ _ _ => mem_univ _)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance n04PulledFieldsCircleFixedBaseOperationsPairSMul (M : CircleModelData) :
    SMul ℝ (M.Space × M.Space) := Prod.instSMul

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

include hI

theorem n04PulledFields_fixedBase_circleComposition (travel : I → ℕ → ℝ) :
    N04PulledFieldsFixedBaseFamily (pairGrading M.grading M.grading) M.grading univ
      (fun i x => circleShiftedChartComposeLinear hM hT hD hγ (travel i) x.1 x.2) := by
  let J := fun i => (smoothTameOn_circleChartComposition hM hT hD hγ hI (travel i)).choose
  let data := n04PulledFields_circleForward_fixedBase_oneHigh hD hT hγ hM hI
  have h : N04PulledFieldsFixedBaseFamily (pairGrading M.grading M.grading) M.grading univ
      (fun i x => circleShiftedChartComposeContinuousLinear hM hT hD hγ (travel i) x.1 x.2) := by
    refine ⟨J, data.choose, fun n => n + data.choose_spec.choose, fun n R hR s => ?_⟩
    let estimate := data.choose_spec.choose_spec n R hR s
    exact ⟨estimate.choose, estimate.choose_spec.1,
      fun i x _ => estimate.choose_spec.2 (travel i) (J i) x⟩
  exact h.congr (fun i x _ =>
    circleShiftedChartComposeContinuousLinear_apply hM hT hD hγ (travel i) x.1 x.2)

theorem n04PulledFields_fixedBase_circleAverage (travel : I → ℕ → ℝ) :
    N04PulledFieldsFixedBaseFamily (pairGrading M.grading M.grading) M.grading univ
      (fun i x => circleAverageComposeLinear hM hT hD hγ (travel i) x.1 x.2) := by
  let J := fun i => (smoothTameOn_circleAverageComposeLinear hM hT hD hγ hI (travel i)).choose
  let data := n04PulledFields_circleAverage_fixedBase_oneHigh hD hT hγ hM hI
  refine ⟨J, data.choose, fun n => n + data.choose_spec.choose, fun n R hR s => ?_⟩
  let estimate := data.choose_spec.choose_spec n R hR s
  exact ⟨estimate.choose, estimate.choose_spec.1,
    fun i x _ => estimate.choose_spec.2 (travel i) (J i) x⟩

theorem n04PulledFields_fixedBase_circleInverse
    (travel : I → ℕ → ℝ) (a : ℝ) (ha : 0 < a) :
    N04PulledFieldsFixedBaseFamily (pairGrading M.grading M.grading) M.grading
      (circleUniformInverseDomain M a ×ˢ univ)
      (fun i x => circlePositiveInverseComposeLinear hM hT hD hγ (travel i) x.1 x.2) := by
  let JF := (smoothTameOn_circleChartComposition hM hT hD hγ hI (fun _ => 0)).choose
  let JP := fun travel : ℕ → ℝ =>
    (smoothTameOn_circlePositiveInverseComposeLinear hM hT hD hγ hI travel).choose
  let data := circlePositiveInverseComposeLinear_fixedBase_oneHigh
    hD hT hγ hM hI JF (JP (fun _ => 0)) (a / 2) (half_pos ha)
  refine ⟨fun i => smoothDirectionsRestrict (JP (travel i))
    ((circleUniformInverseDomain_isOpen M a).prod isOpen_univ)
    (fun _ hx => ⟨circleUniformInverseDomain_subset_positive ha hx.1, hx.2⟩),
    data.choose, fun n => (data.choose_spec n).choose, fun n R hR s => ?_⟩
  let estimate := (data.choose_spec n).choose_spec (max R 1) (le_max_right _ _) s
  refine ⟨estimate.choose, estimate.choose_spec.1, fun i x hx hbx v => ?_⟩
  have hlow : ∀ m θ, a / 2 ≤ deriv (circleAffineLift (travel i) (M.decode x.1) 1 m) θ := by
    intro m θ
    rw [circleAffineLift_deriv hM]
    exact interior_subset hx.1 m θ
  exact estimate.choose_spec.2 (travel i) (JP (travel i)) x hlow
    (hbx.trans (le_max_left _ _)) v

section Maps

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {p : ℕ → Seminorm ℝ E} {U : Set E} {f g : I → E → M.Space}

theorem n04PulledFields_fixedBase_circleCompose_maps
    (travel : I → ℕ → ℝ) (hp : Monotone p)
    (hPI : HasInterpolation (pairGrading realGrading p)) (hU : IsOpen U)
    (hf : N04PulledFieldsFixedBaseFamily p M.grading U f)
    (hg : N04PulledFieldsFixedBaseFamily p M.grading U g) :
    N04PulledFieldsFixedBaseFamily p M.grading U
      (fun i x => circleShiftedChartComposeLinear hM hT hD hγ (travel i) (f i x) (g i x)) := by
  letI : ∀ n, CompleteSpace (M.level n) :=
    fun n => (hM.2.1 n).isComplete.completeSpace_coe
  exact n04PulledFields_fixedBase_binary_maps p M.grading M.grading
    (fun i x y => circleShiftedChartComposeLinear hM hT hD hγ (travel i) x y)
    (n04PulledFields_fixedBase_circleComposition hD hT hγ hM hI travel) hp hPI hU hf hg

theorem n04PulledFields_fixedBase_circleInverse_maps
    (travel : I → ℕ → ℝ) (a : ℝ) (ha : 0 < a) (hp : Monotone p)
    (hPI : HasInterpolation (pairGrading realGrading p)) (hU : IsOpen U)
    (hlower : ∀ i x, x ∈ U → ∀ m θ, a ≤ 1 + deriv (M.decode (f i x) m) θ)
    (hf : N04PulledFieldsFixedBaseFamily p M.grading U f)
    (hg : N04PulledFieldsFixedBaseFamily p M.grading U g) :
    N04PulledFieldsFixedBaseFamily p M.grading U
      (fun i x => circlePositiveInverseComposeLinear hM hT hD hγ (travel i) (f i x) (g i x)) := by
  letI : ∀ n, CompleteSpace (M.level n) :=
    fun n => (hM.2.1 n).isComplete.completeSpace_coe
  exact (n04PulledFields_fixedBase_circleInverse hD hT hγ hM hI travel a ha).comp
    hp hPI (hf.prodMk hp hg) hU ((circleUniformInverseDomain_isOpen M a).prod isOpen_univ)
    (fun i x hx => ⟨mem_circleUniformInverseDomain hM hT hD hγ ha (f i x)
      (hlower i x hx), mem_univ _⟩)

theorem n04PulledFields_fixedBase_circleAverage_maps
    (travel : I → ℕ → ℝ) (hp : Monotone p)
    (hPI : HasInterpolation (pairGrading realGrading p)) (hU : IsOpen U)
    (hf : N04PulledFieldsFixedBaseFamily p M.grading U f)
    (hg : N04PulledFieldsFixedBaseFamily p M.grading U g) :
    N04PulledFieldsFixedBaseFamily p M.grading U
      (fun i x => circleAverageComposeLinear hM hT hD hγ (travel i) (f i x) (g i x)) := by
  letI : ∀ n, CompleteSpace (M.level n) :=
    fun n => (hM.2.1 n).isComplete.completeSpace_coe
  exact n04PulledFields_fixedBase_binary_maps p M.grading M.grading
    (fun i x y => circleAverageComposeLinear hM hT hD hγ (travel i) x y)
    (n04PulledFields_fixedBase_circleAverage hD hT hγ hM hI travel) hp hPI hU hf hg

end Maps

end ContinuousFlexibility.Statements
