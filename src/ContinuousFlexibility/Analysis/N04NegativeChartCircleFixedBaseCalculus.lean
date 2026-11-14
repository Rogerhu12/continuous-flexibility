module

public import ContinuousFlexibility.Analysis.N04NegativeChartCircleCompositionBounds
public import ContinuousFlexibility.Analysis.N04NegativeChartFixedBaseFamilies
public import ContinuousFlexibility.Analysis.N04NegativeGeometryInverseCircleCompositionBounds
public import ContinuousFlexibility.Analysis.CircleUniformFamilyOperations
public import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# Fixed-base calculus for the actual circle maps

Forward composition uses the explicit full-jet bound. Positive inverse
composition uses the actual inverse-family theorem. Both operations keep
the common source base before all parameter and angular orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance n04NegativeChartCircleCalculusPairSMul (H : CircleModelData) :
    SMul ℝ (H.Space × H.Space) := Prod.instSMul

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}

theorem n04FixedBaseSmoothFamilyOn_circleComposition
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation H.grading)
    (travel : I → ℕ → ℝ) :
    N04FixedBaseSmoothFamilyOn (pairGrading H.grading H.grading) H.grading univ
      (fun i x => circleShiftedChartComposeLinear hH hT hD hγ (travel i) x.1 x.2) := by
  let J := fun i =>
    (exists_circleChartComposition_smoothDirections hH hT hD hγ hi (travel i)).choose
  let data := n04NegativeChart_circleComposition_fixedBase_oneHigh hH hT hD hγ hi
  let B : ℕ := data.choose
  let d : ℕ := data.choose_spec.choose
  have hJ : N04FixedBaseSmoothFamilyOn (pairGrading H.grading H.grading) H.grading univ
      (fun i x => circleShiftedChartComposeContinuousLinear hH hT hD hγ (travel i) x.1 x.2) := by
    refine ⟨J, B, fun n => ⟨n + d, fun R hR s => ?_⟩⟩
    let estimate := data.choose_spec.choose_spec n R hR s
    exact ⟨estimate.choose, estimate.choose_spec.1, fun i x hx hlow v =>
      estimate.choose_spec.2 (travel i) univ (J i) x hx hlow v⟩
  exact hJ.congr (fun i x _ =>
    circleShiftedChartComposeContinuousLinear_apply hH hT hD hγ (travel i) x.1 x.2)

section Maps

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {p : ℕ → Seminorm ℝ E} {U : Set E} {f g : I → E → H.Space}

theorem n04FixedBaseSmoothFamilyOn_circleCompose_maps
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation H.grading)
    (travel : I → ℕ → ℝ) (hp : Monotone p)
    (hIp : HasInterpolation (pairGrading realGrading p)) (hU : IsOpen U)
    (hf : N04FixedBaseSmoothFamilyOn p H.grading U f)
    (hg : N04FixedBaseSmoothFamilyOn p H.grading U g) :
    N04FixedBaseSmoothFamilyOn p H.grading U
      (fun i x => circleShiftedChartComposeLinear hH hT hD hγ (travel i) (f i x) (g i x)) := by
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  let outer : I → (H.Space × H.Space) → H.Space := fun i x =>
    circleShiftedChartComposeLinear hH hT hD hγ (travel i) x.1 x.2
  let inner : I → E → H.Space × H.Space := fun i x => (f i x, g i x)
  have ho : N04FixedBaseSmoothFamilyOn (pairGrading H.grading H.grading) H.grading
      univ outer := n04FixedBaseSmoothFamilyOn_circleComposition hH hT hD hγ hi travel
  have hj : N04FixedBaseSmoothFamilyOn p (pairGrading H.grading H.grading) U inner :=
    hf.prodMk hp hg
  exact N04FixedBaseSmoothFamilyOn.comp (Y := fun n => H.level n) (bond := H.bond)
    (q := pairGrading H.grading H.grading) (r := H.grading) (f := inner) (g := outer)
    ho hp hIp hj hU isOpen_univ (fun _ _ _ => mem_univ _)

theorem n04FixedBaseSmoothFamilyOn_circleInverse_maps
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation H.grading)
    (travel : I → ℕ → ℝ) (a : ℝ) (ha : 0 < a) (hp : Monotone p)
    (hIp : HasInterpolation (pairGrading realGrading p)) (hU : IsOpen U)
    (hlower : ∀ i x, x ∈ U → ∀ m θ, a ≤ 1 + deriv (H.decode (f i x) m) θ)
    (hf : N04FixedBaseSmoothFamilyOn p H.grading U f)
    (hg : N04FixedBaseSmoothFamilyOn p H.grading U g) :
    N04FixedBaseSmoothFamilyOn p H.grading U
      (fun i x => circlePositiveInverseComposeLinear hH hT hD hγ (travel i) (f i x) (g i x)) := by
  let smoothData := uniformSmoothFamilyOn_circleInverse_maps hH hT hD hγ hi travel a ha hp hU
    hlower hf.uniform hg.uniform
  let K := smoothData.choose
  obtain ⟨J, BJ, hJ⟩ := hf.prodMk hp hg
  let data := n04NegativeGeometry_circleInverse_fixedBase_oneHigh
    hH hT hD hγ hi p hp hIp J BJ hJ travel a ha hlower
  refine ⟨K, data.choose, fun n => ?_⟩
  let orderData := data.choose_spec.2 n
  refine ⟨orderData.choose, fun R hR s => ?_⟩
  let estimate := orderData.choose_spec R hR s
  exact ⟨estimate.choose, estimate.choose_spec.1, fun i x hx hlow v =>
    estimate.choose_spec.2 i (K i) x hx hlow v⟩

end Maps

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- The parameter grading used by N01 has the interpolation property
needed by fixed-base composition, including its affine constant slot. -/
theorem n04FixedBase_sectorParameter_hasInterpolation
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) :
    HasInterpolation (pairGrading realGrading (pairGrading (sectorGrading S) realGrading)) := by
  have hr : Monotone realGrading := fun _ _ _ _ => le_rfl
  have hsector : HasInterpolation (sectorGrading S) := by
    let data : HasInterpolation (stateGrading S) := coordinate_hasInterpolation_stateGrading hS
    let b : ℕ := data.choose
    let l : ℕ := data.choose_spec.choose
    refine ⟨b, l, fun a b c ha hab hbc => ?_⟩
    let estimate := data.choose_spec.choose_spec a b c ha hab hbc
    exact ⟨estimate.choose, estimate.choose_spec.1, fun z => estimate.choose_spec.2 z.val⟩
  exact coordinate_hasInterpolation_pair hr (sectorPairGrading_monotone S)
    coordinate_hasInterpolation_realGrading
    (coordinate_hasInterpolation_pair (sectorGrading_monotone S) hr
      hsector coordinate_hasInterpolation_realGrading)

end ContinuousFlexibility.Statements
