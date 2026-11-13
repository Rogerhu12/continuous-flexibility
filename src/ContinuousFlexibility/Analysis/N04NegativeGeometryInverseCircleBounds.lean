import ContinuousFlexibility.Analysis.CirclePositiveInverseFixedBaseBounds
import ContinuousFlexibility.Analysis.CircleTravelUniformJets
import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations
import ContinuousFlexibility.Analysis.TameFixedBaseCompositionBounds
import ContinuousFlexibility.Analysis.N04EndpointCircleFixedBaseBounds
import ContinuousFlexibility.Analysis.N01ReturnCircleUniformBounds
import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# A common low order for the actual inverse-circle families

The inverse-composition operator has one low order before every parameter
order and every travel selector. Composing its genuine tower with a
family having the same fixed-base property retains that quantifier order.
The actual inverse of the ordinary characteristic flow is the negative
diagonal of this operator, so its estimates use one common low order too.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

/- Use the same cached state instances as the statement layer. -/
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

local instance n04NegativeGeometryInverseBoundsCircleSMul (H : CircleModelData) :
    SMul ℝ (H.Space × H.Space) := Prod.instSMul

private theorem inverseOperator_fixedBase
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation H.grading)
    (JF : SmoothDirections univ (fun y : H.Space × H.Space =>
      circleShiftedChartComposeContinuousLinear hH hT hD hγ (fun _ => 0) y.1 y.2))
    (JP : ∀ travel : ℕ → ℝ, SmoothDirections (circlePositiveLiftDomain H ×ˢ univ)
      (fun y : H.Space × H.Space =>
        circlePositiveInverseComposeLinear hH hT hD hγ travel y.1 y.2))
    (a : ℝ) (ha : 0 < a) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ travel : ℕ → ℝ,
      ∀ K : SmoothDirections (circleUniformInverseDomain H a ×ˢ univ)
        (fun y : H.Space × H.Space =>
          circlePositiveInverseComposeLinear hH hT hD hγ travel y.1 y.2),
      ∀ y ∈ circleUniformInverseDomain H a ×ˢ univ,
        pairGrading H.grading H.grading B y ≤ R →
      ∀ v : Fin n → H.Space × H.Space,
        H.grading s (K.D n y v) ≤
          C * tameJetSize (pairGrading H.grading H.grading) n s L B y v := by
  let data := circlePositiveInverseComposeLinear_fixedBase_oneHigh
    (M := H) hD hT hγ hH hi JF (JP (fun _ => 0)) (a / 2) (half_pos ha)
  let B : ℕ := data.choose
  refine ⟨B, fun n => ?_⟩
  let orderData := data.choose_spec n
  let L : ℕ := orderData.choose
  refine ⟨L, fun R _hR s => ?_⟩
  let estimate := orderData.choose_spec (max R 1) (le_max_right _ _) s
  refine ⟨estimate.choose, estimate.choose_spec.1, fun travel K y hy hlow v => ?_⟩
  have hlower (m : ℕ) (θ : ℝ) :
      a / 2 ≤ deriv (circleAffineLift travel (H.decode y.1) 1 m) θ := by
    rw [circleAffineLift_deriv hH]
    exact interior_subset hy.1 m θ
  let K' : SmoothDirections (circleUniformInverseDomain H a ×ˢ univ)
      (fun y : H.Space × H.Space =>
        circlePositiveInverseComposeLinear hH hT hD hγ travel y.1 y.2) :=
    (JP travel).restrict ((circleUniformInverseDomain_isOpen H a).prod isOpen_univ)
      (fun y hy => ⟨circleUniformInverseDomain_subset_positive ha hy.1, hy.2⟩)
  have heq := congrArg (fun A : (H.Space × H.Space) [×n]→L[ℝ] H.Space => A v)
    (K.unique K' n y hy)
  have heq' : K.D n y v = (JP travel).D n y v := heq
  rw [heq']
  exact estimate.choose_spec.2 travel (JP travel) y hlower (hlow.trans (le_max_left _ _)) v

section InverseComposition

variable {I E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  {U : Set E} {f g : I → E → H.Space}

/-- One input base precedes all orders and all actual inverse towers.
The hypotheses describe the forward families and their genuine towers;
no inverse estimate is an input. -/
theorem n04NegativeGeometry_circleInverse_fixedBase_oneHigh
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation H.grading)
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (hIp : HasInterpolation (pairGrading realGrading p))
    (J : ∀ i, SmoothDirections U (fun x => (f i x, g i x)))
    (BJ : ℕ)
    (hJ : ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U → p BJ x ≤ R →
      ∀ v : Fin n → E,
        pairGrading H.grading H.grading s ((J i).D n x v) ≤
          C * tameJetSize p n s L BJ x v)
    (travel : I → ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hlower : ∀ i x, x ∈ U → ∀ m θ,
      a ≤ 1 + deriv (H.decode (f i x) m) θ) :
    ∃ B : ℕ, BJ ≤ B ∧ ∀ n : ℕ, ∃ L : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i (K : SmoothDirections U (fun x =>
        circlePositiveInverseComposeLinear hH hT hD hγ (travel i) (f i x) (g i x))),
      ∀ x ∈ U, p B x ≤ R → ∀ v : Fin n → E,
        H.grading s (K.D n x v) ≤ C * tameJetSize p n s L B x v := by
  classical
  let : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  let W : Set H.Space := circleUniformInverseDomain H a
  have hW : IsOpen W := circleUniformInverseDomain_isOpen H a
  have hsub : W ⊆ circlePositiveLiftDomain H := circleUniformInverseDomain_subset_positive ha
  let JP : ∀ travel : ℕ → ℝ, SmoothDirections (circlePositiveLiftDomain H ×ˢ univ)
      (fun y : H.Space × H.Space =>
        circlePositiveInverseComposeLinear hH hT hD hγ travel y.1 y.2) :=
    fun travel => (smoothTameOn_circlePositiveInverseComposeLinear hH hT hD hγ hi travel).choose
  let KP : ∀ i, SmoothDirections (W ×ˢ univ)
      (fun y : H.Space × H.Space =>
        circlePositiveInverseComposeLinear hH hT hD hγ (travel i) y.1 y.2) :=
    fun i => (JP (travel i)).restrict (hW.prod isOpen_univ)
      (fun y hy => ⟨hsub hy.1, hy.2⟩)
  let JF : SmoothDirections univ (fun y : H.Space × H.Space =>
      circleShiftedChartComposeContinuousLinear hH hT hD hγ (fun _ => 0) y.1 y.2) :=
    (exists_circleChartComposition_uniform_oneHigh hH hT hD hγ hi (fun _ => 0)).choose
  let inverseData := inverseOperator_fixedBase hH hT hD hγ hi JF JP a ha
  let BK : ℕ := inverseData.choose
  let d : ℕ → ℕ := fun n => (hJ n).choose
  let e : ℕ → ℕ := fun n => (inverseData.choose_spec n).choose
  have houter (n : ℕ) (R : ℝ) (_hR : 0 ≤ R) (s : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i y, y ∈ W ×ˢ univ →
        pairGrading H.grading H.grading BK y ≤ R →
        ∀ v : Fin n → H.Space × H.Space,
          H.grading s ((KP i).D n y v) ≤
            C * tameJetSize (pairGrading H.grading H.grading) n s (e n) BK y v := by
    let estimate := (inverseData.choose_spec n).choose_spec R _hR s
    exact ⟨estimate.choose, estimate.choose_spec.1,
      fun i y hy hlow v => estimate.choose_spec.2 (travel i) (KP i) y hy hlow v⟩
  have hmap (i : I) : MapsTo (fun x => (f i x, g i x)) U (W ×ˢ univ) :=
    fun x hx => ⟨mem_circleUniformInverseDomain hH hT hD hγ ha (f i x)
      (hlower i x hx), mem_univ _⟩
  let composeData := projectiveCompositionJets_fixedBase_oneHigh
    p (pairGrading H.grading H.grading) H.grading hp hIp J KP BJ BK d e
      (fun n => (hJ n).choose_spec) houter hmap
  let B : ℕ := composeData.choose
  refine ⟨B, composeData.choose_spec.1, fun n => ?_⟩
  let orderData := composeData.choose_spec.2 n
  let L : ℕ := orderData.choose
  refine ⟨L, fun R hR s => ?_⟩
  let estimate := orderData.choose_spec R hR s
  refine ⟨estimate.choose, estimate.choose_spec.1, fun i K x hx hlow v => ?_⟩
  let Kactual : SmoothDirections U (fun x =>
      circlePositiveInverseComposeLinear hH hT hD hγ (travel i) (f i x) (g i x)) :=
    smoothDirectionsOfJets (J i).open_domain
      (projectiveCompositionJets (fun x => (f i x, g i x)) (J i).D (KP i).D)
      (HasProjectiveJetsOn.comp_topological (J i).open_domain (KP i).open_domain
        (J i).hasProjectiveJetsOn (KP i).hasProjectiveJetsOn (hmap i))
  have heq := congrArg (fun A : E [×n]→L[ℝ] H.Space => A v) (K.unique Kactual n x hx)
  have heq' : K.D n x v =
      projectiveCompositionJets (fun x => (f i x, g i x)) (J i).D (KP i).D n x v := heq
  rw [heq']
  exact estimate.choose_spec.2 i x hx hlow v

end InverseComposition

private theorem inverseBounds_parameterInterpolation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) :
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

/-- The genuine inverse displacement of every closed-radius selector has
one common low order. Its bound is uniform in the selector and in the
choice of genuine tower of that same actual inverse. -/
theorem N01Properties.n04NegativeGeometry_selectorInverseCircle_fixedBase_oneHigh
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ) :
    ∃ B : ℕ, base ≤ B ∧ ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (hN.selectorInverseCircle hS hT rsel hrsel),
      ∀ x ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B x ≤ R →
      ∀ v : Fin n → StateDirections S × ℝ,
        (S.circle (3 / 4 : ℝ)).grading s (J.D n x v) ≤
          K * tameJetSize (pairGrading (sectorGrading S) realGrading) n s L B x v := by
  classical
  let p := pairGrading (sectorGrading S) realGrading
  let H := S.circle (3 / 4 : ℝ)
  let U := sectorNeighborhood S base ε ε
  let I := {rsel : ℕ → ℝ // ∀ m, rsel m ∈ Icc (C.left m) (C.right m)}
  let f : I → (StateDirections S × ℝ) → H.Space :=
    fun i => hN.endpointFlowCircle hS hT i.val i.property
  let J : ∀ i, SmoothDirections U (f i) :=
    fun i => (hN.exists_endpointFlowCircle_smoothDirections hS hT i.val i.property).choose
  let P : ∀ i, SmoothDirections U (fun x => (f i x, f i x)) :=
    fun i => smoothDirectionsProd (J i) (J i)
  obtain ⟨BJ, hBJ, hJ⟩ := hN.endpointFlowCircle_fixedBase_oneHigh hS hT
  have hP : ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i x, x ∈ U → p BJ x ≤ R →
      ∀ v : Fin n → StateDirections S × ℝ,
        pairGrading H.grading H.grading s ((P i).D n x v) ≤
          K * tameJetSize p n s L BJ x v := by
    intro n
    obtain ⟨L, hL⟩ := hJ n
    refine ⟨L, fun R hR s => ?_⟩
    obtain ⟨K, hK, hb⟩ := hL R hR s
    refine ⟨K + K, add_nonneg hK hK, fun i x hx hlow v => ?_⟩
    have h := hb i.val i.property (J i) x hx hlow v
    simpa only [P, smoothDirectionsProd, ContinuousMultilinearMap.prod_apply,
      pairGrading_apply, add_mul] using add_le_add h h
  have hp : Monotone p := sectorPairGrading_monotone S
  have hIp : HasInterpolation (pairGrading realGrading p) :=
    inverseBounds_parameterInterpolation hS
  have hlower (i : I) (x : StateDirections S × ℝ) (hx : x ∈ U) (m : ℕ) (θ : ℝ) :
      1 / 2 ≤ 1 + deriv (H.decode (f i x) m) θ := by
    rw [← circleAffineLift_deriv (hS.2.1 (3 / 4 : ℝ))
      (fun j => -opticalTravel D.w (C.left j) (i.val j)),
      hN.endpointFlowCircle_affineLift hS hT i.val i.property x hx]
    exact hflow x hx m (i.val m) (i.property m) θ
  obtain ⟨B, hB, hbound⟩ := n04NegativeGeometry_circleInverse_fixedBase_oneHigh
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 p hp hIp P BJ hP
    (fun i m => -opticalTravel D.w (C.left m) (i.val m)) (1 / 2) (by norm_num) hlower
  refine ⟨B, hBJ.trans hB, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hbound n
  refine ⟨L, fun R hR s => ?_⟩
  obtain ⟨K, hK, hb⟩ := hL R hR s
  refine ⟨K, hK, fun rsel hrsel Jinv x hx hlow v => ?_⟩
  let i : I := ⟨rsel, hrsel⟩
  let Jpositive : SmoothDirections U (fun x =>
      circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun m => -opticalTravel D.w (C.left m) (rsel m)) (f i x) (f i x)) :=
    (solveSmoothDirectionsPostcomp Jinv (-ContinuousLinearMap.id ℝ H.Space)).congrOn
      (fun x _ => by
        change -(-circlePositiveInverseComposeLinear _ _ _ _ _ _ _) = _
        exact neg_neg _)
  have h := hb i Jpositive x hx hlow v
  change H.grading s (-Jinv.D n x v) ≤ _ at h
  simpa only [map_neg_eq_map] using h

end ContinuousFlexibility.Statements
