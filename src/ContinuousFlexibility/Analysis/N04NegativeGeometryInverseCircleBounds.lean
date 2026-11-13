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
  let W : Set H.Space := circleUniformInverseDomain H a
  have hW : IsOpen W := circleUniformInverseDomain_isOpen H a
  have hsub : W ⊆ circlePositiveLiftDomain H := circleUniformInverseDomain_subset_positive ha
  let JP : ∀ i, SmoothDirections (circlePositiveLiftDomain H ×ˢ univ)
      (fun y : H.Space × H.Space =>
        circlePositiveInverseComposeLinear hH hT hD hγ (travel i) y.1 y.2) :=
    fun i => (smoothTameOn_circlePositiveInverseComposeLinear hH hT hD hγ hi (travel i)).choose
  let KP : ∀ i, SmoothDirections (W ×ˢ univ)
      (fun y : H.Space × H.Space =>
        circlePositiveInverseComposeLinear hH hT hD hγ (travel i) y.1 y.2) :=
    fun i => (JP i).restrict (hW.prod isOpen_univ)
      (fun y hy => ⟨hsub hy.1, hy.2⟩)
  let JF : SmoothDirections univ (fun y : H.Space × H.Space =>
      circleShiftedChartComposeContinuousLinear hH hT hD hγ (fun _ => 0) y.1 y.2) :=
    (exists_circleChartComposition_uniform_oneHigh hH hT hD hγ hi (fun _ => 0)).choose
  let JP₀ : SmoothDirections (circlePositiveLiftDomain H ×ˢ univ)
      (fun y : H.Space × H.Space =>
        circlePositiveInverseComposeLinear hH hT hD hγ (fun _ => 0) y.1 y.2) :=
    (smoothTameOn_circlePositiveInverseComposeLinear hH hT hD hγ hi (fun _ => 0)).choose
  obtain ⟨BK, hBK⟩ := circlePositiveInverseComposeLinear_fixedBase_oneHigh
    hD hT hγ hH hi JF JP₀ (a / 2) (half_pos ha)
  choose d hd using hJ
  choose e he using hBK
  have houter (n : ℕ) (R : ℝ) (_hR : 0 ≤ R) (s : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i y, y ∈ W ×ˢ univ →
        pairGrading H.grading H.grading BK y ≤ R →
        ∀ v : Fin n → H.Space × H.Space,
          H.grading s ((KP i).D n y v) ≤
            C * tameJetSize (pairGrading H.grading H.grading) n s (e n) BK y v := by
    obtain ⟨C, hC, hb⟩ := he n (max R 1) (le_max_right _ _) s
    refine ⟨C, hC, fun i y hy hlow v => ?_⟩
    exact hb (travel i) (JP i) y
      (fun m θ => (interior_subset hy.1 m θ).trans_eq
        (circleAffineLift_deriv hH (travel i) y.1 m θ).symm)
      (hlow.trans (le_max_left _ _)) v
  have hmap (i : I) : MapsTo (fun x => (f i x, g i x)) U (W ×ˢ univ) :=
    fun x hx => ⟨mem_circleUniformInverseDomain hH hT hD hγ ha (f i x)
      (hlower i x hx), mem_univ _⟩
  obtain ⟨B, hB, hb⟩ := projectiveCompositionJets_fixedBase_oneHigh
    p (pairGrading H.grading H.grading) H.grading hp hIp J KP BJ BK d e hd houter hmap
  refine ⟨B, hB, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hb n
  refine ⟨L, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hL R hR s
  refine ⟨C, hC, fun i K x hx hlow v => ?_⟩
  let Kactual := (J i).compCircle hH (KP i) (hmap i)
  have heq : K.D n x = Kactual.D n x := K.unique Kactual n x hx
  rw [heq]
  exact hc i x hx hlow v

end InverseComposition

local instance n04NegativeGeometryInverseBoundsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

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
  let P := fun i => smoothDirectionsProd (J i) (J i)
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
    change H.grading s ((J i).D n x v) + H.grading s ((J i).D n x v) ≤ _
    exact (add_le_add h h).trans_eq (by ring)
  have hp : Monotone p := sectorPairGrading_monotone S
  have hIp : HasInterpolation (pairGrading realGrading p) :=
    hasInterpolation_of_hasSmoothing (tamePairGrading_monotone (fun _ _ _ _ => le_rfl) hp)
      (hasSmoothing_pairGrading hasSmoothing_realGrading
        (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading))
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
