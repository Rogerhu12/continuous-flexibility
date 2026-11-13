import ContinuousFlexibility.Analysis.N04EndpointCircleFixedBaseBounds
import ContinuousFlexibility.Analysis.CirclePositiveInverseFixedBaseBounds
import ContinuousFlexibility.Analysis.TameFixedBaseCompositionBounds
import ContinuousFlexibility.Analysis.N01ReturnCircleUniformBounds
import ContinuousFlexibility.Analysis.TameProductDirections

/-!
# Fixed-base estimates for the actual inverse flow displacement

The endpoint function and the inverse function are the existing realized
circle objects. The actual uniform slope lower bound places their diagonal
in one common open inverse domain. Ordered-partition composition then keeps
one input base before all parameter orders, and uniqueness transfers the
estimate to every given tower of the literal selector inverse.

Restored from the reviewed 152-line source in archive commit `0227745d`,
`source-snapshot-38/positive/reconstructed/N04SelectorInverseCircleFixedBaseBounds.lean`.
The archived source was reviewed without compilation.  This module retains
its fixed seminorm-evenness rewrite, gives its declaration a distinct name,
and projects existential witnesses directly to keep the graded goals small.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

local instance n04PulledFieldsSelectorFixedBaseStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

private theorem n04PulledFields_negativeTowerJet
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
    {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (K : SmoothDirections U (fun x => -f x))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    K.D n x v = -J.D n x v := by
  let N : SmoothDirections U (fun x => -f x) :=
    (solveSmoothDirectionsPostcomp J (-ContinuousLinearMap.id ℝ F)).congrOn
      (fun _ _ => rfl)
  have hjet := congrArg (fun A : E [×n]→L[ℝ] F => A v) (K.unique N n x hx)
  simp only [N, SmoothDirections.congrOn, solveSmoothDirectionsPostcomp,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] at hjet
  exact hjet

/-- The original inverse-flow displacement retains its physical circle
weight and one low base for all selectors and all parameter orders. -/
theorem N01Properties.n04PulledFields_selectorInverseCircle_fixedBase_oneHigh
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
        deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2) :
    ∃ B : ℕ, base ≤ B ∧ ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (hN.selectorInverseCircle hS hT rsel hrsel),
      ∀ x ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B x ≤ R →
      ∀ v : Fin n → (StateDirections S × ℝ),
        (S.circle (3 / 4 : ℝ)).grading s (J.D n x v) ≤
          K * tameJetSize (pairGrading (sectorGrading S) realGrading) n s L B x v := by
  classical
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (sectorGrading S) realGrading
  let q := pairGrading H.grading H.grading
  let U := sectorNeighborhood S base ε ε
  let V := circleUniformInverseDomain H (1 / 2) ×ˢ (univ : Set H.Space)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hγ : (0 : ℝ) < 3 / 4 := by norm_num
  have hHI : HasInterpolation H.grading := (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  have hp : Monotone p := sectorPairGrading_monotone S
  have hr : Monotone realGrading := fun _ _ _ _ => le_rfl
  have hsector : HasInterpolation (sectorGrading S) := by
    let data := coordinate_hasInterpolation_stateGrading hS
    let b₀ : ℕ := data.choose
    let ell : ℕ := data.choose_spec.choose
    refine ⟨b₀, ell, fun a b c ha hab hbc => ?_⟩
    let estimate := data.choose_spec.choose_spec a b c ha hab hbc
    exact ⟨estimate.choose, estimate.choose_spec.1, fun z => estimate.choose_spec.2 z.val⟩
  have hIp : HasInterpolation (pairGrading realGrading p) :=
    coordinate_hasInterpolation_pair hr hp coordinate_hasInterpolation_realGrading
      (coordinate_hasInterpolation_pair (sectorGrading_monotone S) hr
        hsector coordinate_hasInterpolation_realGrading)
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  have hV : IsOpen V := (circleUniformInverseDomain_isOpen H (1 / 2)).prod isOpen_univ
  have hsub : V ⊆ circlePositiveLiftDomain H ×ˢ univ :=
    fun x hx => ⟨circleUniformInverseDomain_subset_positive (by norm_num) hx.1, hx.2⟩
  let I := {rsel : ℕ → ℝ // ∀ m, rsel m ∈ Icc (C.left m) (C.right m)}
  let travel : I → ℕ → ℝ := fun i m => -opticalTravel D.w (C.left m) (i.val m)
  let endpoint : I → (StateDirections S × ℝ) → H.Space :=
    fun i => hN.endpointFlowCircle hS hT i.val i.property
  let JE : ∀ i : I, SmoothDirections U (endpoint i) :=
    fun i => (hN.smoothTameOn_endpointFlowCircle hS hT i.val i.property).choose
  let f : I → (StateDirections S × ℝ) → H.Space × H.Space :=
    fun i x => (endpoint i x, endpoint i x)
  let JF : ∀ i : I, SmoothDirections U (f i) := fun i => smoothDirectionsProd (JE i) (JE i)
  let P : (ℕ → ℝ) → H.Space × H.Space → H.Space := fun t x =>
    circlePositiveInverseComposeLinear hH hT hN.1.1 hγ t x.1 x.2
  let JP : ∀ t : ℕ → ℝ,
      SmoothDirections (circlePositiveLiftDomain H ×ˢ univ) (P t) :=
    fun t => (smoothTameOn_circlePositiveInverseComposeLinear hH hT hN.1.1 hγ hHI t).choose
  let J₀ : SmoothDirections univ (fun x : H.Space × H.Space =>
      circleShiftedChartComposeContinuousLinear hH hT hN.1.1 hγ (fun _ => 0) x.1 x.2) :=
    (exists_circleChartComposition_uniform_oneHigh hH hT hN.1.1 hγ hHI (fun _ => 0)).choose
  let KP : ∀ i : I, SmoothDirections V (P (travel i)) :=
    fun i => (JP (travel i)).restrict hV hsub
  let endpointData := hN.endpointFlowCircle_fixedBase_oneHigh hS hT
  let BE : ℕ := endpointData.choose
  let d : ℕ → ℕ := fun n => (endpointData.choose_spec.2 n).choose
  let inverseData := circlePositiveInverseComposeLinear_fixedBase_oneHigh
    hN.1.1 hT hγ hH hHI J₀ (JP (fun _ => 0)) (1 / 4) (by norm_num)
  let BP : ℕ := inverseData.choose
  let e : ℕ → ℕ := fun n => (inverseData.choose_spec n).choose
  have hJF : ∀ n R, 0 ≤ R → ∀ s, ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, x ∈ U → p BE x ≤ R → ∀ v : Fin n → (StateDirections S × ℝ),
        q s ((JF i).D n x v) ≤ A * tameJetSize p n s (d n) BE x v := by
    intro n R hR s
    let estimate := (endpointData.choose_spec.2 n).choose_spec R hR s
    let A : ℝ := estimate.choose
    refine ⟨2 * A, mul_nonneg (by norm_num) estimate.choose_spec.1,
      fun i x hx hbx v => ?_⟩
    have hh := estimate.choose_spec.2 i.val i.property (JE i) x hx hbx v
    simpa only [JF, smoothDirectionsProd, ContinuousMultilinearMap.prod_apply,
      q, pairGrading_apply, two_mul, add_mul] using add_le_add hh hh
  have hKP : ∀ n R, 0 ≤ R → ∀ s, ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, x ∈ V → q BP x ≤ R → ∀ v : Fin n → H.Space × H.Space,
        H.grading s ((KP i).D n x v) ≤ A * tameJetSize q n s (e n) BP x v := by
    intro n R hR s
    let estimate := (inverseData.choose_spec n).choose_spec
      (max R 1) (le_max_right _ _) s
    refine ⟨estimate.choose, estimate.choose_spec.1, fun i x hx hbx v => ?_⟩
    have hlow : ∀ m θ, (1 / 4 : ℝ) ≤
        deriv (circleAffineLift (travel i) (H.decode x.1) 1 m) θ := by
      intro m θ
      rw [circleAffineLift_deriv hH]
      have hh : (1 / 2 : ℝ) / 2 ≤ 1 + deriv (H.decode x.1 m) θ :=
        interior_subset hx.1 m θ
      convert hh using 1 <;> norm_num
    exact estimate.choose_spec.2 (travel i) (JP (travel i)) x hlow
      (hbx.trans (le_max_left _ _)) v
  have hmap (i : I) : MapsTo (f i) U V := by
    intro x hx
    refine ⟨mem_circleUniformInverseDomain hH hT hN.1.1 hγ (by norm_num) (endpoint i x)
      (fun m θ => ?_), mem_univ _⟩
    exact hN.endpointFlowCircle_uniform_lower hS hT hflow i.val i.property x hx m θ
  let compositionData := projectiveCompositionJets_fixedBase_oneHigh
    p q H.grading hp hIp JF KP BE BP d e hJF hKP hmap
  let B : ℕ := compositionData.choose
  refine ⟨B, endpointData.choose_spec.1.trans compositionData.choose_spec.1, fun n => ?_⟩
  let lossData := compositionData.choose_spec.2 n
  let L : ℕ := lossData.choose
  refine ⟨L, fun R hR s => ?_⟩
  let estimate := lossData.choose_spec R hR s
  refine ⟨estimate.choose, estimate.choose_spec.1, fun rsel hrsel J x hx hbx v => ?_⟩
  let i : I := ⟨rsel, hrsel⟩
  let JC : SmoothDirections U (P (travel i) ∘ f i) :=
    smoothDirectionsOfJets hU (projectiveCompositionJets (f i) (JF i).D (KP i).D)
      (HasProjectiveJetsOn.comp_topological hU hV
        (JF i).hasProjectiveJetsOn (KP i).hasProjectiveJetsOn (hmap i))
  have heq : J.D n x v = -JC.D n x v :=
    n04PulledFields_negativeTowerJet JC J n x hx v
  rw [heq, map_neg_eq_map]
  change H.grading s (projectiveCompositionJets (f i) (JF i).D (KP i).D n x v) ≤ _
  exact estimate.choose_spec.2 i x hx hbx v

end ContinuousFlexibility.Statements
