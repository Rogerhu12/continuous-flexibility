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
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

local instance n04SelectorFixedBaseStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- The original inverse-flow displacement retains its physical circle
weight and one low base for all selectors and all parameter orders. -/
theorem N01Properties.selectorInverseCircle_fixedBase_oneHigh
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
    have h0 : HasInterpolation (stateGrading S) := coordinate_hasInterpolation_stateGrading hS
    obtain ⟨b, l, hb⟩ := h0
    refine ⟨b, l, fun a b c ha hab hbc => ?_⟩
    have h1 := hb a b c ha hab hbc
    obtain ⟨A, hA, hb⟩ := h1
    exact ⟨A, hA, fun z => hb z.val⟩
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
  sorry

end ContinuousFlexibility.Statements
