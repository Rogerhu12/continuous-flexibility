import ContinuousFlexibility.Analysis.N04EndpointCircleFixedBaseBounds
import ContinuousFlexibility.Analysis.CirclePositiveInverseFixedBaseBounds
import ContinuousFlexibility.Analysis.TameFixedBaseCompositionBounds
import ContinuousFlexibility.Analysis.N01ReturnCircleUniformBounds
import ContinuousFlexibility.Analysis.TameProductDirections
import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations

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

/-- A tower of `h` agrees with the negative of any genuine jet family of
`c` when `h = -c` on the open domain. -/
private theorem jet_eq_neg_of_hasProjectiveJetsOn
    {X F : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F]
    [T2Space F]
    {U : Set X} (hU : IsOpen U) {c h : X → F} (Jc : ProjectiveJetFamily X F)
    (hc : HasProjectiveJetsOn c Jc U) (hh : ∀ y ∈ U, -c y = h y)
    (J : SmoothDirections U h) (n : ℕ) (x : X) (hx : x ∈ U) (v : Fin n → X) :
    J.D n x v = -Jc n x v := by
  let JC : SmoothDirections U c := smoothDirectionsOfJets hU Jc hc
  let JA : SmoothDirections U h :=
    (solveSmoothDirectionsPostcomp JC (-ContinuousLinearMap.id ℝ F)).congr
      (fun y hy => by
        simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
        exact hh y hy)
  have hjet := congrArg (fun A : X [×n]→L[ℝ] F => A v) (J.unique JA n x hx)
  simpa only [JA, SmoothDirections.congr, solveSmoothDirectionsPostcomp,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, JC,
    smoothDirectionsOfJets] using hjet

set_option backward.isDefEq.respectTransparency false in
/-- The negative of a composed circle tower has the jets of the negated
ordered-partition composition, on the same open domain. -/
private theorem circle_neg_composition_jet_eq
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {T : MaterialData} {γ : ℝ} {M : CircleModelData} (hM : IsCircleModel T γ M)
    {U : Set X} {V : Set (M.Space × M.Space)} (hU : IsOpen U)
    {u : X → M.Space × M.Space} {w : M.Space × M.Space → M.Space} {h : X → M.Space}
    (JF : SmoothDirections U u) (KP : SmoothDirections V w) (hmap : MapsTo u U V)
    (hh : ∀ y ∈ U, -w (u y) = h y)
    (J : SmoothDirections U h) (n : ℕ) (x : X) (hx : x ∈ U) (v : Fin n → X) :
    J.D n x v = -projectiveCompositionJets u JF.D KP.D n x v :=
  jet_eq_neg_of_hasProjectiveJetsOn hU _ (JF.compCircle hM KP hmap).hasProjectiveJetsOn
    hh J n x hx v

/-- The fixed-base composition bound, transported to every tower of the
negated composition. All spaces and families are abstract here. -/
private theorem negComposition_fixedBase_oneHigh
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {T : MaterialData} {γ : ℝ} {M : CircleModelData} (hM : IsCircleModel T γ M)
    {I : Type*} (p : ℕ → Seminorm ℝ X) (hp : Monotone p)
    (hIp : HasInterpolation (pairGrading realGrading p))
    {U : Set X} {V : Set (M.Space × M.Space)} (hU : IsOpen U)
    {u : I → X → M.Space × M.Space} {w : I → M.Space × M.Space → M.Space}
    (JF : ∀ i, SmoothDirections U (u i)) (KP : ∀ i, SmoothDirections V (w i))
    (BE BP : ℕ) (d e : ℕ → ℕ)
    (hJF : ∀ n R, 0 ≤ R → ∀ s, ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, x ∈ U → p BE x ≤ R → ∀ v : Fin n → X,
        pairGrading M.grading M.grading s ((JF i).D n x v) ≤
          A * tameJetSize p n s (d n) BE x v)
    (hKP : ∀ n R, 0 ≤ R → ∀ s, ∃ A : ℝ, 0 ≤ A ∧
      ∀ i y, y ∈ V → pairGrading M.grading M.grading BP y ≤ R →
        ∀ v : Fin n → M.Space × M.Space,
          M.grading s ((KP i).D n y v) ≤
            A * tameJetSize (pairGrading M.grading M.grading) n s (e n) BP y v)
    (hmap : ∀ i, MapsTo (u i) U V)
    (h : I → X → M.Space) (hh : ∀ i, ∀ y ∈ U, -w i (u i y) = h i y) :
    ∃ B : ℕ, BE ≤ B ∧ ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i (J : SmoothDirections U (h i)), ∀ x ∈ U, p B x ≤ R →
        ∀ v : Fin n → X, M.grading s (J.D n x v) ≤ K * tameJetSize p n s L B x v := by
  have hcomp := projectiveCompositionJets_fixedBase_oneHigh
    p (pairGrading M.grading M.grading) M.grading hp hIp JF KP BE BP d e hJF hKP hmap
  obtain ⟨B, hB, hbound⟩ := hcomp
  refine ⟨B, hB, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hbound n
  refine ⟨L, fun R hR s => ?_⟩
  obtain ⟨A, hA, hb⟩ := hL R hR s
  refine ⟨A, hA, fun i J x hx hbx v => ?_⟩
  have heq : J.D n x v = -projectiveCompositionJets (u i) (JF i).D (KP i).D n x v := sorry
  rw [heq, map_neg_eq_map]
  exact hb i x hx hbx v

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
  have hEall := hN.endpointFlowCircle_fixedBase_oneHigh hS hT
  obtain ⟨BE, hBE, hE⟩ := hEall
  choose d hd using hE
  have hPall := circlePositiveInverseComposeLinear_fixedBase_oneHigh
    hN.1.1 hT hγ hH hHI J₀ (JP (fun _ => 0)) (1 / 4) (by norm_num)
  obtain ⟨BP, hP⟩ := hPall
  choose e he using hP
  have hJF : ∀ n R, 0 ≤ R → ∀ s, ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, x ∈ U → p BE x ≤ R → ∀ v : Fin n → (StateDirections S × ℝ),
        q s ((JF i).D n x v) ≤ A * tameJetSize p n s (d n) BE x v := by
    intro n R hR s
    have hdn := hd n R hR s
    obtain ⟨A, hA, hb⟩ := hdn
    refine ⟨2 * A, mul_nonneg (by norm_num) hA, fun i x hx hbx v => ?_⟩
    have hh := hb i.val i.property (JE i) x hx hbx v
    simpa only [JF, smoothDirectionsProd, ContinuousMultilinearMap.prod_apply,
      q, pairGrading_apply, two_mul, add_mul] using add_le_add hh hh
  have hKP : ∀ n R, 0 ≤ R → ∀ s, ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, x ∈ V → q BP x ≤ R → ∀ v : Fin n → H.Space × H.Space,
        H.grading s ((KP i).D n x v) ≤ A * tameJetSize q n s (e n) BP x v := by
    intro n R hR s
    have hen := he n (max R 1) (le_max_right _ _) s
    obtain ⟨A, hA, hb⟩ := hen
    refine ⟨A, hA, fun i x hx hbx v => ?_⟩
    have hlow : ∀ m θ, (1 / 4 : ℝ) ≤
        deriv (circleAffineLift (travel i) (H.decode x.1) 1 m) θ := by
      intro m θ
      rw [circleAffineLift_deriv hH]
      have hh : (1 / 2 : ℝ) / 2 ≤ 1 + deriv (H.decode x.1 m) θ :=
        interior_subset hx.1 m θ
      convert hh using 1 <;> norm_num
    exact hb (travel i) (JP (travel i)) x hlow (hbx.trans (le_max_left _ _)) v
  have hmap (i : I) : MapsTo (f i) U V := by
    intro x hx
    refine ⟨mem_circleUniformInverseDomain hH hT hN.1.1 hγ (by norm_num) (endpoint i x)
      (fun m θ => ?_), mem_univ _⟩
    exact hN.endpointFlowCircle_uniform_lower hS hT hflow i.val i.property x hx m θ
  sorry

end ContinuousFlexibility.Statements
