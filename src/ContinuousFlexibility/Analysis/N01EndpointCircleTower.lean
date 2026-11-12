import ContinuousFlexibility.Analysis.N01EndpointOneHigh
import ContinuousFlexibility.Analysis.N01EndpointSecondEnvelope
import ContinuousFlexibility.Analysis.N01EndpointZeroCircleMember
import ContinuousFlexibility.Analysis.CircleLocalPositiveJetAssembly
import ContinuousFlexibility.Analysis.SmoothDirectionsGluing

/-!
# The actual endpoint flow in the physical circle topology

All scalar jets are realized in the supplied circle model. At each
parameter order, weighted Taylor estimates and a bounded low-order box
give continuity of the actual jets. The resulting tower has genuine
projective line derivatives on the full original sector domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointCircleTowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem circleTower_pair_origin_mem
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) {δ : ℝ} (hδ : 0 < δ) :
    (0 : E × ℝ) ∈ {z | p z.1 < δ ∧ |z.2| < δ} :=
  ⟨p.map_zero'.trans_lt hδ, (abs_zero : |(0 : ℝ)| = 0).trans_lt hδ⟩

def N01Properties.endpointFlowCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) : CircleSpace S := by
  classical
  exact if hz : z ∈ sectorNeighborhood S base ε ε then
    circleRealize (hS.2.1 (3 / 4 : ℝ))
      (hN.endpointFlowScalarJets hS hT rsel hrsel 0 z Fin.elim0)
      (hN.endpointFlowScalarJets_zero_circleMember hS hT rsel hrsel z hz)
  else 0

theorem N01Properties.endpointFlowCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    (S.circle (3 / 4 : ℝ)).decode (hN.endpointFlowCircle hS hT rsel hrsel z) =
      hN.endpointFlowScalarJets hS hT rsel hrsel 0 z Fin.elim0 := by
  simp only [endpointFlowCircle, dif_pos hz]
  exact circleRealize_decode (hS.2.1 (3 / 4 : ℝ)) _ _

theorem N01Properties.endpointFlowCircle_decode_apply
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (hN.endpointFlowCircle hS hT rsel hrsel z) m θ =
      C.minusFlow (liftSectorParameter S C z) m (rsel m) θ -
        C.minusFlow (C.referenceState, 0) m (rsel m) θ := by
  exact (congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
    (hN.endpointFlowCircle_decode hS hT rsel hrsel z hz)).trans
      (hN.endpointFlowScalarJets_zero hS hT rsel hrsel z hz m θ)

theorem N01Properties.endpointFlowCircle_zero
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    hN.endpointFlowCircle hS hT rsel hrsel 0 = 0 := by
  have hzero : (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε :=
    circleTower_pair_origin_mem (sectorGrading S base) hN.2.1
  apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  exact (hN.endpointFlowCircle_decode hS hT rsel hrsel 0 hzero).trans
    ((hN.endpointFlowScalarJets_zero_at_origin hS hT rsel hrsel).trans
      (S.circle (3 / 4 : ℝ)).decode.map_zero.symm)

private theorem convex_seminorm_strict_sublevel
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (R : ℝ) : Convex ℝ {x : E | p x < R} := by
  intro x hx y hy a b ha hb hab
  have hx' : x ∈ p.ball 0 R := by simpa only [Set.mem_ofPred_eq, Seminorm.mem_ball_zero] using hx
  have hy' : y ∈ p.ball 0 R := by simpa only [Set.mem_ofPred_eq, Seminorm.mem_ball_zero] using hy
  simpa only [Set.mem_ofPred_eq, Seminorm.mem_ball_zero] using p.convex_ball 0 R hx' hy' ha hb hab

/-- A complete per-order box certificate gives a neighbourhood at each
parameter order and point, before choosing the output-order seminorm. -/
private theorem circleTower_localBounds_of_boxBounds
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {T : MaterialData} {γ : ℝ} {U : Set E} {base : ℕ}
    (p : ℕ → Seminorm ℝ E) (hp : ∀ j, Continuous (p j))
    (hU : IsOpen U) (hcU : Convex ℝ U)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hbox : ∀ n : ℕ, ∃ B : ℕ, base ≤ B ∧ ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ U, p B y ≤ R →
        ∀ v : Fin (n + 1) → E,
          circleNorm T γ s (A (n + 1) y v) ≤
            K * (1 + p j y) * ∏ i, p j (v i)) :
    CircleLocalPositiveJetNormBounds (T := T) (γ := γ) (U := U) A := by
  intro n x hx
  obtain ⟨B, _hB, hbound⟩ := hbox n
  let V : Set E := U ∩ {y | p B y < p B x + 1}
  have hVo : IsOpen V := hU.inter (isOpen_lt (hp B) continuous_const)
  have hVc : Convex ℝ V := hcU.inter
    (convex_seminorm_strict_sublevel (p B) (p B x + 1))
  have hxV : x ∈ V := ⟨hx,
    Set.mem_ofPred.mpr (lt_add_of_pos_right (p B x) zero_lt_one)⟩
  refine ⟨V, hVo, hVc, hxV, inter_subset_left, ?_⟩
  intro s
  have hR : 0 ≤ p B x + 1 := add_nonneg (apply_nonneg _ _) zero_le_one
  obtain ⟨j, K, hK, hestimate⟩ := hbound (p B x + 1) hR s
  exact ⟨p j, K, hp j, hK, fun y hy v => hestimate y hy.1 hy.2.le v⟩

/-- Fix the actual parameter and circle types before supplying the model's
families and certificates to the generic assembly theorem. -/
private theorem circleTower_parameter_assembly
    (T : MaterialData) (S : PhysicalSpacesData)
    {U : Set (StateDirections S × ℝ)}
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hU : IsOpen U) (f : StateDirections S × ℝ → CircleSpace S)
    (A : ∀ n : ℕ, (StateDirections S × ℝ) →
      MultilinearMap ℝ (fun _ : Fin n => StateDirections S × ℝ) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T (3 / 4 : ℝ) (A n x v))
    (hbound : CircleLocalPositiveJetNormBounds (T := T) (γ := (3 / 4 : ℝ)) (U := U) A)
    (hzero : ∀ x ∈ U, A 0 x Fin.elim0 = (S.circle (3 / 4 : ℝ)).decode (f x))
    (hscalar : ∀ n (x w : StateDirections S × ℝ)
      (v : Fin n → StateDirections S × ℝ) (t : ℝ), x + t • w ∈ U → ∀ m b θ,
      HasDerivAt (fun u => iteratedDeriv b (A n (x + u • w) v m) θ)
        (iteratedDeriv b (A (n + 1) (x + t • w) (Fin.cons w v) m) θ) t)
    (henergy : CircleJetSecondEnvelopes (T := T) (γ := (3 / 4 : ℝ)) (U := U) A) :
    ∃ J : SmoothDirections U f, ∀ n x, x ∈ U →
      ∀ v : Fin n → StateDirections S × ℝ,
        (S.circle (3 / 4 : ℝ)).decode (J.D n x v) = A n x v := by
  exact exists_circle_smoothDirections_of_locally_positive_scalar_jets
    (E := StateDirections S × ℝ) (T := T) (γ := (3 / 4 : ℝ))
    (S := S.circle (3 / 4 : ℝ)) (U := U)
    hS hM hH hU f A hmember hbound hzero hscalar henergy

private theorem circleTower_endpoint_localBounds
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    CircleLocalPositiveJetNormBounds (T := T) (γ := (3 / 4 : ℝ))
      (U := sectorNeighborhood S base ε ε)
      (hN.endpointFlowScalarJets hS hT rsel hrsel) := by
  exact circleTower_localBounds_of_boxBounds
    (E := StateDirections S × ℝ) (T := T) (γ := (3 / 4 : ℝ))
    (U := sectorNeighborhood S base ε ε) (base := base)
    (pairGrading (sectorGrading S) realGrading) (sectorPairGrading_continuous S)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    (hN.endpointFlowScalarJets hS hT rsel hrsel)
    (hN.endpointFlowScalarJets_positive_norm_bounds_on_box hS hT rsel hrsel)

theorem N01Properties.exists_endpointFlowCircle_smoothDirections
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    ∃ J : SmoothDirections (sectorNeighborhood S base ε ε) (hN.endpointFlowCircle hS hT rsel hrsel),
      ∀ n x, x ∈ sectorNeighborhood S base ε ε → ∀ v : Fin n → (StateDirections S × ℝ),
        (S.circle (3 / 4 : ℝ)).decode (J.D n x v) = hN.endpointFlowScalarJets hS hT rsel hrsel n x v := by
  have hU : IsOpen (sectorNeighborhood S base ε ε) :=
    sectorNeighborhood_isOpen S base ε ε
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  exact circleTower_parameter_assembly
    (T := T) (S := S) (U := sectorNeighborhood S base ε ε)
    (hS.2.1 (3 / 4 : ℝ)) hM hH hU
    (hN.endpointFlowCircle hS hT rsel hrsel)
    (hN.endpointFlowScalarJets hS hT rsel hrsel)
    (fun n x hx v => hN.endpointFlowScalarJets_circleMember hS hT rsel hrsel n x hx v)
    (circleTower_endpoint_localBounds hN hS hT rsel hrsel)
    (fun x hx => (hN.endpointFlowCircle_decode hS hT rsel hrsel x hx).symm)
    (fun n x w v t ht m b θ =>
      hN.endpointFlowScalarJets_hasDerivAt_line hS hT rsel hrsel n x w v t ht m b θ)
    (hN.endpointFlowScalarJets_second_envelopes hS hT rsel hrsel hU (fun _ hx => hx))

end ContinuousFlexibility.Statements
