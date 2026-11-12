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

theorem N01Properties.exists_endpointFlowCircle_smoothDirections
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    ∃ J : SmoothDirections (sectorNeighborhood S base ε ε) (hN.endpointFlowCircle hS hT rsel hrsel),
      ∀ n x, x ∈ sectorNeighborhood S base ε ε → ∀ v : Fin n → (StateDirections S × ℝ),
        (S.circle (3 / 4 : ℝ)).decode (J.D n x v) = hN.endpointFlowScalarJets hS hT rsel hrsel n x v := by
  classical
  let U : Set (StateDirections S × ℝ) := sectorNeighborhood S base ε ε
  let p : ℕ → Seminorm ℝ (StateDirections S × ℝ) :=
    pairGrading (sectorGrading S) realGrading
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  have hlocal : ∀ n x, x ∈ U →
      ∃ V : Set (StateDirections S × ℝ), IsOpen V ∧ Convex ℝ V ∧
        x ∈ V ∧ V ⊆ U ∧
        ∀ s, ∃ q : Seminorm ℝ (StateDirections S × ℝ), ∃ K : ℝ,
          Continuous q ∧ 0 ≤ K ∧ ∀ y ∈ V, ∀ v : Fin (n + 1) → StateDirections S × ℝ,
          circleNorm T (3 / 4 : ℝ) s
            (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) y v) ≤
            K * (1 + q y) * ∏ i, q (v i) := by
    intro n x hx
    obtain ⟨B, _hB, hbound⟩ :=
      hN.endpointFlowScalarJets_positive_norm_bounds_on_box hS hT rsel hrsel n
    let V : Set (StateDirections S × ℝ) := U ∩ {y | p B y < p B x + 1}
    have hVo : IsOpen V := hU.inter
      (isOpen_lt (sectorPairGrading_continuous S B) continuous_const)
    have hVc : Convex ℝ V := (sectorNeighborhood_convex S base ε ε).inter
      (convex_seminorm_strict_sublevel (p B) (p B x + 1))
    have hxV : x ∈ V := ⟨hx,
      Set.mem_ofPred.mpr (lt_add_of_pos_right (p B x) zero_lt_one)⟩
    refine ⟨V, hVo, hVc, hxV, inter_subset_left, ?_⟩
    intro s
    have hR : 0 ≤ p B x + 1 := add_nonneg (apply_nonneg _ _) zero_le_one
    obtain ⟨j, K, hK, hestimate⟩ := hbound (p B x + 1) hR s
    exact ⟨p j, K, sectorPairGrading_continuous S j, hK,
      fun y hy v => hestimate y hy.1 hy.2.le v⟩
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  exact exists_circle_smoothDirections_of_locally_positive_scalar_jets
    (hS.2.1 (3 / 4 : ℝ)) hM hH hU
    (hN.endpointFlowCircle hS hT rsel hrsel)
    (hN.endpointFlowScalarJets hS hT rsel hrsel)
    (fun n x hx v => hN.endpointFlowScalarJets_circleMember hS hT rsel hrsel n x hx v)
    hlocal
    (fun x hx => (hN.endpointFlowCircle_decode hS hT rsel hrsel x hx).symm)
    (fun n x w v t ht m b θ =>
      hN.endpointFlowScalarJets_hasDerivAt_line hS hT rsel hrsel n x w v t ht m b θ)
    (hN.endpointFlowScalarJets_second_envelopes hS hT rsel hrsel hU (fun _ hx => hx))

end ContinuousFlexibility.Statements
