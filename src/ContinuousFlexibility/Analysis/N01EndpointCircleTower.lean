import ContinuousFlexibility.Analysis.N01EndpointOneHigh
import ContinuousFlexibility.Analysis.N01EndpointSecondEnvelope
import ContinuousFlexibility.Analysis.N01EndpointZeroCircleMember
import ContinuousFlexibility.Analysis.CirclePositiveJetAssembly
import ContinuousFlexibility.Analysis.SmoothDirectionsGluing

/-!
# The actual endpoint flow in the physical circle topology

All scalar jets are realized in the supplied circle model. Uniform
weighted Taylor estimates give genuine projective line derivatives on
each bounded low-order box. Their unique towers agree on overlaps and
therefore give one smooth tower on the full original sector domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointCircleTowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

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
  rw [hN.endpointFlowCircle_decode hS hT rsel hrsel z hz]
  exact hN.endpointFlowScalarJets_zero hS hT rsel hrsel z hz m θ

theorem N01Properties.endpointFlowCircle_zero
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    hN.endpointFlowCircle hS hT rsel hrsel 0 = 0 := by
  have hzero : (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε := by
    constructor
    · change sectorGrading S base (0 : StateDirections S) < ε
      rw [(sectorGrading S base).map_zero']
      exact hN.2.1
    · change |(0 : ℝ)| < ε
      rw [abs_zero]
      exact hN.2.1
  apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  exact (hN.endpointFlowCircle_decode hS hT rsel hrsel 0 hzero).trans
    ((hN.endpointFlowScalarJets_zero_at_origin hS hT rsel hrsel).trans
      (S.circle (3 / 4 : ℝ)).decode.map_zero.symm)

private theorem convex_seminorm_strict_sublevel
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (R : ℝ) : Convex ℝ {x : E | p x < R} := by
  intro x hx y hy a b ha hb hab
  have hx' : x ∈ p.ball 0 R := by simpa only [Seminorm.mem_ball_zero] using hx
  have hy' : y ∈ p.ball 0 R := by simpa only [Seminorm.mem_ball_zero] using hy
  simpa only [Seminorm.mem_ball_zero] using p.convex_ball 0 R hx' hy' ha hb hab

theorem N01Properties.exists_endpointFlowCircle_smoothDirections
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    ∃ J : SmoothDirections (sectorNeighborhood S base ε ε) (hN.endpointFlowCircle hS hT rsel hrsel),
      ∀ n x, x ∈ sectorNeighborhood S base ε ε → ∀ v : Fin n → (StateDirections S × ℝ),
        (S.circle (3 / 4 : ℝ)).decode (J.D n x v) = hN.endpointFlowScalarJets hS hT rsel hrsel n x v := by
  classical
  obtain ⟨B, _, hbound⟩ := hN.endpointFlowScalarJets_positive_norm_bounds_on_box hS hT rsel hrsel
  let U : Set (StateDirections S × ℝ) := sectorNeighborhood S base ε ε
  let p := pairGrading (sectorGrading S) realGrading
  let V : U → Set (StateDirections S × ℝ) := fun i =>
    U ∩ {x | p B x < p B i.val + 1}
  have hVo (i : U) : IsOpen (V i) :=
    (sectorNeighborhood_isOpen S base ε ε).inter
      (isOpen_lt (sectorPairGrading_continuous S B) continuous_const)
  have hVc (i : U) : Convex ℝ (V i) :=
    (sectorNeighborhood_convex S base ε ε).inter
      (convex_seminorm_strict_sublevel (p B) (p B i.val + 1))
  have hsub (i : U) : V i ⊆ U := inter_subset_left
  have hcover : ∀ x ∈ U, ∃ i : U, x ∈ V i := by
    intro x hx
    exact ⟨⟨x, hx⟩, hx, lt_add_of_pos_right _ zero_lt_one⟩
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  have hlocal (i : U) : ∃ J : SmoothDirections (V i) (hN.endpointFlowCircle hS hT rsel hrsel),
      ∀ n x, x ∈ V i → ∀ v : Fin n → (StateDirections S × ℝ),
        (S.circle (3 / 4 : ℝ)).decode (J.D n x v) = hN.endpointFlowScalarJets hS hT rsel hrsel n x v := by
    have hR : 0 ≤ p B i.val + 1 := add_nonneg (apply_nonneg _ _) zero_le_one
    have hpositive : CirclePositiveJetNormBounds (T := T) (γ := (3 / 4 : ℝ))
        (U := V i) (hN.endpointFlowScalarJets hS hT rsel hrsel) := by
      intro n s
      obtain ⟨j, K, hK, hk⟩ := hbound (p B i.val + 1) hR n s
      exact ⟨p j, K, sectorPairGrading_continuous S j, hK,
        fun x hx v => hk x hx.1 hx.2.le v⟩
    exact exists_circle_smoothDirections_of_positive_scalar_jets
      (hS.2.1 (3 / 4 : ℝ)) hM hH (hVo i) (hVc i) (hN.endpointFlowCircle hS hT rsel hrsel)
      (hN.endpointFlowScalarJets hS hT rsel hrsel)
      (fun n x hx v => hN.endpointFlowScalarJets_circleMember hS hT rsel hrsel n x hx.1 v)
      hpositive
      (fun x hx => (hN.endpointFlowCircle_decode hS hT rsel hrsel x hx.1).symm)
      (fun n x w v t ht m b θ => hN.endpointFlowScalarJets_hasDerivAt_line hS hT rsel hrsel n x w v t ht.1 m b θ)
      (hN.endpointFlowScalarJets_second_envelopes hS hT rsel hrsel (hVo i) (hsub i))
  choose J hJ using hlocal
  obtain ⟨K, hK⟩ := exists_smoothDirections_of_open_cover
    (sectorNeighborhood_isOpen S base ε ε) V J hsub hcover
  refine ⟨K, ?_⟩
  intro n x hx v
  obtain ⟨i, hi⟩ := hcover x hx
  rw [hK i n x hi]
  exact hJ i n x hi v

end ContinuousFlexibility.Statements
