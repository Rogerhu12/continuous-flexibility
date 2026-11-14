module

public import ContinuousFlexibility.Analysis.N01EndpointZeroGrowth
public import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Fixed-base estimates for every genuine endpoint circle tower

The actual endpoint estimates choose their low order before all parameter
orders. We keep that order when passing to the circle grading and to any
given genuine tower. Constants precede both the closed-radius selector and
the tower; no derivative family is selected separately at different orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

local instance n04EndpointFixedBaseStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- The physical circle weight is unchanged, and one low order controls every
parameter order of the actual closed-radius flow displacement. -/
theorem N01Properties.endpointFlowCircle_fixedBase_oneHigh
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B : ℕ, base ≤ B ∧ ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (hN.endpointFlowCircle hS hT rsel hrsel),
      ∀ x ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B x ≤ R →
      ∀ v : Fin n → (StateDirections S × ℝ),
        (S.circle (3 / 4 : ℝ)).grading s (J.D n x v) ≤
          K * tameJetSize (pairGrading (sectorGrading S) realGrading) n s L B x v := by
  classical
  let p := pairGrading (sectorGrading S) realGrading
  let H := S.circle (3 / 4 : ℝ)
  have hp : Monotone p := sectorPairGrading_monotone S
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  let positive := hN.endpointFlowScalarJets_positive_circleNorm_oneHigh_uniform_radius hS hT
  let zero := hN.endpointFlowCircle_circleNorm_local_growth_uniform_radius hS hT
  let Bp : ℕ := positive.choose
  let Bz : ℕ := zero.choose
  let B : ℕ := max Bz Bp
  have hBp : Bp ≤ B := le_max_right _ _
  have hBz : Bz ≤ B := le_max_left _ _
  have hdecode (rsel : ℕ → ℝ)
      (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
      (J : SmoothDirections (sectorNeighborhood S base ε ε)
        (hN.endpointFlowCircle hS hT rsel hrsel)) (n : ℕ)
      (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε)
      (v : Fin n → (StateDirections S × ℝ)) :
      H.decode (J.D n x v) = hN.endpointFlowScalarJets hS hT rsel hrsel n x v := by
    let data := hN.exists_endpointFlowCircle_smoothDirections hS hT rsel hrsel
    have heq := J.unique data.choose n x hx
    exact (congrArg (fun A : ContinuousMultilinearMap ℝ
      (fun _ : Fin n => StateDirections S × ℝ) H.Space => H.decode (A v)) heq).trans
        (data.choose_spec n x hx v)
  have hraw (n : ℕ) : ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (hN.endpointFlowCircle hS hT rsel hrsel),
      ∀ x ∈ sectorNeighborhood S base ε ε, p B x ≤ R →
      ∀ v : Fin n → (StateDirections S × ℝ),
        circleNorm T (3 / 4 : ℝ) s (H.decode (J.D n x v)) ≤
          K * oneHighVariationWeight p B (s + L) x v := by
    cases n with
    | zero =>
        let L : ℕ := zero.choose_spec.choose
        refine ⟨L, fun R hR s hs => ?_⟩
        let data := zero.choose_spec.choose_spec.2 R hR s (hBz.trans hs)
        refine ⟨data.choose, data.choose_spec.1, fun rsel hrsel J x hx hlow v => ?_⟩
        have hv : v = Fin.elim0 := Subsingleton.elim _ _
        have hz : J.D 0 x v = hN.endpointFlowCircle hS hT rsel hrsel x :=
          (congrArg (fun w => J.D 0 x w) hv).trans (J.zero x hx)
        have hb := data.choose_spec.2 rsel hrsel x hx ((hp hBz x).trans hlow)
        have heq := congrArg (fun u : H.Space => circleNorm T (3 / 4 : ℝ) s (H.decode u)) hz
        simpa only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
          mul_one, add_zero] using heq.trans_le hb
    | succ n =>
        let lossData := positive.choose_spec.2 n
        let L : ℕ := lossData.choose
        refine ⟨L, fun R hR s hs => ?_⟩
        let data := lossData.choose_spec R hR s (hBp.trans hs)
        refine ⟨data.choose, data.choose_spec.1, fun rsel hrsel J x hx hlow v => ?_⟩
        have hb := data.choose_spec.2 rsel hrsel x hx ((hp hBp x).trans hlow) v
        exact (congrArg (circleNorm T (3 / 4 : ℝ) s)
          (hdecode rsel hrsel J (n + 1) x hx v)).trans_le
            (hb.trans (mul_le_mul_of_nonneg_left
              (oneHighVariationWeight_mono hp hBp le_rfl x v) data.choose_spec.1))
  refine ⟨B, positive.choose_spec.1.trans hBp, fun n => ?_⟩
  let data := hraw n
  let L : ℕ := data.choose
  refine ⟨B + L, fun R hR s => ?_⟩
  let estimate := data.choose_spec R hR (s + B) (Nat.le_add_left B s)
  let K : ℝ := estimate.choose
  have hK : 0 ≤ K := estimate.choose_spec.1
  refine ⟨K, hK, fun rsel hrsel J x hx hlow v => ?_⟩
  have hb : circleNorm T (3 / 4 : ℝ) (s + B) (H.decode (J.D n x v)) ≤
      K * tameJetSize p n s (B + L) B x v := by
    simpa only [K, L, oneHighVariationWeight, tameJetSize, Nat.add_assoc] using
      estimate.choose_spec.2 rsel hrsel J x hx hlow v
  apply (circleGrading_le_iff_circleNorm hH s (J.D n x v)
    (mul_nonneg hK (tameJetSize_nonneg p n s (B + L) B x v))).mpr
  intro j hj
  exact (circleNorm_monotone_of_member (hH.2.2.2.1 (J.D n x v))
    (hj.trans (Nat.le_add_right s B))).trans hb

end ContinuousFlexibility.Statements
