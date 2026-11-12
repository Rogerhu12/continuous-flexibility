import ContinuousFlexibility.Analysis.N01EndpointSmoothTame
import ContinuousFlexibility.Analysis.TameUniformFamilyJets

/-!
# Selector-uniform bounds for the actual closed-radius flow towers

The underlying estimates are the physical endpoint norm bounds with
their constants already chosen before the radius selector. Passing to
the supplied finite-maximum grading and to joint jet growth preserves
that uniformity. The result applies to any genuine tower of the actual
flow displacement, by uniqueness.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

local instance n01FlowCircleUniformBoundsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

private theorem flowCircle_oneHigh_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (B H : ℕ) (x : E) (v : Fin 0 → E) :
    oneHighVariationWeight p B H x v = 1 + p H x := by
  simp only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
    mul_one, add_zero]

private theorem flowCircle_oneHigh_shifted_eq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (n s B L : ℕ) (x : E) (v : Fin n → E) :
    oneHighVariationWeight p B ((s + B) + L) x v =
      tameJetSize p n s (B + L) B x v := by
  simp only [oneHighVariationWeight, tameJetSize, Nat.add_assoc]

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlowCircle_uniformFamilyJetBounds
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : I → ℕ → ℝ)
    (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m))
    (J : ∀ i, SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.endpointFlowCircle hS hT (rsel i) (hrsel i))) :
    UniformFamilyJetBounds (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading J := by
  let p := pairGrading (sectorGrading S) realGrading
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hdecode (i : I) (n : ℕ) (x : StateDirections S × ℝ)
      (hx : x ∈ sectorNeighborhood S base ε ε) (v : Fin n → StateDirections S × ℝ) :
      H.decode ((J i).D n x v) =
        hN.endpointFlowScalarJets hS hT (rsel i) (hrsel i) n x v := by
    let towerData := hN.exists_endpointFlowCircle_smoothDirections hS hT (rsel i) (hrsel i)
    let canonical : SmoothDirections (sectorNeighborhood S base ε ε)
        (hN.endpointFlowCircle hS hT (rsel i) (hrsel i)) := towerData.choose
    have heq : (J i).D n x = canonical.D n x := (J i).unique canonical n x hx
    exact (congrArg (fun A : ContinuousMultilinearMap ℝ
        (fun _ : Fin n => StateDirections S × ℝ) H.Space => H.decode (A v)) heq).trans
      (towerData.choose_spec n x hx v)
  have hraw (n : ℕ) : ∃ B L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i x, x ∈ sectorNeighborhood S base ε ε → p B x ≤ R →
      ∀ v : Fin n → StateDirections S × ℝ,
        circleNorm T (3 / 4 : ℝ) s (H.decode ((J i).D n x v)) ≤
          K * oneHighVariationWeight p B (s + L) x v := by
    cases n with
    | zero =>
        let data := hN.endpointFlowCircle_circleNorm_local_growth_uniform_radius hS hT
        let B : ℕ := data.choose
        let L : ℕ := data.choose_spec.choose
        refine ⟨B, L, fun R hR s hs => ?_⟩
        let orderData := data.choose_spec.choose_spec.2 R hR s hs
        let K : ℝ := orderData.choose
        have hK : 0 ≤ K := orderData.choose_spec.1
        refine ⟨K, hK, fun i x hx hlow v => ?_⟩
        have hv : v = Fin.elim0 := by
          funext j
          exact Fin.elim0 j
        have hzero : (J i).D 0 x v = hN.endpointFlowCircle hS hT (rsel i) (hrsel i) x :=
          (congrArg (fun w : Fin 0 → StateDirections S × ℝ => (J i).D 0 x w) hv).trans
            ((J i).zero x hx)
        have hnorm : circleNorm T (3 / 4 : ℝ) s (H.decode ((J i).D 0 x v)) =
            circleNorm T (3 / 4 : ℝ) s
              (H.decode (hN.endpointFlowCircle hS hT (rsel i) (hrsel i) x)) :=
          congrArg (fun u : H.Space => circleNorm T (3 / 4 : ℝ) s (H.decode u)) hzero
        exact hnorm.trans_le
          ((orderData.choose_spec.2 (rsel i) (hrsel i) x hx hlow).trans_eq
            (congrArg (fun a : ℝ => K * a) (flowCircle_oneHigh_zero p B (s + L) x v).symm))
    | succ n =>
        let data := hN.endpointFlowScalarJets_positive_circleNorm_oneHigh_uniform_radius hS hT
        let B : ℕ := data.choose
        let L : ℕ := data.choose_spec.choose
        refine ⟨B, L, fun R hR s hs => ?_⟩
        let orderData := data.choose_spec.choose_spec.2 n R hR s hs
        let K : ℝ := orderData.choose
        have hK : 0 ≤ K := orderData.choose_spec.1
        exact ⟨K, hK, fun i x hx hlow v =>
          (congrArg (circleNorm T (3 / 4 : ℝ) s) (hdecode i (n + 1) x hx v)).trans_le
            (orderData.choose_spec.2 (rsel i) (hrsel i) x hx hlow v)⟩
  intro n
  refine uniformFamilyLowGrowthOn_of_oneHigh (p := p) (q := H.grading)
    (U := sectorNeighborhood S base ε ε)
    (fun (i : I) (x : StateDirections S × ℝ) (v : Fin n → StateDirections S × ℝ) =>
      (J i).D n x v) ?_
  let data := hraw n
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  refine ⟨B, B + L, fun R hR s => ?_⟩
  let orderData := data.choose_spec.choose_spec R hR (s + B) (by omega)
  let K : ℝ := orderData.choose
  have hK : 0 ≤ K := orderData.choose_spec.1
  refine ⟨K, hK, fun i x hx hlow v => ?_⟩
  have hnorm : circleNorm T (3 / 4 : ℝ) (s + B) (H.decode ((J i).D n x v)) ≤
      K * tameJetSize p n s (B + L) B x v :=
    (orderData.choose_spec.2 i x hx hlow v).trans_eq
      (congrArg (fun a : ℝ => K * a) (flowCircle_oneHigh_shifted_eq p n s B L x v))
  apply (circleGrading_le_iff_circleNorm hH s ((J i).D n x v)
    (mul_nonneg hK (tameJetSize_nonneg p n s (B + L) B x v))).mpr
  intro j hj
  exact (circleNorm_monotone_of_member (hH.2.2.2.1 ((J i).D n x v))
    (hj.trans (Nat.le_add_right s B))).trans hnorm

end ContinuousFlexibility.Statements
