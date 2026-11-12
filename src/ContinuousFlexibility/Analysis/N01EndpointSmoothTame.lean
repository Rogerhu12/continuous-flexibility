import ContinuousFlexibility.Analysis.N01EndpointZeroGrowth

/-!
# Closed-radius flow displacements are smooth tame in the circle model

For every fixed selector of radii in the closed flow intervals, the
tower consists of genuine projective derivatives on the original
sector neighborhood. Each local tame estimate uses a fixed low order
and a fixed loss before the output order is chosen. The reference
subtraction is the actual reference flow at the same selected radii.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointSmoothTameStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

private theorem endpoint_oneHigh_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (B H : ℕ) (x : E) (v : Fin 0 → E) :
    oneHighVariationWeight p B H x v = 1 + p H x := by
  simp only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
    mul_one, add_zero]

private theorem seminorm_le_center_add_one
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x x₀ : E) (hnear : p (x - x₀) < 1) :
    p x ≤ p x₀ + 1 := by
  have h := map_add_le_add p (x - x₀) x₀
  rw [sub_add_cancel] at h
  linarith only [h, hnear]

private theorem endpoint_oneHigh_nonneg
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (B H : ℕ) {k : ℕ} (x : E) (v : Fin k → E) :
    0 ≤ oneHighVariationWeight p B H x v := by
  exact multilinearTameSize_nonneg (p B) (p H) k
    (add_nonneg zero_le_one (apply_nonneg _ _)) v

theorem N01Properties.smoothTameOn_endpointFlowCircle
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.endpointFlowCircle hS hT rsel hrsel) := by
  let towerData := hN.exists_endpointFlowCircle_smoothDirections hS hT rsel hrsel
  let J : SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.endpointFlowCircle hS hT rsel hrsel) := towerData.choose
  let p := pairGrading (sectorGrading S) realGrading
  have hjet (k : ℕ) : ∃ B L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ sectorNeighborhood S base ε ε, p B x ≤ R →
      ∀ v : Fin k → (StateDirections S × ℝ),
      circleNorm T (3 / 4 : ℝ) s ((S.circle (3 / 4 : ℝ)).decode (J.D k x v)) ≤
        K * oneHighVariationWeight p B (s + L) x v := by
    cases k with
    | zero =>
      let data := hN.endpointFlowCircle_circleNorm_local_growth hS hT rsel hrsel
      let B : ℕ := data.choose
      let L : ℕ := data.choose_spec.choose
      refine ⟨B, L, fun R hR s hs => ?_⟩
      let orderData := data.choose_spec.choose_spec.2 R hR s hs
      let K : ℝ := orderData.choose
      have hK : 0 ≤ K := orderData.choose_spec.1
      refine ⟨K, hK, ?_⟩
      intro x hx hxlow v
      have hv : v = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      have hzero : J.D 0 x v = hN.endpointFlowCircle hS hT rsel hrsel x :=
        (congrArg (fun w : Fin 0 → (StateDirections S × ℝ) => J.D 0 x w) hv).trans
          (J.zero x hx)
      have hnorm : circleNorm T (3 / 4 : ℝ) s
          ((S.circle (3 / 4 : ℝ)).decode (J.D 0 x v)) =
          circleNorm T (3 / 4 : ℝ) s
            ((S.circle (3 / 4 : ℝ)).decode (hN.endpointFlowCircle hS hT rsel hrsel x)) :=
        congrArg (fun u : (S.circle (3 / 4 : ℝ)).Space =>
          circleNorm T (3 / 4 : ℝ) s ((S.circle (3 / 4 : ℝ)).decode u)) hzero
      exact hnorm.trans_le ((orderData.choose_spec.2 x hx hxlow).trans_eq
        (congrArg (fun a : ℝ => K * a) (endpoint_oneHigh_zero p B (s + L) x v).symm))
    | succ n =>
      let data := hN.endpointFlowScalarJets_positive_circleNorm_oneHigh hS hT rsel hrsel
      let B : ℕ := data.choose
      let lossData := data.choose_spec.2 n
      let L : ℕ := lossData.choose
      refine ⟨B, L, fun R hR s hs => ?_⟩
      let orderData := lossData.choose_spec R hR s hs
      let K : ℝ := orderData.choose
      have hK : 0 ≤ K := orderData.choose_spec.1
      exact ⟨K, hK, fun x hx hxlow v =>
        (congrArg (circleNorm T (3 / 4 : ℝ) s)
          (towerData.choose_spec (n + 1) x hx v)).trans_le
            (orderData.choose_spec.2 x hx hxlow v)⟩
  refine ⟨J, ?_⟩
  intro k x₀ hx₀
  let jetData := hjet k
  let B : ℕ := jetData.choose
  let L : ℕ := jetData.choose_spec.choose
  let R : ℝ := p B x₀ + 1
  have hR : 0 ≤ R := add_nonneg (apply_nonneg _ _) zero_le_one
  refine ⟨L, B, 1, zero_lt_one, fun s hs => ?_⟩
  let orderData := jetData.choose_spec.choose_spec R hR s hs
  let K : ℝ := orderData.choose
  have hK : 0 ≤ K := orderData.choose_spec.1
  refine ⟨K, hK, ?_⟩
  intro x hx hnear v
  have hxlow : p B x ≤ R := seminorm_le_center_add_one (p B) x x₀ hnear
  have hnorm := orderData.choose_spec.2 x hx hxlow v
  have hW : 0 ≤ oneHighVariationWeight p B (s + L) x v := endpoint_oneHigh_nonneg p B (s + L) x v
  change (S.circle (3 / 4 : ℝ)).grading s (J.D k x v) ≤
    K * oneHighVariationWeight p B (s + L) x v
  apply (circleGrading_le_iff_circleNorm (hS.2.1 (3 / 4 : ℝ)) s (J.D k x v)
    (mul_nonneg hK hW)).mpr
  intro i hi
  exact (circleNorm_monotone_of_member ((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 (J.D k x v)) hi).trans hnorm

end ContinuousFlexibility.Statements
