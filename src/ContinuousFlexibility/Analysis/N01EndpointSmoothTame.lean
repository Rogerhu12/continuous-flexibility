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

private theorem endpoint_oneHigh_nonneg
    {E : Type*} [AddCommGroup E] [Module ℝ E]
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
  obtain ⟨J, hJ⟩ := hN.exists_endpointFlowCircle_smoothDirections hS hT rsel hrsel
  let p := pairGrading (sectorGrading S) realGrading
  have hjet (k : ℕ) : ∃ B L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ sectorNeighborhood S base ε ε, p B x ≤ R →
      ∀ v : Fin k → (StateDirections S × ℝ),
      circleNorm T (3 / 4 : ℝ) s ((S.circle (3 / 4 : ℝ)).decode (J.D k x v)) ≤
        K * oneHighVariationWeight p B (s + L) x v := by
    cases k with
    | zero =>
      obtain ⟨B, L, _, hbound⟩ := hN.endpointFlowCircle_circleNorm_local_growth hS hT rsel hrsel
      refine ⟨B, L, fun R hR s hs => ?_⟩
      obtain ⟨K, hK, hk⟩ := hbound R hR s hs
      refine ⟨K, hK, ?_⟩
      intro x hx hxlow v
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      rw [hv, J.zero x hx]
      simpa only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
        mul_one, add_zero] using hk x hx hxlow
    | succ n =>
      obtain ⟨B, L, _, hbound⟩ := hN.endpointFlowScalarJets_positive_circleNorm_oneHigh hS hT rsel hrsel
      refine ⟨B, L, fun R hR s hs => ?_⟩
      obtain ⟨K, hK, hk⟩ := hbound n R hR s hs
      exact ⟨K, hK, fun x hx hxlow v => by
        rw [hJ (n + 1) x hx v]
        exact hk x hx hxlow v⟩
  refine ⟨J, ?_⟩
  intro k x₀ hx₀
  obtain ⟨B, L, hbound⟩ := hjet k
  let R : ℝ := p B x₀ + 1
  have hR : 0 ≤ R := add_nonneg (apply_nonneg _ _) zero_le_one
  refine ⟨L, B, 1, zero_lt_one, fun s hs => ?_⟩
  obtain ⟨K, hK, hk⟩ := hbound R hR s hs
  refine ⟨K, hK, ?_⟩
  intro x hx hnear v
  have hxlow : p B x ≤ R := by
    have h := map_add_le_add (p B) (x - x₀) x₀
    rw [sub_add_cancel] at h
    dsimp only [R]
    linarith only [h, hnear]
  have hnorm := hk x hx hxlow v
  have hW : 0 ≤ oneHighVariationWeight p B (s + L) x v := endpoint_oneHigh_nonneg p B (s + L) x v
  change (S.circle (3 / 4 : ℝ)).grading s (J.D k x v) ≤
    K * oneHighVariationWeight p B (s + L) x v
  apply (circleGrading_le_iff_circleNorm (hS.2.1 (3 / 4 : ℝ)) s (J.D k x v)
    (mul_nonneg hK hW)).mpr
  intro i hi
  exact (circleNorm_monotone_of_member ((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 (J.D k x v)) hi).trans hnorm

end ContinuousFlexibility.Statements
