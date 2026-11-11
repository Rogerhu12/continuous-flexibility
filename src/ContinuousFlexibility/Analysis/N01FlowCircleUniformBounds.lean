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
    let h := hN.exists_endpointFlowCircle_smoothDirections hS hT (rsel i) (hrsel i)
    have heq : (J i).D n x = h.choose.D n x := (J i).unique h.choose n x hx
    rw [heq]
    exact h.choose_spec n x hx v
  have hraw (n : ℕ) : ∃ B L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i x, x ∈ sectorNeighborhood S base ε ε → p B x ≤ R →
      ∀ v : Fin n → StateDirections S × ℝ,
        circleNorm T (3 / 4 : ℝ) s (H.decode ((J i).D n x v)) ≤
          K * oneHighVariationWeight p B (s + L) x v := by
    cases n with
    | zero =>
        let h := hN.endpointFlowCircle_circleNorm_local_growth_uniform_radius hS hT
        let B := h.choose
        let L := h.choose_spec.choose
        have hb := h.choose_spec.choose_spec.2
        refine ⟨B, L, fun R hR s hs => ?_⟩
        obtain ⟨K, hK, hk⟩ := hb R hR s hs
        refine ⟨K, hK, fun i x hx hlow v => ?_⟩
        have hv : v = Fin.elim0 := Subsingleton.elim _ _
        rw [hv, (J i).zero x hx]
        simpa only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
          mul_one, add_zero] using hk (rsel i) (hrsel i) x hx hlow
    | succ n =>
        let h := hN.endpointFlowScalarJets_positive_circleNorm_oneHigh_uniform_radius hS hT
        let B := h.choose
        let L := h.choose_spec.choose
        have hb := h.choose_spec.choose_spec.2
        refine ⟨B, L, fun R hR s hs => ?_⟩
        obtain ⟨K, hK, hk⟩ := hb n R hR s hs
        refine ⟨K, hK, fun i x hx hlow v => ?_⟩
        rw [hdecode i (n + 1) x hx v]
        exact hk (rsel i) (hrsel i) x hx hlow v
  intro n
  apply uniformFamilyLowGrowthOn_of_oneHigh
  obtain ⟨B, L, hb⟩ := hraw n
  refine ⟨B, B + L, fun R hR s => ?_⟩
  obtain ⟨K, hK, hk⟩ := hb R hR (s + B) (by omega)
  refine ⟨K, hK, fun i x hx hlow v => ?_⟩
  have hnorm : circleNorm T (3 / 4 : ℝ) (s + B) (H.decode ((J i).D n x v)) ≤
      K * tameJetSize p n s (B + L) B x v := by
    simpa only [oneHighVariationWeight, tameJetSize, Nat.add_assoc] using hk i x hx hlow v
  apply (circleGrading_le_iff_circleNorm hH s ((J i).D n x v)
    (mul_nonneg hK (tameJetSize_nonneg p n s (B + L) B x v))).mpr
  intro j hj
  exact (circleNorm_monotone_of_member (hH.2.2.2.1 ((J i).D n x v))
    (hj.trans (Nat.le_add_right s B))).trans hnorm

end ContinuousFlexibility.Statements
