import ContinuousFlexibility.Analysis.N01EndpointCircleJets
import ContinuousFlexibility.Analysis.N01FlowScalarHeightBounds
import ContinuousFlexibility.Analysis.N01FlowSamplePrefactor

/-!
# Local physical height bounds for the chosen endpoint scalar jets

Uniqueness transfers the actual Euler-height estimate to the same scalar
multilinear fields used in circle reconstruction. Cancelling the N01
height factor against the output circle weight costs exactly one material
order, independently of the angular and parameter orders.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointScalarHeightBoundsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointScalarHeightBoundsRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlow_pure_scalar_height_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m b θ, b ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ η : HeightPair S,
      (∃ c : ℝ, ∀ r ∈ Ioo (C.left m) (C.right m), ∀ ψ,
        heightPairField S η (r, ψ) = stateU S (liftSectorParameter S C z).1 (r, ψ) + c) →
      |iteratedDeriv b
        (hN.endpointFlowScalarJets hS hT (n + 1) z
          (fun _ => scalarParameterDirection S) m) θ| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + loss) z) *
            heightPairGrading S base η + heightPairGrading S (s + loss) η) := by
  obtain ⟨B, hB, htower⟩ :=
    hN.sectorFlow_pure_scalar_height_bound_mod_constant hS hT n s
  refine ⟨B, hB, fun m b θ hb z hz η hη => ?_⟩
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩
  obtain ⟨J, hJ⟩ := htower m b θ (C.right m) hb hr
  rw [hN.endpointFlowScalarJets_iteratedDeriv hS hT (n + 1) z hz]
  have heq := (hN.sectorFlow_closed_angularTower hS hT m (C.right m) hr b θ).unique
    J (n + 1) z hz
  rw [heq]
  exact hJ z hz η hη

theorem N01Properties.endpointFlow_pure_scalar_weighted_height_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m b c θ, b ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ η : HeightPair S,
      (∃ a : ℝ, ∀ r ∈ Ioo (C.left m) (C.right m), ∀ ψ,
        heightPairField S η (r, ψ) = stateU S (liftSectorParameter S C z).1 (r, ψ) + a) →
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b
          (hN.endpointFlowScalarJets hS hT (n + 1) z
            (fun _ => scalarParameterDirection S) m) θ| ≤
        K * T.M (T.sample m) ^ (c + 1) *
          (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + loss) z) *
            heightPairGrading S base η + heightPairGrading S (s + loss) η) := by
  obtain ⟨B, hB, hbound⟩ := hN.endpointFlow_pure_scalar_height_bound hS hT n s
  obtain ⟨K, hK, hpref⟩ := hN.flow_sample_prefactor_le_M hT hB.le
  refine ⟨B * K, mul_pos hB hK, fun m b c θ hb z hz η hη => ?_⟩
  have hs := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ hs).2.2.2
  have hH : 0 ≤ T.H (T.sample m) := (hT.2.1 _ hs).2.1.le
  let W : ℝ := ((n : ℝ) + 2 +
    pairGrading (sectorGrading S) realGrading (s + loss) z) *
      heightPairGrading S base η + heightPairGrading S (s + loss) η
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact add_nonneg (mul_nonneg
      (add_nonneg (by positivity) (apply_nonneg _ _)) (apply_nonneg _ _))
      (apply_nonneg _ _)
  calc
    _ ≤ (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B * W) :=
      mul_le_mul_of_nonneg_left (hbound m b θ hb z hz η hη)
        (mul_nonneg (pow_nonneg hM c) (Real.rpow_nonneg hH _))
    _ = (B * T.M (T.sample m) ^ c) *
        (T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
          T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B) * W := by ring
    _ ≤ (B * T.M (T.sample m) ^ c) * (K * T.M (T.sample m)) * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hpref m) (mul_nonneg hB.le (pow_nonneg hM c))) hW
    _ = _ := by rw [pow_succ]; dsimp only [W]; ring

end ContinuousFlexibility.Statements
