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

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlow_pure_scalar_height_bound_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)), ∀ m b θ, b ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ η : HeightPair S,
      (∃ c : ℝ, ∀ r ∈ Ioo (C.left m) (C.right m), ∀ ψ,
        heightPairField S η (r, ψ) = stateU S (liftSectorParameter S C z).1 (r, ψ) + c) →
      |iteratedDeriv b
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
          (fun _ => scalarParameterDirection S) m) θ| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + hN.ordinaryFlowLoss (n + 2)) z) *
            heightPairGrading S base η + heightPairGrading S (s + hN.ordinaryFlowLoss (n + 2)) η) := by
  let data := hN.sectorFlow_pure_scalar_height_bound_mod_constant hS hT n s
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  refine ⟨B, hB, fun rsel hrsel m b θ hb z hz η hη => ?_⟩
  have hr : rsel m ∈ Icc (C.left m) (C.right m) := hrsel m
  let pointData := data.choose_spec.2 m b θ (rsel m) hb hr
  let J := pointData.choose
  have heq := (hN.sectorFlow_closed_angularTower hS hT m (rsel m) hr b θ).unique
    J (n + 1) z hz
  have heval := congrArg (fun A : (StateDirections S × ℝ) [×(n + 1)]→L[ℝ] ℝ =>
    A (fun _ => scalarParameterDirection S)) heq
  have hangle := hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel (n + 1)
    z hz (fun _ => scalarParameterDirection S) m b θ
  have habs := congrArg (fun t : ℝ => |t|) (hangle.trans heval)
  exact habs.trans_le (pointData.choose_spec z hz η hη)

theorem N01Properties.endpointFlow_pure_scalar_height_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m b θ, b ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ η : HeightPair S,
      (∃ c : ℝ, ∀ r ∈ Ioo (C.left m) (C.right m), ∀ ψ,
        heightPairField S η (r, ψ) = stateU S (liftSectorParameter S C z).1 (r, ψ) + c) →
      |iteratedDeriv b
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
          (fun _ => scalarParameterDirection S) m) θ| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + hN.ordinaryFlowLoss (n + 2)) z) *
            heightPairGrading S base η + heightPairGrading S (s + hN.ordinaryFlowLoss (n + 2)) η) := by
  let data := hN.endpointFlow_pure_scalar_height_bound_uniform_radius hS hT n s
  exact Exists.intro data.choose
    (And.intro data.choose_spec.1 (data.choose_spec.2 rsel hrsel))

private theorem weighted_scalar_height_prefactor_bound
    {B K M w h e value W : ℝ} (c : ℕ)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hw : 0 ≤ w) (hW : 0 ≤ W)
    (hvalue : value ≤ B * h * e * W) (hpref : w * h * e ≤ K * M) :
    (M ^ c * w) * value ≤ (B * K) * M ^ (c + 1) * W := by
  calc
    _ ≤ (M ^ c * w) * (B * h * e * W) :=
      mul_le_mul_of_nonneg_left hvalue (mul_nonneg (pow_nonneg hM c) hw)
    _ = (B * M ^ c) * (w * h * e) * W := by ring
    _ ≤ (B * M ^ c) * (K * M) * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpref (mul_nonneg hB (pow_nonneg hM c))) hW
    _ = (B * K) * M ^ (c + 1) * W := by rw [pow_succ]; ring

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlow_pure_scalar_weighted_height_bound_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)), ∀ m b c θ, b ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ η : HeightPair S,
      (∃ a : ℝ, ∀ r ∈ Ioo (C.left m) (C.right m), ∀ ψ,
        heightPairField S η (r, ψ) = stateU S (liftSectorParameter S C z).1 (r, ψ) + a) →
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b
          (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
            (fun _ => scalarParameterDirection S) m) θ| ≤
        K * T.M (T.sample m) ^ (c + 1) *
          (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + hN.ordinaryFlowLoss (n + 2)) z) *
            heightPairGrading S base η + heightPairGrading S (s + hN.ordinaryFlowLoss (n + 2)) η) := by
  let data := hN.endpointFlow_pure_scalar_height_bound_uniform_radius hS hT n s
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  let pref := hN.flow_sample_prefactor_le_M hT hB.le
  let K : ℝ := pref.choose
  have hK : 0 < K := pref.choose_spec.1
  have hpref : ∀ m : ℕ,
      T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
        T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B ≤ K * T.M (T.sample m) := pref.choose_spec.2
  refine ⟨B * K, mul_pos hB hK, fun rsel hrsel m b c θ hb z hz η hη => ?_⟩
  have hD : IsAccumulatingProfile D := hN.1.1
  have hgeom : AccumulatingProfileBounds D hD.choose := hD.choose_spec
  have hs : T.sample m ∈ radialCore D := materialSample_mem_radialCore hT hgeom.2.1 m
  have hM : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ hs).2.2.2
  have hH : 0 ≤ T.H (T.sample m) := (hT.2.1 _ hs).2.1.le
  have hW : 0 ≤
      (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + hN.ordinaryFlowLoss (n + 2)) z) *
        heightPairGrading S base η + heightPairGrading S (s + hN.ordinaryFlowLoss (n + 2)) η) :=
    add_nonneg (mul_nonneg
      (add_nonneg (by positivity) (apply_nonneg _ _)) (apply_nonneg _ _))
      (apply_nonneg _ _)
  exact weighted_scalar_height_prefactor_bound c hB.le hM (Real.rpow_nonneg hH _) hW
    (data.choose_spec.2 rsel hrsel m b θ hb z hz η hη) (hpref m)

theorem N01Properties.endpointFlow_pure_scalar_weighted_height_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m b c θ, b ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ η : HeightPair S,
      (∃ a : ℝ, ∀ r ∈ Ioo (C.left m) (C.right m), ∀ ψ,
        heightPairField S η (r, ψ) = stateU S (liftSectorParameter S C z).1 (r, ψ) + a) →
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b
          (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
            (fun _ => scalarParameterDirection S) m) θ| ≤
        K * T.M (T.sample m) ^ (c + 1) *
          (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + hN.ordinaryFlowLoss (n + 2)) z) *
            heightPairGrading S base η + heightPairGrading S (s + hN.ordinaryFlowLoss (n + 2)) η) := by
  let data := hN.endpointFlow_pure_scalar_weighted_height_bound_uniform_radius hS hT n s
  exact Exists.intro data.choose
    (And.intro data.choose_spec.1 (data.choose_spec.2 rsel hrsel))

end ContinuousFlexibility.Statements
