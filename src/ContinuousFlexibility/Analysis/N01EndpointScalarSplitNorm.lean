import ContinuousFlexibility.Analysis.N01EndpointScalarCircleMember
import ContinuousFlexibility.Analysis.N01EndpointSplitNorm

/-!
# Pure scalar endpoint jets with separate physical orders

The Euler identity supplies a genuine localized copy of the actual
height. Its low and high energies keep the material order separate from
the angular order until after their infinite component sums.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointScalarSplitNormStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

private theorem scalar_height_scaled_energy_bound
    {M K A lo hi y : ℝ} {E F : ℝ≥0∞} (c : ℕ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hlo : lo ≤ Real.sqrt E.toReal) (hhi : hi ≤ Real.sqrt F.toReal)
    (hpoint : y ≤ K * M ^ (c + 1) * (A * lo + hi)) :
    y ≤ K * (A * Real.sqrt (ENNReal.ofReal ((M ^ (c + 1)) ^ 2) * E).toReal +
      Real.sqrt (ENNReal.ofReal ((M ^ (c + 1)) ^ 2) * F).toReal) := by
  have hsqrt (Q : ℝ≥0∞) :
      Real.sqrt (ENNReal.ofReal ((M ^ (c + 1)) ^ 2) * Q).toReal =
        M ^ (c + 1) * Real.sqrt Q.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hM _)]
  calc
    y ≤ K * M ^ (c + 1) * (A * lo + hi) := hpoint
    _ ≤ K * M ^ (c + 1) * (A * Real.sqrt E.toReal + Real.sqrt F.toReal) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hlo hA) hhi)
        (mul_nonneg hK (pow_nonneg hM _))
    _ = K * (A * Real.sqrt (ENNReal.ofReal ((M ^ (c + 1)) ^ 2) * E).toReal +
        Real.sqrt (ENNReal.ofReal ((M ^ (c + 1)) ^ 2) * F).toReal) := by
      rw [hsqrt, hsqrt]
      ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlow_pure_scalar_weightedJetNorm_height_bound_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)), ∀ z ∈ sectorNeighborhood S base ε ε,
      circleWeightedJetNorm T (3 / 4 : ℝ) b c
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
          (fun _ => scalarParameterDirection S)) ≤
        K * (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (b + loss) z) *
          (S.height (3 / 4 : ℝ)).grading (base + c + 6)
            (liftSectorParameter S C z).1.1.1 +
          (S.height (3 / 4 : ℝ)).grading (b + loss + c + 6)
            (liftSectorParameter S C z).1.1.1) := by
  let pointData := hN.endpointFlow_pure_scalar_weighted_height_bound_uniform_radius hS hT n b
  let K : ℝ := pointData.choose
  have hK : 0 < K := pointData.choose_spec.1
  let lowData := hN.physicalPlateauEnergy_weighted_tsum_le_grading_sq
    hS hT (hS.1 (3 / 4 : ℝ)) base (c + 1)
  let K₀ : ℝ := lowData.choose
  have hK₀ : 0 ≤ K₀ := lowData.choose_spec.1
  let highData := hN.physicalPlateauEnergy_weighted_tsum_le_grading_sq
    hS hT (hS.1 (3 / 4 : ℝ)) (b + loss) (c + 1)
  let K₁ : ℝ := highData.choose
  have hK₁ : 0 ≤ K₁ := highData.choose_spec.1
  let L : ℝ := Real.sqrt K₀ + Real.sqrt K₁
  have hL : 0 ≤ L := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨Real.sqrt (2 * Real.pi) * K * L,
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK.le) hL, ?_⟩
  intro rsel hrsel z hz
  let ξ : HeightPair S := (liftSectorParameter S C z).1.1
  let directions := hN.exists_height_pair_plateau_directions hS hT ξ
  let η : ℕ → HeightPair S := directions.choose
  let A : ℝ := (n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (b + loss) z
  have hA : 0 ≤ A := add_nonneg (by positivity) (apply_nonneg _ _)
  let E : ℕ → ℕ → ℝ≥0∞ := fun j m =>
    ENNReal.ofReal ((T.M (T.sample m) ^ (c + 1)) ^ 2) *
      physicalPlateauEnergy D T C (3 / 4 : ℝ) j
        ((S.height (3 / 4 : ℝ)).decode ξ.1) m
  have hE : (∑' m, E base m) ≤ ENNReal.ofReal
      (K₀ * ((S.height (3 / 4 : ℝ)).grading (base + c + 6) ξ.1) ^ 2) := by
    have hi : base + (c + 1) + 5 = base + c + 6 := by omega
    exact (lowData.choose_spec.2 ξ.1).trans_eq
      (congrArg (fun i : ℕ => ENNReal.ofReal
        (K₀ * ((S.height (3 / 4 : ℝ)).grading i ξ.1) ^ 2)) hi)
  have hF : (∑' m, E (b + loss) m) ≤ ENNReal.ofReal
      (K₁ * ((S.height (3 / 4 : ℝ)).grading (b + loss + c + 6) ξ.1) ^ 2) := by
    have hi : b + loss + (c + 1) + 5 = b + loss + c + 6 := by omega
    exact (highData.choose_spec.2 ξ.1).trans_eq
      (congrArg (fun i : ℕ => ENNReal.ofReal
        (K₁ * ((S.height (3 / 4 : ℝ)).grading i ξ.1) ^ 2)) hi)
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  have hb (m : ℕ) (θ : ℝ) :
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
          (fun _ => scalarParameterDirection S) m) θ| ≤
        K * (A * Real.sqrt (E base m).toReal +
          Real.sqrt (E (b + loss) m).toReal) :=
    scalar_height_scaled_energy_bound c (hM m) hK.le hA
      ((directions.choose_spec.2.2.2 base).2 m)
      ((directions.choose_spec.2.2.2 (b + loss)).2 m)
      (pointData.choose_spec.2 rsel hrsel m b c θ le_rfl z hz (η m)
        (directions.choose_spec.2.2.1 m))
  exact weightedJetNorm_le_scaled_two_envelopes
    hK.le hK₀ hK₁ hA (apply_nonneg _ _) (apply_nonneg _ _) hE hF
    (fun m => (hN.endpointFlowScalarJets_regular hS hT rsel hrsel (n + 1) z hz
      (fun _ => scalarParameterDirection S) m).1) hM hH b c hb

theorem N01Properties.endpointFlow_pure_scalar_weightedJetNorm_height_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ sectorNeighborhood S base ε ε,
      circleWeightedJetNorm T (3 / 4 : ℝ) b c
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
          (fun _ => scalarParameterDirection S)) ≤
        K * (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (b + loss) z) *
          (S.height (3 / 4 : ℝ)).grading (base + c + 6)
            (liftSectorParameter S C z).1.1.1 +
          (S.height (3 / 4 : ℝ)).grading (b + loss + c + 6)
            (liftSectorParameter S C z).1.1.1) := by
  let data := hN.endpointFlow_pure_scalar_weightedJetNorm_height_bound_uniform_radius hS hT n b c
  exact ⟨data.choose, data.choose_spec.1, data.choose_spec.2 rsel hrsel⟩

theorem liftSectorParameter_physical_height_grading_le
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : StateDirections S × ℝ) (s : ℕ) :
    (S.height (3 / 4 : ℝ)).grading s (liftSectorParameter S C z).1.1.1 ≤
      (S.height (3 / 4 : ℝ)).grading s C.referenceState.1.1 +
        pairGrading (sectorGrading S) realGrading s z := by
  have heq : (liftSectorParameter S C z).1.1.1 =
      C.referenceState.1.1 + z.1.val.1.1 := rfl
  exact (congrArg ((S.height (3 / 4 : ℝ)).grading s) heq).trans_le
    ((map_add_le_add ((S.height (3 / 4 : ℝ)).grading s) _ _).trans
      (add_le_add (le_refl _) (sectorParameter_height_grading_le S s z)))

private theorem real_reference_budget_bounds
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 ≤ 1 + a + b ∧ a ≤ 1 + a + b ∧ b ≤ 1 + a + b := by
  refine ⟨?_, ?_, ?_⟩
  · linarith only [ha, hb]
  · linarith only [hb]
  · linarith only [ha]

private theorem scalar_height_budget_transfer
    {K N J a b u v x y z r : ℝ}
    (hK : 0 ≤ K) (hN : 1 ≤ N) (hJ : 1 ≤ J) (ha : a ≤ J) (hb : b ≤ J)
    (hu : 0 ≤ u) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hu_bound : u ≤ a + y) (hv_bound : v ≤ b + z)
    (hpoint : r ≤ K * ((N + x) * u + v)) :
    r ≤ K * (N * J) * ((1 + x) * (1 + y) + (1 + z)) := by
  have hu' : u ≤ J * (1 + y) := hu_bound.trans (by
    calc
      a + y ≤ J + J * y := add_le_add ha (le_mul_of_one_le_left hy hJ)
      _ = J * (1 + y) := by ring)
  have hv' : v ≤ J * (1 + z) := hv_bound.trans (by
    calc
      b + z ≤ J + J * z := add_le_add hb (le_mul_of_one_le_left hz hJ)
      _ = J * (1 + z) := by ring)
  have hcoefficient : N + x ≤ N * (1 + x) := by
    calc
      N + x ≤ N + N * x := add_le_add (le_refl _) (le_mul_of_one_le_left hx hN)
      _ = N * (1 + x) := by ring
  have hlast : J * (1 + z) ≤ N * (J * (1 + z)) :=
    le_mul_of_one_le_left
      (mul_nonneg (zero_le_one.trans hJ) (add_nonneg zero_le_one hz)) hN
  calc
    r ≤ K * ((N + x) * u + v) := hpoint
    _ ≤ K * (N * (1 + x) * (J * (1 + y)) + N * (J * (1 + z))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul hcoefficient hu' hu
          (mul_nonneg (zero_le_one.trans hN) (add_nonneg zero_le_one hx)))
          (hv'.trans hlast)) hK
    _ = K * (N * J) * ((1 + x) * (1 + y) + (1 + z)) := by ring

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlow_pure_scalar_weightedJetNorm_budget_bound_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)), ∀ z ∈ sectorNeighborhood S base ε ε,
      circleWeightedJetNorm T (3 / 4 : ℝ) b c
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
          (fun _ => scalarParameterDirection S)) ≤
        K * ((1 + pairGrading (sectorGrading S) realGrading (b + loss) z) *
          (1 + pairGrading (sectorGrading S) realGrading (base + c + 6) z) +
          (1 + pairGrading (sectorGrading S) realGrading (b + loss + c + 6) z)) := by
  let normData := hN.endpointFlow_pure_scalar_weightedJetNorm_height_bound_uniform_radius hS hT n b c
  let K : ℝ := normData.choose
  have hK : 0 ≤ K := normData.choose_spec.1
  let J : ℝ := 1 + (S.height (3 / 4 : ℝ)).grading (base + c + 6) C.referenceState.1.1 +
    (S.height (3 / 4 : ℝ)).grading (b + loss + c + 6) C.referenceState.1.1
  let N : ℝ := (n : ℝ) + 2
  have hrefs := real_reference_budget_bounds
    (apply_nonneg ((S.height (3 / 4 : ℝ)).grading (base + c + 6)) C.referenceState.1.1)
    (apply_nonneg ((S.height (3 / 4 : ℝ)).grading (b + loss + c + 6)) C.referenceState.1.1)
  have hJ : 1 ≤ J := hrefs.1
  have hN₀ : 1 ≤ N := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp only [N]
    linarith only [hn]
  refine ⟨K * (N * J), mul_nonneg hK (mul_nonneg (zero_le_one.trans hN₀)
    (zero_le_one.trans hJ)), ?_⟩
  intro rsel hrsel z hz
  let p := pairGrading (sectorGrading S) realGrading
  exact scalar_height_budget_transfer hK hN₀ hJ hrefs.2.1 hrefs.2.2
    (apply_nonneg ((S.height (3 / 4 : ℝ)).grading (base + c + 6))
      (liftSectorParameter S C z).1.1.1)
    (apply_nonneg (p (b + loss)) z)
    (apply_nonneg (p (base + c + 6)) z)
    (apply_nonneg (p (b + loss + c + 6)) z)
    (liftSectorParameter_physical_height_grading_le S C z (base + c + 6))
    (liftSectorParameter_physical_height_grading_le S C z (b + loss + c + 6))
    (normData.choose_spec.2 rsel hrsel z hz)

theorem N01Properties.endpointFlow_pure_scalar_weightedJetNorm_budget_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ sectorNeighborhood S base ε ε,
      circleWeightedJetNorm T (3 / 4 : ℝ) b c
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
          (fun _ => scalarParameterDirection S)) ≤
        K * ((1 + pairGrading (sectorGrading S) realGrading (b + loss) z) *
          (1 + pairGrading (sectorGrading S) realGrading (base + c + 6) z) +
          (1 + pairGrading (sectorGrading S) realGrading (b + loss + c + 6) z)) := by
  let data := hN.endpointFlow_pure_scalar_weightedJetNorm_budget_bound_uniform_radius hS hT n b c
  exact ⟨data.choose, data.choose_spec.1, data.choose_spec.2 rsel hrsel⟩

end ContinuousFlexibility.Statements
