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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

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
  obtain ⟨K, hK, hpoint⟩ := hN.endpointFlow_pure_scalar_weighted_height_bound hS hT rsel hrsel n b
  obtain ⟨K₀, hK₀, hE₀⟩ := hN.physicalPlateauEnergy_weighted_tsum_le_grading_sq
    hS hT (hS.1 (3 / 4 : ℝ)) base (c + 1)
  obtain ⟨K₁, hK₁, hE₁⟩ := hN.physicalPlateauEnergy_weighted_tsum_le_grading_sq
    hS hT (hS.1 (3 / 4 : ℝ)) (b + loss) (c + 1)
  let L : ℝ := Real.sqrt K₀ + Real.sqrt K₁
  have hL : 0 ≤ L := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨Real.sqrt (2 * Real.pi) * K * L,
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK.le) hL, ?_⟩
  intro z hz
  let ξ : HeightPair S := (liftSectorParameter S C z).1.1
  obtain ⟨η, _, _, hlocal, henergy⟩ := hN.exists_height_pair_plateau_directions hS hT ξ
  let A : ℝ := (n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (b + loss) z
  have hA : 0 ≤ A := add_nonneg (by positivity) (apply_nonneg _ _)
  let E : ℕ → ℕ → ℝ≥0∞ := fun j m =>
    ENNReal.ofReal ((T.M (T.sample m) ^ (c + 1)) ^ 2) *
      physicalPlateauEnergy D T C (3 / 4 : ℝ) j
        ((S.height (3 / 4 : ℝ)).decode ξ.1) m
  let U : ℝ := Real.sqrt K₀ * (S.height (3 / 4 : ℝ)).grading (base + c + 6) ξ.1
  let V : ℝ := Real.sqrt K₁ * (S.height (3 / 4 : ℝ)).grading (b + loss + c + 6) ξ.1
  have hU : 0 ≤ U := mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
  have hV : 0 ≤ V := mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
  have hE : (∑' m, E base m) ≤ ENNReal.ofReal (U ^ 2) := by
    dsimp only [U]
    rw [mul_pow, Real.sq_sqrt hK₀]
    have hi : base + (c + 1) + 5 = base + c + 6 := by omega
    simpa only [E, hi] using hE₀ ξ.1
  have hF : (∑' m, E (b + loss) m) ≤ ENNReal.ofReal (V ^ 2) := by
    dsimp only [V]
    rw [mul_pow, Real.sq_sqrt hK₁]
    have hi : b + loss + (c + 1) + 5 = b + loss + c + 6 := by omega
    simpa only [E, hi] using hE₁ ξ.1
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  have hsqrt (j m : ℕ) : Real.sqrt (E j m).toReal =
      T.M (T.sample m) ^ (c + 1) *
        Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) j
          ((S.height (3 / 4 : ℝ)).decode ξ.1) m).toReal := by
    dsimp only [E]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (hM m) _)]
  have hb (m : ℕ) (θ : ℝ) :
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
          (fun _ => scalarParameterDirection S) m) θ| ≤
        (K * A) * Real.sqrt (E base m).toReal +
          K * Real.sqrt (E (b + loss) m).toReal := by
    have hp := hpoint m b c θ le_rfl z hz (η m) (hlocal m)
    calc
      _ ≤ K * T.M (T.sample m) ^ (c + 1) *
          (A * heightPairGrading S base (η m) +
            heightPairGrading S (b + loss) (η m)) := hp
      _ ≤ K * T.M (T.sample m) ^ (c + 1) *
          (A * Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) base
              ((S.height (3 / 4 : ℝ)).decode ξ.1) m).toReal +
            Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) (b + loss)
              ((S.height (3 / 4 : ℝ)).decode ξ.1) m).toReal) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left ((henergy base).2 m) hA)
            ((henergy (b + loss)).2 m)) (mul_nonneg hK.le (pow_nonneg (hM m) _))
      _ = _ := by rw [hsqrt, hsqrt]; ring
  have hn := circleWeightedJetNorm_le_two_envelopes
    (mul_nonneg hK.le hA) hK.le hU hV hE hF
    (fun m => (hN.endpointFlowScalarJets_regular hS hT rsel hrsel (n + 1) z hz
      (fun _ => scalarParameterDirection S) m).1) hM hH b c hb
  have h₀ : Real.sqrt K₀ ≤ L := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have h₁ : Real.sqrt K₁ ≤ L := le_add_of_nonneg_left (Real.sqrt_nonneg _)
  calc
    _ ≤ Real.sqrt (2 * Real.pi) * (K * A * U + K * V) := hn
    _ = Real.sqrt (2 * Real.pi) * K *
        (A * (Real.sqrt K₀ * (S.height (3 / 4 : ℝ)).grading (base + c + 6) ξ.1) +
          Real.sqrt K₁ * (S.height (3 / 4 : ℝ)).grading (b + loss + c + 6) ξ.1) := by
      dsimp only [U, V]
      ring
    _ ≤ Real.sqrt (2 * Real.pi) * K *
        (A * (L * (S.height (3 / 4 : ℝ)).grading (base + c + 6) ξ.1) +
          L * (S.height (3 / 4 : ℝ)).grading (b + loss + c + 6) ξ.1) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h₀ (apply_nonneg _ _)) hA)
          (mul_le_mul_of_nonneg_right h₁ (apply_nonneg _ _)))
        (mul_nonneg (Real.sqrt_nonneg _) hK.le)
    _ = _ := by dsimp only [A, ξ]; ring

theorem liftSectorParameter_physical_height_grading_le
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : StateDirections S × ℝ) (s : ℕ) :
    (S.height (3 / 4 : ℝ)).grading s (liftSectorParameter S C z).1.1.1 ≤
      (S.height (3 / 4 : ℝ)).grading s C.referenceState.1.1 +
        pairGrading (sectorGrading S) realGrading s z := by
  have heq : (liftSectorParameter S C z).1.1.1 =
      C.referenceState.1.1 + z.1.val.1.1 := rfl
  rw [heq]
  exact (map_add_le_add ((S.height (3 / 4 : ℝ)).grading s) _ _).trans
    (add_le_add (le_refl _) (sectorParameter_height_grading_le S s z))

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
  obtain ⟨K, hK, hbound⟩ :=
    hN.endpointFlow_pure_scalar_weightedJetNorm_height_bound hS hT rsel hrsel n b c
  let J : ℝ := 1 + (S.height (3 / 4 : ℝ)).grading (base + c + 6) C.referenceState.1.1 +
    (S.height (3 / 4 : ℝ)).grading (b + loss + c + 6) C.referenceState.1.1
  let N : ℝ := (n : ℝ) + 2
  have hJ : 1 ≤ J := by
    have h₀ := apply_nonneg ((S.height (3 / 4 : ℝ)).grading (base + c + 6)) C.referenceState.1.1
    have h₁ := apply_nonneg ((S.height (3 / 4 : ℝ)).grading (b + loss + c + 6)) C.referenceState.1.1
    dsimp only [J]
    linarith only [h₀, h₁]
  have hN₀ : 1 ≤ N := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp only [N]
    linarith only [hn]
  refine ⟨K * (N * J), mul_nonneg hK (mul_nonneg (zero_le_one.trans hN₀)
    (zero_le_one.trans hJ)), ?_⟩
  intro z hz
  let p := pairGrading (sectorGrading S) realGrading
  have href₀ : (S.height (3 / 4 : ℝ)).grading (base + c + 6) C.referenceState.1.1 ≤ J := by
    have h := apply_nonneg ((S.height (3 / 4 : ℝ)).grading (b + loss + c + 6)) C.referenceState.1.1
    dsimp only [J]
    linarith only [h]
  have href₁ : (S.height (3 / 4 : ℝ)).grading (b + loss + c + 6) C.referenceState.1.1 ≤ J := by
    have h := apply_nonneg ((S.height (3 / 4 : ℝ)).grading (base + c + 6)) C.referenceState.1.1
    dsimp only [J]
    linarith only [h]
  have hheight₀ : (S.height (3 / 4 : ℝ)).grading (base + c + 6)
      (liftSectorParameter S C z).1.1.1 ≤ J * (1 + p (base + c + 6) z) := by
    apply (liftSectorParameter_physical_height_grading_le S C z _).trans
    have hp : p (base + c + 6) z ≤ J * p (base + c + 6) z :=
      le_mul_of_one_le_left (apply_nonneg _ _) hJ
    nlinarith only [href₀, hp]
  have hheight₁ : (S.height (3 / 4 : ℝ)).grading (b + loss + c + 6)
      (liftSectorParameter S C z).1.1.1 ≤ J * (1 + p (b + loss + c + 6) z) := by
    apply (liftSectorParameter_physical_height_grading_le S C z _).trans
    have hp : p (b + loss + c + 6) z ≤ J * p (b + loss + c + 6) z :=
      le_mul_of_one_le_left (apply_nonneg _ _) hJ
    nlinarith only [href₁, hp]
  have hcoefficient : N + p (b + loss) z ≤ N * (1 + p (b + loss) z) := by
    have hp := le_mul_of_one_le_left (apply_nonneg (p (b + loss)) z) hN₀
    nlinarith only [hp]
  have hlast : J * (1 + p (b + loss + c + 6) z) ≤
      N * (J * (1 + p (b + loss + c + 6) z)) :=
    le_mul_of_one_le_left (mul_nonneg (zero_le_one.trans hJ)
      (add_nonneg zero_le_one (apply_nonneg _ _))) hN₀
  calc
    _ ≤ K * ((N + p (b + loss) z) *
        (S.height (3 / 4 : ℝ)).grading (base + c + 6) (liftSectorParameter S C z).1.1.1 +
        (S.height (3 / 4 : ℝ)).grading (b + loss + c + 6) (liftSectorParameter S C z).1.1.1) :=
      hbound z hz
    _ ≤ K * (N * (1 + p (b + loss) z) * (J * (1 + p (base + c + 6) z)) +
        N * (J * (1 + p (b + loss + c + 6) z))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul hcoefficient hheight₀ (apply_nonneg _ _)
          (mul_nonneg (zero_le_one.trans hN₀) (add_nonneg zero_le_one (apply_nonneg _ _))))
          (hheight₁.trans hlast)) hK
    _ = _ := by dsimp only [p]; ring

end ContinuousFlexibility.Statements
