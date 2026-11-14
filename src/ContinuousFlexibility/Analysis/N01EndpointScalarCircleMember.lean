module

public import ContinuousFlexibility.Analysis.N01EndpointScalarHeightBounds
public import ContinuousFlexibility.Analysis.N01HeightPlateauDirections
public import ContinuousFlexibility.Analysis.N01WeightedPlateauEnvelope
public import ContinuousFlexibility.Analysis.CircleEnergyEnvelope

/-!
# Genuine circle membership of every positive pure scalar endpoint jet

The circle field is the previously selected N01 jet. Its component
energy comes from actual physical plateau localizations of the supplied
height, with the trace removed by constant-height locality. The proof
keeps the infinite component sum; a uniform pointwise bound alone is
never used as a summability substitute.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointScalarCircleMemberStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointScalarCircleMemberRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

private theorem circleMember_of_local_height_envelope
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ}
    (hv : ∀ m, ContDiff ℝ ∞ (v m) ∧ Function.Periodic (v m) Real.pi)
    (hM : ∀ m, 1 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (g : ℕ → ℕ → ℝ) (energy : ℕ → ℕ → ℝ≥0∞)
    (hmono : ∀ m, Monotone (fun s => g s m))
    (hg : ∀ s m, g s m ≤ Real.sqrt (energy s m).toReal)
    (base loss : ℕ) (A : ℕ → ℝ) (hA : ∀ s, 0 ≤ A s)
    (henergy : ∀ s, (∑' m : ℕ,
      ENNReal.ofReal ((T.M (T.sample m) ^ (s + 1)) ^ 2) *
        energy (max base (s + loss)) m) < ⊤)
    (hpoint : ∀ s, ∃ K : ℝ, 0 ≤ K ∧ ∀ m b c, b + c ≤ s → ∀ θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤ K * T.M (T.sample m) ^ (c + 1) *
          (A s * g base m + g (s + loss) m)) :
    CircleMember T γ v := by
  apply circleMember_of_energy_envelope hv
    (fun m => zero_le_one.trans (hM m)) hH
  intro s
  obtain ⟨K, hK, hp⟩ := hpoint s
  let t := max base (s + loss)
  let E : ℕ → ℝ≥0∞ := fun m =>
    ENNReal.ofReal ((T.M (T.sample m) ^ (s + 1)) ^ 2) * energy t m
  refine ⟨E, K * (A s + 1), henergy s,
    mul_nonneg hK (add_nonneg (hA s) zero_le_one), ?_⟩
  intro m b c horder θ
  let e : ℝ := Real.sqrt (energy t m).toReal
  have he : 0 ≤ e := Real.sqrt_nonneg _
  have hbase : g base m ≤ e :=
    (hmono m (le_max_left _ _)).trans (hg t m)
  have hhigh : g (s + loss) m ≤ e :=
    (hmono m (le_max_right _ _)).trans (hg t m)
  have hW : A s * g base m + g (s + loss) m ≤ (A s + 1) * e := by
    calc
      _ ≤ A s * e + e := add_le_add (mul_le_mul_of_nonneg_left hbase (hA s)) hhigh
      _ = _ := by ring
  have hsqrt : Real.sqrt (E m).toReal = T.M (T.sample m) ^ (s + 1) * e := by
    dsimp only [E, e]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (zero_le_one.trans (hM m)) _)]
  have hc : T.M (T.sample m) ^ (c + 1) ≤ T.M (T.sample m) ^ (s + 1) :=
    pow_le_pow_right₀ (hM m) (by omega)
  calc
    _ ≤ K * T.M (T.sample m) ^ (c + 1) *
        (A s * g base m + g (s + loss) m) := hp m b c horder θ
    _ ≤ K * T.M (T.sample m) ^ (c + 1) * ((A s + 1) * e) :=
      mul_le_mul_of_nonneg_left hW
        (mul_nonneg hK (pow_nonneg (zero_le_one.trans (hM m)) _))
    _ ≤ K * T.M (T.sample m) ^ (s + 1) * ((A s + 1) * e) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hK)
        (mul_nonneg (add_nonneg (hA s) zero_le_one) he)
    _ = K * (A s + 1) * Real.sqrt (E m).toReal := by rw [hsqrt]; ring

theorem N01Properties.endpointFlow_pure_scalar_circleMember
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ)
    (hz : z ∈ sectorNeighborhood S base ε ε) :
    CircleMember T (3 / 4 : ℝ)
      (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (fun _ => scalarParameterDirection S)) := by
  let lossData := hN.endpointFlow_pure_scalar_weighted_height_bound hS hT rsel hrsel n
  let d : ℕ := lossData.choose
  let horders := lossData.choose_spec
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 1 ≤ T.M (T.sample m) := (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  let ξ : HeightPair S := (liftSectorParameter S C z).1.1
  let directions := hN.exists_height_pair_plateau_directions hS hT ξ
  let η : ℕ → HeightPair S := directions.choose
  have hmono : Monotone (heightPairGrading S) :=
    pairGrading_monotone
      (gradedSeminorm_monotone (fun i => (S.height (3 / 4 : ℝ)).level i)
        (S.height (3 / 4 : ℝ)).bond)
      (fun _ _ _ _ => le_rfl)
  let energy : ℕ → ℕ → ℝ≥0∞ := fun s => physicalPlateauEnergy D T C (3 / 4 : ℝ) s
    ((S.height (3 / 4 : ℝ)).decode ξ.1)
  let A : ℕ → ℝ := fun s =>
    (n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + (loss + d)) z
  apply circleMember_of_local_height_envelope
    (hN.endpointFlowScalarJets_regular hS hT rsel hrsel (n + 1) z hz
      (fun _ => scalarParameterDirection S)) hM hH
    (fun s m => heightPairGrading S s (η m)) energy
    (fun m i j hij => hmono hij (η m))
    (fun s m => (directions.choose_spec.2.2.2 s).2 m) base (loss + d) A
    (fun s => add_nonneg (by positivity) (apply_nonneg _ _))
    (fun s => hN.physicalPlateauEnergy_weighted_tsum_lt_top hS hT
      (hS.1 (3 / 4 : ℝ)) ξ.1 (max base (s + (loss + d))) (s + 1))
  intro s
  let pointData := horders s
  refine ⟨pointData.choose, pointData.choose_spec.1.le, ?_⟩
  intro m b c horder θ
  have hpoint := pointData.choose_spec.2 m b c θ (by omega) z hz (η m)
    (directions.choose_spec.2.2.1 m)
  exact hpoint.trans_eq (congrArg (fun t : ℕ =>
    pointData.choose * T.M (T.sample m) ^ (c + 1) *
      (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading t z) *
        heightPairGrading S base (η m) + heightPairGrading S t (η m)))
    (Nat.add_assoc s loss d))

end ContinuousFlexibility.Statements
