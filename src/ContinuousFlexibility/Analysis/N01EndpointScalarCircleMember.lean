import ContinuousFlexibility.Analysis.N01EndpointScalarHeightBounds
import ContinuousFlexibility.Analysis.N01HeightPlateauDirections
import ContinuousFlexibility.Analysis.N01WeightedPlateauEnvelope
import ContinuousFlexibility.Analysis.CircleEnergyEnvelope

/-!
# Genuine circle membership of every positive pure scalar endpoint jet

The circle field is the previously selected N01 jet. Its component
energy comes from actual physical plateau localizations of the supplied
height, with the trace removed by constant-height locality. The proof
keeps the infinite component sum; a uniform pointwise bound alone is
never used as a summability substitute.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointScalarCircleMemberStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointScalarCircleMemberRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

private theorem endpointFlow_pure_scalar_circleMember_of_plateau
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ)
    (hz : z ∈ sectorNeighborhood S base ε ε)
    (η : ℕ → HeightPair S)
    (hlocal : ∀ m, ∃ c : ℝ, ∀ t ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
      heightPairField S (η m) (t, θ) =
        heightPairField S (liftSectorParameter S C z).1.1 (t, θ) + c)
    (henergy : ∀ s m, heightPairGrading S s (η m) ≤
      Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) s
        ((S.height (3 / 4 : ℝ)).decode (liftSectorParameter S C z).1.1.1) m).toReal) :
    CircleMember T (3 / 4 : ℝ)
      (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (fun _ => scalarParameterDirection S)) := by
  have hD : IsAccumulatingProfile D := hN.1.1
  have hgeom : AccumulatingProfileBounds D hD.choose := hD.choose_spec
  have hs (m : ℕ) : T.sample m ∈ radialCore D :=
    materialSample_mem_radialCore hT hgeom.2.1 m
  have hM (m : ℕ) : 1 ≤ T.M (T.sample m) := (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  let ξ : HeightPair S := (liftSectorParameter S C z).1.1
  have hmono : Monotone (heightPairGrading S) :=
    pairGrading_monotone
      (gradedSeminorm_monotone (fun i => (S.height (3 / 4 : ℝ)).level i)
        (S.height (3 / 4 : ℝ)).bond)
      (fun _ _ _ _ => le_rfl)
  apply circleMember_of_energy_envelope
    (hN.endpointFlowScalarJets_regular hS hT rsel hrsel (n + 1) z hz
      (fun _ => scalarParameterDirection S))
    (fun m => zero_le_one.trans (hM m)) hH
  intro s
  let data := N01Properties.endpointFlow_pure_scalar_weighted_height_bound
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT rsel hrsel n s
  let K : ℝ := data.choose
  have hK : 0 < K := data.choose_spec.1
  let t : ℕ := max base (s + loss)
  let E : ℕ → ℝ≥0∞ := fun m =>
    ENNReal.ofReal ((T.M (T.sample m) ^ (s + 1)) ^ 2) *
      physicalPlateauEnergy D T C (3 / 4 : ℝ) t
        ((S.height (3 / 4 : ℝ)).decode ξ.1) m
  let A : ℝ := (n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + loss) z
  have hA : 0 ≤ A := add_nonneg (by positivity) (apply_nonneg _ _)
  have hEt : (∑' m : ℕ, E m) < ⊤ :=
    hN.physicalPlateauEnergy_weighted_tsum_lt_top hS hT (hS.1 (3 / 4 : ℝ)) ξ.1 t (s + 1)
  refine ⟨E, K * (A + 1), hEt, mul_nonneg hK.le (by positivity), ?_⟩
  intro m b c horder θ
  let e : ℝ := Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) t
    ((S.height (3 / 4 : ℝ)).decode ξ.1) m).toReal
  have he : 0 ≤ e := Real.sqrt_nonneg _
  have hbase : heightPairGrading S base (η m) ≤ e :=
    (hmono (le_max_left _ _) (η m)).trans (henergy t m)
  have hhigh : heightPairGrading S (s + loss) (η m) ≤ e :=
    (hmono (le_max_right _ _) (η m)).trans (henergy t m)
  have hW : A * heightPairGrading S base (η m) +
      heightPairGrading S (s + loss) (η m) ≤ (A + 1) * e := by
    calc
      _ ≤ A * e + e := add_le_add (mul_le_mul_of_nonneg_left hbase hA) hhigh
      _ = _ := by ring
  have hsqrt : Real.sqrt (E m).toReal = T.M (T.sample m) ^ (s + 1) * e := by
    dsimp only [E, e]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (zero_le_one.trans (hM m)) _)]
  have hp :
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b
          (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
            (fun _ => scalarParameterDirection S) m) θ| ≤
        K * T.M (T.sample m) ^ (c + 1) *
          (A * heightPairGrading S base (η m) + heightPairGrading S (s + loss) (η m)) :=
    data.choose_spec.2 m b c θ (by omega) z hz (η m) (hlocal m)
  have hc : T.M (T.sample m) ^ (c + 1) ≤ T.M (T.sample m) ^ (s + 1) :=
    pow_le_pow_right₀ (hM m) (by omega)
  calc
    _ ≤ K * T.M (T.sample m) ^ (c + 1) *
        (A * heightPairGrading S base (η m) + heightPairGrading S (s + loss) (η m)) := hp
    _ ≤ K * T.M (T.sample m) ^ (c + 1) * ((A + 1) * e) :=
      mul_le_mul_of_nonneg_left hW
        (mul_nonneg hK.le (pow_nonneg (zero_le_one.trans (hM m)) _))
    _ ≤ K * T.M (T.sample m) ^ (s + 1) * ((A + 1) * e) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hK.le)
        (mul_nonneg (by positivity) he)
    _ = K * (A + 1) * Real.sqrt (E m).toReal := by rw [hsqrt]; ring

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
  let data := N01Properties.exists_height_pair_plateau_directions
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT (show HeightPair S from (liftSectorParameter S C z).1.1)
  exact endpointFlow_pure_scalar_circleMember_of_plateau hN hS hT rsel hrsel n z hz
    data.choose data.choose_spec.2.2.1 (fun s m => (data.choose_spec.2.2.2 s).2 m)

end ContinuousFlexibility.Statements
