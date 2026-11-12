import ContinuousFlexibility.Analysis.N01EndpointHeightLineEnvelope
import ContinuousFlexibility.Analysis.CircleFiniteEnergyEnvelopes
import ContinuousFlexibility.Analysis.CircleJetAssembly

/-!
# Actual summable second-variation envelopes of the endpoint flow

The fixed state-direction energies and the two fixed height energies are
combined through the genuine multilinear identity of every angular jet.
This supplies the projective Taylor estimate on any open subdomain of
the N01 sector neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointSecondEnvelopeStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal BigOperators

private theorem weighted_abs_multilinear_scalar_split
    {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    (u : E) (a : Fin k → ℝ) (v : Fin k → E) {weight : ℝ} (hw : 0 ≤ weight) :
    weight * |F v| ≤
      |∏ i, a i| * (weight * |F (fun _ => u)|) +
      ∑ i : Fin k, weight * |F (multilinearDifferenceTuple (fun j => a j • u) v i)| := by
  classical
  let q : Fin k → E := fun i => a i • u
  have hidentity : F v = F q + ∑ i : Fin k, F (multilinearDifferenceTuple q v i) := by
    have h := F.map_sub_map_piecewise v q Finset.univ
    have heq : F v - F q = ∑ i : Fin k, F (multilinearDifferenceTuple q v i) := by
      simpa only [Finset.piecewise_univ, Finset.mem_univ, true_implies,
        multilinearDifferenceTuple, eq_comm] using h
    calc
      F v = F q + (F v - F q) := by ring
      _ = _ := congrArg (fun z => F q + z) heq
  have hq : F q = (∏ i, a i) * F (fun _ => u) := by
    simpa only [smul_eq_mul] using F.map_smul_univ a (fun _ => u)
  calc
    _ = weight * |F q + ∑ i : Fin k, F (multilinearDifferenceTuple q v i)| := by rw [hidentity]
    _ ≤ weight * (|F q| + ∑ i : Fin k, |F (multilinearDifferenceTuple q v i)|) :=
      mul_le_mul_of_nonneg_left
        ((abs_add_le _ _).trans (add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs _ _))) hw
    _ = _ := by rw [hq, abs_mul, mul_add, Finset.mul_sum]; ring

private theorem scalar_split_diagonal_snd
    {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (u : E × ℝ) (hu : u.2 = 1) (v : Fin k → E × ℝ) (i : Fin k) :
    (multilinearDifferenceTuple (fun j => (v j).2 • u) v i i).2 = 0 := by
  simp only [multilinearDifferenceTuple, lt_self_iff_false, if_false, if_true]
  change (v i).2 - (v i).2 * u.2 = 0
  rw [hu, mul_one, sub_self]

private theorem scalar_add_fin_const_sum (n : ℕ) (r : ℝ) :
    r + ∑ _i : Fin (n + 1), r = ((n : ℝ) + 2) * r := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private theorem circleSecondEnvelopes_of_line_bounds
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {T : MaterialData} {γ : ℝ} {U V : Set E}
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hU : IsOpen U) (hsub : U ⊆ V)
    (hbound : ∀ (n s : ℕ) (x w : E) (v : Fin (n + 1) → E),
      ∃ energy : ℕ → ℝ≥0∞, ∃ K : ℝ,
        (∑' m, energy m) < ⊤ ∧ 0 ≤ K ∧
          ∀ t : ℝ, |t| ≤ 1 → x + t • w ∈ V →
          ∀ m b c, b + c ≤ s → ∀ θ,
            (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
              |iteratedDeriv b (A (n + 1) (x + t • w) v m) θ| ≤
                K * Real.sqrt (energy m).toReal) :
    CircleJetSecondEnvelopes (T := T) (γ := γ) (U := U) A := by
  intro n x hx v w
  have hline : Continuous (fun t : ℝ => x + t • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnear : {t : ℝ | x + t • w ∈ U} ∈ 𝓝 (0 : ℝ) :=
    hline.continuousAt.preimage_mem_nhds (by
      simpa only [zero_smul, add_zero] using hU.mem_nhds hx)
  let radiusData := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ := radiusData.choose
  have hδ : 0 < δ := radiusData.choose_spec.1
  have hmem (t : ℝ) (ht : |t| < min δ 1) : x + t • w ∈ U := by
    apply radiusData.choose_spec.2
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      ht.trans_le (min_le_left δ 1)
  refine ⟨min δ 1, lt_min hδ zero_lt_one, hmem, ?_⟩
  intro s
  let lineData := hbound (n + 1) s x w (Fin.cons w (Fin.cons w v))
  exact ⟨lineData.choose, lineData.choose_spec.choose,
    lineData.choose_spec.choose_spec.1, lineData.choose_spec.choose_spec.2.1,
    fun t ht => lineData.choose_spec.choose_spec.2.2 t
      (ht.trans_le (min_le_right δ 1)).le (hsub (hmem t ht))⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlowScalarJets_line_energy_envelope
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n s : ℕ) (x w : StateDirections S × ℝ)
    (v : Fin (n + 1) → (StateDirections S × ℝ)) :
    ∃ E : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, E m) < ⊤ ∧ 0 ≤ K ∧
      ∀ t : ℝ, |t| ≤ 1 → x + t • w ∈ sectorNeighborhood S base ε ε →
      ∀ m b c, b + c ≤ s → ∀ θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) (x + t • w) v m) θ| ≤
        K * Real.sqrt (E m).toReal := by
  classical
  let q : Fin (n + 1) → (StateDirections S × ℝ) := fun i =>
    (v i).2 • scalarParameterDirection S
  let stateData (i : Fin (n + 1)) :=
    hN.endpointFlowScalarJets_state_slot_line_energy_envelope hS hT rsel hrsel n s x w
      (multilinearDifferenceTuple q v i) i
      (scalar_split_diagonal_snd (E := StateDirections S)
        (scalarParameterDirection S) rfl v i)
  let Es : Fin (n + 1) → ℕ → ℝ≥0∞ := fun i => (stateData i).choose
  let Ks : Fin (n + 1) → ℝ := fun i => (stateData i).choose_spec.choose
  have hEs (i : Fin (n + 1)) : (∑' m, Es i m) < ⊤ :=
    (stateData i).choose_spec.choose_spec.1
  have hKs (i : Fin (n + 1)) : 0 ≤ Ks i :=
    (stateData i).choose_spec.choose_spec.2.1
  let pureData :=
    hN.endpointFlow_pure_scalar_line_energy_envelope hS hT rsel hrsel n s x w
  let Eq : ℕ → ℝ≥0∞ := pureData.choose
  let Kq : ℝ := pureData.choose_spec.choose
  have hEq : (∑' m, Eq m) < ⊤ := pureData.choose_spec.choose_spec.1
  have hKq : 0 ≤ Kq := pureData.choose_spec.choose_spec.2.1
  let ι := Option (Fin (n + 1))
  let E : ι → ℕ → ℝ≥0∞
    | none => Eq
    | some i => Es i
  let K : ι → ℝ
    | none => |∏ i : Fin (n + 1), (v i).2| * Kq
    | some i => Ks i
  have hE (i : ι) : (∑' m, E i m) < ⊤ := by
    cases i with
    | none => exact hEq
    | some i => exact hEs i
  have hK (i : ι) : 0 ≤ K i := by
    cases i with
    | none => exact mul_nonneg (abs_nonneg _) hKq
    | some i => exact hKs i
  let total : ℕ → ℝ≥0∞ := fun m => ∑ i : ι, ENNReal.ofReal (K i ^ 2) * E i m
  have htotal : (∑' m, total m) < ⊤ := finiteEnergyEnvelope_tsum_lt_top K E hE
  refine ⟨total, (n : ℝ) + 2, htotal, by positivity, ?_⟩
  intro t ht hz m b c hbc θ
  let J := hN.sectorFlow_closed_angularTower hS hT m (rsel m)
    (hrsel m) b θ
  let F := (J.D (n + 1) (x + t • w)).toMultilinearMap
  have hjet (u : Fin (n + 1) → (StateDirections S × ℝ)) :
      iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) (x + t • w) u m) θ = F u :=
    hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel (n + 1) (x + t • w) hz u m b θ
  let weight : ℝ := T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))
  have hsample := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hweight : 0 ≤ weight := mul_nonneg
    (pow_nonneg (zero_le_one.trans (hT.2.1 _ hsample).2.2.2) _)
    (Real.rpow_nonneg (hT.2.1 _ hsample).2.1.le _)
  let R : ℝ := Real.sqrt (total m).toReal
  have hpoint (i : ι) : K i * Real.sqrt (E i m).toReal ≤ R :=
    finiteEnergyEnvelope_term_le K (fun j => E j m) hK
      (fun j => (ENNReal.le_tsum (f := E j) m).trans_lt (hE j)) i
  have hpure : |∏ i : Fin (n + 1), (v i).2| *
      (weight * |F (fun _ => scalarParameterDirection S)|) ≤ R := by
    have hb : weight * |F (fun _ => scalarParameterDirection S)| ≤
        Kq * Real.sqrt (Eq m).toReal :=
      (congrArg (fun y : ℝ => weight * |y|)
        (hjet (fun _ => scalarParameterDirection S))).symm.trans_le
          (pureData.choose_spec.choose_spec.2.2 t ht hz m b c hbc θ)
    exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans
      ((mul_assoc _ _ _).symm.trans_le (hpoint none))
  have hterm (i : Fin (n + 1)) : weight * |F (multilinearDifferenceTuple q v i)| ≤ R := by
    have hb : weight * |F (multilinearDifferenceTuple q v i)| ≤
        Ks i * Real.sqrt (Es i m).toReal :=
      (congrArg (fun y : ℝ => weight * |y|)
        (hjet (multilinearDifferenceTuple q v i))).symm.trans_le
          ((stateData i).choose_spec.choose_spec.2.2 t ht hz m b c hbc θ)
    exact hb.trans (hpoint (some i))
  refine (congrArg (fun y : ℝ => weight * |y|) (hjet v)).trans_le ?_
  calc
    _ ≤ |∏ i : Fin (n + 1), (v i).2| *
        (weight * |F (fun _ => scalarParameterDirection S)|) +
        ∑ i : Fin (n + 1), weight * |F (multilinearDifferenceTuple q v i)| :=
      weighted_abs_multilinear_scalar_split F (scalarParameterDirection S)
        (fun i => (v i).2) v hweight
    _ ≤ R + ∑ _i : Fin (n + 1), R :=
      add_le_add hpure (Finset.sum_le_sum (fun i _ => hterm i))
    _ = ((n : ℝ) + 2) * R := scalar_add_fin_const_sum n R

theorem N01Properties.endpointFlowScalarJets_second_envelopes
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    (hsub : U ⊆ sectorNeighborhood S base ε ε) :
    CircleJetSecondEnvelopes (T := T) (γ := (3 / 4 : ℝ)) (U := U)
      (hN.endpointFlowScalarJets hS hT rsel hrsel) := by
  exact circleSecondEnvelopes_of_line_bounds
    (E := StateDirections S × ℝ) (T := T) (γ := (3 / 4 : ℝ))
    (U := U) (V := sectorNeighborhood S base ε ε)
    (hN.endpointFlowScalarJets hS hT rsel hrsel) hU hsub
    (fun n s x w v =>
      hN.endpointFlowScalarJets_line_energy_envelope hS hT rsel hrsel n s x w v)

end ContinuousFlexibility.Statements
