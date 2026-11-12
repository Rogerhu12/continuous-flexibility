import ContinuousFlexibility.Analysis.N01EndpointPositiveCircleMember

/-!
# A fixed summable envelope for a genuine state derivative slot

The localized input is fixed while the base point varies. Cyclic
symmetry moves any state slot to the last slot without changing the
actual scalar field or its angular derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointStateEnvelopeStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ENNReal BigOperators

theorem seminorm_line_le_of_abs_le_one
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x w : E) {t : ℝ} (ht : |t| ≤ 1) :
    p (x + t • w) ≤ p x + p w := by
  calc
    _ ≤ p x + p (t • w) := map_add_le_add p x (t • w)
    _ = p x + |t| * p w := by rw [map_smul_eq_mul, Real.norm_eq_abs]
    _ ≤ p x + p w := add_le_add (le_refl _) (mul_le_of_le_one_left (apply_nonneg _ _) ht)

private theorem cyclic_energy_envelope
    {V X : Type*} (n s : ℕ) (U : Set X) (p : X → ℝ)
    (A : (Fin (n + 1) → V) → X → ℕ → ℕ → ℕ → ℝ → ℝ) (Q : V → Prop)
    (hrotate : ∀ v z, z ∈ U → ∀ m b c, b + c ≤ s → ∀ θ,
      A v z m b c θ = A (Fin.snoc (Fin.tail v) (v 0)) z m b c θ)
    (hlast : ∀ (vs : Fin n → V) (u : V), Q u →
      ∃ energy : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, energy m) < ⊤ ∧ 0 ≤ K ∧
        ∀ z ∈ U, ∀ m b c, b + c ≤ s → ∀ θ,
          A (Fin.snoc vs u) z m b c θ ≤ K * (1 + p z) * Real.sqrt (energy m).toReal)
    (v : Fin (n + 1) → V) (i : Fin (n + 1)) (hi : Q (v i)) :
    ∃ energy : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, energy m) < ⊤ ∧ 0 ≤ K ∧
      ∀ z ∈ U, ∀ m b c, b + c ≤ s → ∀ θ,
        A v z m b c θ ≤ K * (1 + p z) * Real.sqrt (energy m).toReal := by
  have haux : ∀ k : ℕ, ∀ (w : Fin (n + 1) → V) (a : Fin (n + 1)),
      a.val = k → Q (w a) →
      ∃ energy : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, energy m) < ⊤ ∧ 0 ≤ K ∧
        ∀ z ∈ U, ∀ m b c, b + c ≤ s → ∀ θ,
          A w z m b c θ ≤ K * (1 + p z) * Real.sqrt (energy m).toReal := by
    intro k
    induction k with
    | zero =>
      intro w a ha hw
      have ha0 : a = 0 := Fin.ext ha
      have hw0 : Q (w 0) := Eq.mp (congrArg (fun j : Fin (n + 1) => Q (w j)) ha0) hw
      obtain ⟨energy, K, henergy, hK, hb⟩ := hlast (Fin.tail w) (w 0) hw0
      refine ⟨energy, K, henergy, hK, ?_⟩
      intro z hz m b c hbc θ
      exact (hrotate w z hz m b c hbc θ).trans_le (hb z hz m b c hbc θ)
    | succ k ih =>
      intro w a ha hw
      have hk : k < n := by have halt := a.isLt; omega
      let a' : Fin n := ⟨k, hk⟩
      let w' : Fin (n + 1) → V :=
        Fin.snoc (α := fun _ : Fin (n + 1) => V) (Fin.tail w) (w 0)
      have haa : a'.succ = a := Fin.ext ha.symm
      have hentry : w' a'.castSucc = w a :=
        (show w' a'.castSucc = w a'.succ from
          Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => V) (w 0) (Fin.tail w) a').trans
            (congrArg w haa)
      have hw' : Q (w' a'.castSucc) := Eq.mpr (congrArg Q hentry) hw
      obtain ⟨energy, K, henergy, hK, hb⟩ := ih w' a'.castSucc rfl hw'
      refine ⟨energy, K, henergy, hK, ?_⟩
      intro z hz m b c hbc θ
      exact (hrotate w z hz m b c hbc θ).trans_le (hb z hz m b c hbc θ)
  exact haux i.val v i rfl hi

private theorem energy_envelope_factor_reorder (K q P e : ℝ) :
    K * (1 + q) * P * e = (K * P) * (1 + q) * e := by ring

private theorem seminorm_energy_bound_on_unit_line
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : Seminorm ℝ X) (x w : X) {t K e y : ℝ}
    (ht : |t| ≤ 1) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hy : y ≤ K * (1 + p (x + t • w)) * e) :
    y ≤ (K * (1 + (p x + p w))) * e :=
  hy.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (seminorm_line_le_of_abs_le_one p x w ht)) hK) he)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlowScalarJets_state_slot_energy_envelope
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n : ℕ) :
    ∃ d : ℕ, ∀ (s : ℕ) (v : Fin (n + 1) → (StateDirections S × ℝ))
      (i : Fin (n + 1)), (v i).2 = 0 →
      ∃ E : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, E m) < ⊤ ∧ 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m b c, b + c ≤ s → ∀ θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v m) θ| ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (max base (s + loss + d)) z) *
          Real.sqrt (E m).toReal := by
  obtain ⟨d, horders⟩ := hN.endpointFlowScalarJets_state_energy_bound hS hT rsel hrsel n
  refine ⟨d, ?_⟩
  intro s v i hi
  let p : ℕ → Seminorm ℝ (StateDirections S × ℝ) := pairGrading (sectorGrading S) realGrading
  let j : ℕ := max base (s + loss + d)
  let pointData := horders s
  let K : ℝ := pointData.choose
  have hK : 0 < K := pointData.choose_spec.1
  refine cyclic_energy_envelope n s (sectorNeighborhood S base ε ε) (p j)
    (fun w z m b c θ =>
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z w m) θ|)
    (fun u : StateDirections S × ℝ => u.2 = 0) ?_ ?_ v i hi
  · intro w z hz m b c hbc θ
    exact congrArg (fun f : ℕ → ℝ → ℝ =>
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (f m) θ|)
      (hN.endpointFlowScalarJets_rotate hS hT rsel hrsel n z hz w)
  · intro vs u hu
    refine ⟨stateLocalizationEnergy D T C j (s + 1) u,
      K * ∏ a : Fin n, p j (vs a),
      hN.stateLocalizationEnergy_tsum_lt_top hS hT j (s + 1) u,
      mul_nonneg hK.le (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)), ?_⟩
    intro z hz m b c hbc θ
    exact (pointData.choose_spec.2 z hz vs u hu m b c hbc θ).trans_eq
      (energy_envelope_factor_reorder K (p j z) (∏ a : Fin n, p j (vs a))
        (Real.sqrt (stateLocalizationEnergy D T C j (s + 1) u m).toReal))

theorem N01Properties.endpointFlowScalarJets_state_slot_line_energy_envelope
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n s : ℕ)
    (x w : StateDirections S × ℝ)
    (v : Fin (n + 1) → (StateDirections S × ℝ)) (i : Fin (n + 1)) (hi : (v i).2 = 0) :
    ∃ E : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, E m) < ⊤ ∧ 0 ≤ K ∧
      ∀ t : ℝ, |t| ≤ 1 → x + t • w ∈ sectorNeighborhood S base ε ε →
      ∀ m b c, b + c ≤ s → ∀ θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) (x + t • w) v m) θ| ≤
        K * Real.sqrt (E m).toReal := by
  obtain ⟨d, horders⟩ := hN.endpointFlowScalarJets_state_slot_energy_envelope hS hT rsel hrsel n
  let data := horders s v i hi
  let energy : ℕ → ℝ≥0∞ := data.choose
  let constantData := data.choose_spec
  let K : ℝ := constantData.choose
  have henergy : (∑' m, energy m) < ⊤ := constantData.choose_spec.1
  have hK : 0 ≤ K := constantData.choose_spec.2.1
  let p : ℕ → Seminorm ℝ (StateDirections S × ℝ) := pairGrading (sectorGrading S) realGrading
  let j : ℕ := max base (s + loss + d)
  refine ⟨energy, K * (1 + (p j x + p j w)), henergy,
    mul_nonneg hK (add_nonneg zero_le_one (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))), ?_⟩
  intro t ht hz m b c hbc θ
  exact seminorm_energy_bound_on_unit_line (p j) x w ht hK (Real.sqrt_nonneg _)
    (constantData.choose_spec.2.2 _ hz m b c hbc θ)

end ContinuousFlexibility.Statements
