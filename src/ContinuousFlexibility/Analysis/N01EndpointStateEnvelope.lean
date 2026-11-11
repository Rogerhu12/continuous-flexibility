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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlowScalarJets_state_slot_energy_envelope
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ)
    (v : Fin (n + 1) → (StateDirections S × ℝ)) (i : Fin (n + 1)) (hi : (v i).2 = 0) :
    ∃ E : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, E m) < ⊤ ∧ 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m b c, b + c ≤ s → ∀ θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT (n + 1) z v m) θ| ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (max base (s + loss)) z) *
          Real.sqrt (E m).toReal := by
  let p := pairGrading (sectorGrading S) realGrading
  let j : ℕ := max base (s + loss)
  have haux : ∀ k : ℕ, ∀ (w : Fin (n + 1) → (StateDirections S × ℝ))
      (a : Fin (n + 1)), a.val = k → (w a).2 = 0 →
      ∃ E : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, E m) < ⊤ ∧ 0 ≤ K ∧
        ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m b c, b + c ≤ s → ∀ θ,
        (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
          |iteratedDeriv b (hN.endpointFlowScalarJets hS hT (n + 1) z w m) θ| ≤
          K * (1 + p j z) * Real.sqrt (E m).toReal := by
    intro k
    induction k with
    | zero =>
      intro w a ha hw
      have ha0 : a = 0 := Fin.ext ha
      rw [ha0] at hw
      obtain ⟨K, hK, hb⟩ := hN.endpointFlowScalarJets_state_energy_bound hS hT n s
      refine ⟨stateLocalizationEnergy D T C j (s + 1) (w 0),
        K * ∏ a : Fin n, p j (Fin.tail w a),
        hN.stateLocalizationEnergy_tsum_lt_top hS hT j (s + 1) (w 0),
        mul_nonneg hK.le (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)), ?_⟩
      intro z hz m b c hbc θ
      have hrot := congrArg (fun f : ℕ → ℝ → ℝ => iteratedDeriv b (f m) θ)
        (hN.endpointFlowScalarJets_rotate hS hT n z hz w)
      rw [hrot]
      exact (hb z hz (Fin.tail w) (w 0) hw m b c hbc θ).trans_eq (by
        dsimp only [j, p]
        ring)
    | succ k ih =>
      intro w a ha hw
      have hk : k < n := by have halt := a.isLt; omega
      let a' : Fin n := ⟨k, hk⟩
      let w' : Fin (n + 1) → (StateDirections S × ℝ) := Fin.snoc (Fin.tail w) (w 0)
      have haa : a'.succ = a := Fin.ext (by simpa only [a', Fin.val_succ] using ha.symm)
      have hw' : (w' a'.castSucc).2 = 0 := by
        dsimp only [w']
        rw [Fin.snoc_castSucc]
        change (w a'.succ).2 = 0
        rw [haa]
        exact hw
      obtain ⟨E, K, hE, hK, hb⟩ := ih w' a'.castSucc rfl hw'
      refine ⟨E, K, hE, hK, ?_⟩
      intro z hz m b c hbc θ
      have hrot := congrArg (fun f : ℕ → ℝ → ℝ => iteratedDeriv b (f m) θ)
        (hN.endpointFlowScalarJets_rotate hS hT n z hz w)
      rw [hrot]
      exact hb z hz m b c hbc θ
  exact haux i.val v i rfl hi

theorem N01Properties.endpointFlowScalarJets_state_slot_line_energy_envelope
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ)
    (x w : StateDirections S × ℝ)
    (v : Fin (n + 1) → (StateDirections S × ℝ)) (i : Fin (n + 1)) (hi : (v i).2 = 0) :
    ∃ E : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, E m) < ⊤ ∧ 0 ≤ K ∧
      ∀ t : ℝ, |t| ≤ 1 → x + t • w ∈ sectorNeighborhood S base ε ε →
      ∀ m b c, b + c ≤ s → ∀ θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT (n + 1) (x + t • w) v m) θ| ≤
        K * Real.sqrt (E m).toReal := by
  obtain ⟨E, K, hE, hK, hb⟩ :=
    hN.endpointFlowScalarJets_state_slot_energy_envelope hS hT n s v i hi
  let p := pairGrading (sectorGrading S) realGrading
  let j : ℕ := max base (s + loss)
  refine ⟨E, K * (1 + (p j x + p j w)), hE,
    mul_nonneg hK (add_nonneg zero_le_one (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))), ?_⟩
  intro t ht hz m b c hbc θ
  exact (hb _ hz m b c hbc θ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl 1) (seminorm_line_le_of_abs_le_one (p j) x w ht)) hK)
      (Real.sqrt_nonneg _))

end ContinuousFlexibility.Statements
