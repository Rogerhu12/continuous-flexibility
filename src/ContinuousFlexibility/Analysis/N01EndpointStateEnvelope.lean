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

private theorem cyclic_tuple_property_of_last_slot
    {E : Type*} (n : ℕ) (P : (Fin (n + 1) → E) → Prop) (Q : E → Prop)
    (hrotate : ∀ w, P (Fin.snoc (Fin.tail w) (w 0)) → P w)
    (hlast : ∀ (vs : Fin n → E) (u : E), Q u → P (Fin.snoc vs u))
    (v : Fin (n + 1) → E) (i : Fin (n + 1)) (hi : Q (v i)) :
    P v := by
  have haux : ∀ k : ℕ, ∀ (w : Fin (n + 1) → E) (a : Fin (n + 1)),
      a.val = k → Q (w a) → P w := by
    intro k
    induction k with
    | zero =>
      intro w a ha hw
      have ha0 : a = 0 := Fin.ext ha
      have hw0 : Q (w 0) :=
        Eq.mp (congrArg (fun t : Fin (n + 1) => Q (w t)) ha0) hw
      exact hrotate w (hlast (Fin.tail w) (w 0) hw0)
    | succ k ih =>
      intro w a ha hw
      have hk : k < n := by have halt := a.isLt; omega
      let a' : Fin n := ⟨k, hk⟩
      let w' : Fin (n + 1) → E :=
        Fin.snoc (α := fun _ : Fin (n + 1) => E) (Fin.tail w) (w 0)
      have haa : a'.succ = a := Fin.ext ha.symm
      have hentry : w' a'.castSucc = w a :=
        (show w' a'.castSucc = w a'.succ from
          Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => E) (w 0) (Fin.tail w) a').trans
            (congrArg w haa)
      have hw' : Q (w' a'.castSucc) := Eq.mpr (congrArg Q hentry) hw
      exact hrotate w (ih w' a'.castSucc rfl hw')
  exact haux i.val v i rfl hi

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlowScalarJets_state_slot_energy_envelope
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n s : ℕ)
    (v : Fin (n + 1) → (StateDirections S × ℝ)) (i : Fin (n + 1)) (hi : (v i).2 = 0) :
    ∃ E : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, E m) < ⊤ ∧ 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m b c, b + c ≤ s → ∀ θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v m) θ| ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (max base (s + loss)) z) *
          Real.sqrt (E m).toReal := by
  let p := pairGrading (sectorGrading S) realGrading
  let j : ℕ := max base (s + loss)
  let boundData := N01Properties.endpointFlowScalarJets_state_energy_bound
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT rsel hrsel n s
  let K₀ : ℝ := boundData.choose
  have hK₀ : 0 < K₀ := boundData.choose_spec.1
  let envelope : (Fin (n + 1) → (StateDirections S × ℝ)) → Prop := fun w =>
    ∃ E : ℕ → ℝ≥0∞, ∃ K : ℝ, (∑' m, E m) < ⊤ ∧ 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m b c, b + c ≤ s → ∀ θ,
        (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
          |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z w m) θ| ≤
          K * (1 + p j z) * Real.sqrt (E m).toReal
  refine cyclic_tuple_property_of_last_slot n envelope
    (fun u : StateDirections S × ℝ => u.2 = 0) ?_ ?_ v i hi
  · intro w hw
    let E : ℕ → ℝ≥0∞ := hw.choose
    let K : ℝ := hw.choose_spec.choose
    refine ⟨E, K, hw.choose_spec.choose_spec.1, hw.choose_spec.choose_spec.2.1, ?_⟩
    intro z hz m b c hbc θ
    have hrot := congrArg (fun f : ℕ → ℝ → ℝ => iteratedDeriv b (f m) θ)
      (hN.endpointFlowScalarJets_rotate hS hT rsel hrsel n z hz w)
    have hweighted := congrArg (fun a : ℝ =>
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) * |a|) hrot
    exact hweighted.trans_le (hw.choose_spec.choose_spec.2.2 z hz m b c hbc θ)
  · intro vs u hu
    let E : ℕ → ℝ≥0∞ := stateLocalizationEnergy D T C j (s + 1) u
    let P : ℝ := ∏ a : Fin n, p j (vs a)
    have hP : 0 ≤ P := Finset.prod_nonneg (fun a _ => apply_nonneg (p j) (vs a))
    refine ⟨E, K₀ * P,
      N01Properties.stateLocalizationEnergy_tsum_lt_top
        (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
        hN hS hT j (s + 1) u,
      mul_nonneg hK₀.le hP, ?_⟩
    intro z hz m b c hbc θ
    exact (boundData.choose_spec.2 z hz vs u hu m b c hbc θ).trans_eq
      (congrArg (fun a : ℝ => a * Real.sqrt (E m).toReal)
        (mul_right_comm K₀ (1 + p j z) P))

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
  let data := N01Properties.endpointFlowScalarJets_state_slot_energy_envelope
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT rsel hrsel n s v i hi
  let E : ℕ → ℝ≥0∞ := data.choose
  let K : ℝ := data.choose_spec.choose
  have hE : (∑' m, E m) < ⊤ := data.choose_spec.choose_spec.1
  have hK : 0 ≤ K := data.choose_spec.choose_spec.2.1
  let p := pairGrading (sectorGrading S) realGrading
  let j : ℕ := max base (s + loss)
  refine ⟨E, K * (1 + (p j x + p j w)), hE,
    mul_nonneg hK (add_nonneg zero_le_one
      (add_nonneg (apply_nonneg (p j) x) (apply_nonneg (p j) w))), ?_⟩
  intro t ht hz m b c hbc θ
  exact (data.choose_spec.choose_spec.2.2 (x + t • w) hz m b c hbc θ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl 1) (seminorm_line_le_of_abs_le_one (p j) x w ht)) hK)
      (Real.sqrt_nonneg _))

end ContinuousFlexibility.Statements
