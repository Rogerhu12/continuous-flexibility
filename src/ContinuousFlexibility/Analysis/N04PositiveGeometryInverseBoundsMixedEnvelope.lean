import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsMixedTerm

/-!
# A genuine mixed inverse envelope with the original state prefix

Strong induction is applied to the evaluated inverse partition formula.
Every surviving state block is an original singleton, and every other
block has lower total order. Consequently only forward state orders up
to the requested prefix are used, even as the spatial order grows.
The exponent `spatial + shift * state - 1` is preserved exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open scoped Topology ContDiff BigOperators

variable (P V : Type*)
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A finite numerical envelope for the actual inverse. The numerical
coefficient and ordinary material power are separate from the spatial
scale and its fixed state-prefix shift. -/
def N04PositiveGeometryMixedInverseEnvelope (n : ℕ) (A : ℝ) (d : ℕ) : Prop :=
  0 < n → ∀ (M H t : ℝ), 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t →
    ∀ (K C : ℕ), 1 ≤ C → ∀ (f g : P × V → V) (x : P × V),
      ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x) →
      ContDiffAt ℝ ∞ g x →
      n04PositiveGeometry_fiberLift f ∘ n04PositiveGeometry_fiberLift g =ᶠ[𝓝 x] id →
      ∀ B : V →L[ℝ] V,
        B.comp ((fderiv ℝ f (n04PositiveGeometry_fiberLift g x)).comp
          (ContinuousLinearMap.inr ℝ P V)) = ContinuousLinearMap.id ℝ V →
        ‖B‖ ≤ M →
        (∀ j, 0 < j → j ≤ n → ∀ w : StateAngleWord j, w.stateArity ≤ K →
          ‖n04PositiveGeometry_projectedJet w.isState f (n04PositiveGeometry_fiberLift g x)‖ ≤
            M * parameterHeightWeight H w.stateArity *
              t ^ (w.angleArity + C * w.stateArity - 1)) →
        ∀ w : StateAngleWord n, w.stateArity ≤ K →
          ‖n04PositiveGeometry_projectedJet w.isState g x‖ ≤
            A * M ^ d * parameterHeightWeight H w.stateArity *
              t ^ (w.angleArity + C * w.stateArity - 1)

private theorem mixedInverseEnvelope_one :
    N04PositiveGeometryMixedInverseEnvelope P V 1 1 2 := by
  intro _ M H t hM hH hHM ht K C hC f g x hf hg hfg B hB hBM hforward w hw
  cases w with
  | state w =>
      cases w
      have hraw := hforward 1 (by omega) le_rfl (.state .nil) hw
      have hi := n04PositiveGeometry_fiberInverse_state_one_norm hf hg hfg B hB
        (StateAngleWord.state .nil).isState rfl
      have hpos : 0 ≤ M * parameterHeightWeight H (StateAngleWord.state .nil).stateArity *
          t ^ ((StateAngleWord.state .nil).angleArity + C *
            (StateAngleWord.state .nil).stateArity - 1) :=
        mul_nonneg (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
          (pow_nonneg (zero_le_one.trans ht) _)
      exact hi.trans ((mul_le_mul hBM hraw (norm_nonneg _) (zero_le_one.trans hM)).trans_eq
        (by rw [pow_two]; ring))
  | angle w =>
      cases w
      have hi := n04PositiveGeometry_fiberInverse_space_one_norm hf hg hfg B hB
        (StateAngleWord.angle .nil).isState rfl
      have hsq : M ≤ M ^ 2 := by nlinarith
      simpa only [StateAngleWord.stateArity, StateAngleWord.angleArity,
        parameterHeightWeight, if_pos rfl, ite_true, one_mul, mul_one,
        Nat.mul_zero, Nat.add_zero, Nat.sub_self, pow_zero] using
          (hi.trans hBM).trans hsq

/-- The envelope is chosen before the common material bound, height,
scale, state-prefix size, actual forward family and actual inverse.
No inverse-jet estimate occurs among its hypotheses. -/
theorem n04PositiveGeometry_mixedInverse_polynomial_envelope (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ d : ℕ, N04PositiveGeometryMixedInverseEnvelope P V n A d := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨1, le_rfl, 0, fun hn => (Nat.not_lt_zero _ hn).elim⟩
    by_cases hn1 : n = 1
    · subst n
      exact ⟨1, le_rfl, 2, mixedInverseEnvelope_one P V⟩
    have hn2 : 2 ≤ n := by omega
    let A₀ : Fin n → ℝ := fun j => (ih j j.isLt).choose
    let d₀ : Fin n → ℕ := fun j => (ih j j.isLt).choose_spec.2.choose
    have hA₀ (j : Fin n) : 1 ≤ A₀ j := (ih j j.isLt).choose_spec.1
    have hprevious (j : Fin n) : N04PositiveGeometryMixedInverseEnvelope P V j (A₀ j) (d₀ j) :=
      (ih j j.isLt).choose_spec.2.choose_spec
    let A₁ : ℝ := 1 + ∑ j, A₀ j
    let d₁ : ℕ := ∑ j, d₀ j
    have hA₁ : 1 ≤ A₁ := le_add_of_nonneg_right
      (Finset.sum_nonneg (fun j _ => zero_le_one.trans (hA₀ j)))
    have hA₀₁ (j : Fin n) : A₀ j ≤ A₁ :=
      (Finset.single_le_sum (fun j _ => zero_le_one.trans (hA₀ j))
        (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)
    have hd₀₁ (j : Fin n) : d₀ j ≤ d₁ :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    let N : ℝ := ∑ c : OrderedFinpartition n, (Fintype.card (Finset (Fin c.length)) : ℝ)
    have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hA : 1 ≤ 1 + N * A₁ ^ n :=
      le_add_of_nonneg_right (mul_nonneg hN (pow_nonneg (zero_le_one.trans hA₁) _))
    refine ⟨1 + N * A₁ ^ n, hA, d₁ * n + n + 3, ?_⟩
    intro hn M H t hM hH hHM ht K C hC f g x hf hg hfg B hB hBM hforward w hw
    have hM₀ : 0 ≤ M := zero_le_one.trans hM
    have ht₀ : 0 ≤ t := zero_le_one.trans ht
    have hheight₀ : 0 ≤ parameterHeightWeight H w.stateArity := parameterHeightWeight_nonneg hH _
    have hinner (j : ℕ) (hj : 0 < j) (hjn : j < n) (u : StateAngleWord j) (hu : u.stateArity ≤ K) :
        ‖n04PositiveGeometry_projectedJet u.isState g x‖ ≤
          A₁ * M ^ d₁ * parameterHeightWeight H u.stateArity *
            t ^ (u.angleArity + C * u.stateArity - 1) := by
      let jj : Fin n := ⟨j, hjn⟩
      have hraw : ∀ a, 0 < a → a ≤ j → ∀ v : StateAngleWord a, v.stateArity ≤ K →
          ‖n04PositiveGeometry_projectedJet v.isState f (n04PositiveGeometry_fiberLift g x)‖ ≤
            M * parameterHeightWeight H v.stateArity *
              t ^ (v.angleArity + C * v.stateArity - 1) :=
        fun a ha haj v hv => hforward a ha (haj.trans hjn.le) v hv
      have hh := hprevious jj hj M H t hM hH hHM ht K C hC f g x
        hf hg hfg B hB hBM hraw u hu
      have hpoly : A₀ jj * M ^ d₀ jj ≤ A₁ * M ^ d₁ :=
        mul_le_mul (hA₀₁ jj) (pow_le_pow_right₀ hM (hd₀₁ jj))
          (pow_nonneg hM₀ _) (zero_le_one.trans hA₁)
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpoly (parameterHeightWeight_nonneg hH _))
        (pow_nonneg ht₀ _))
    let R : ℝ := A₁ ^ n * M ^ (d₁ * n + n + 2) * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + C * w.stateArity - 1)
    have hR : 0 ≤ R := mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hA₁) _) (pow_nonneg hM₀ _)) hheight₀)
      (pow_nonneg ht₀ _)
    have hterm (c : OrderedFinpartition n) (hc : 2 ≤ c.length) (s : Finset (Fin c.length)) :
        ‖n04PositiveGeometry_inverseSelectedTerm w.isState f g x c s‖ ≤ R := by
      by_cases hid : ∀ i ∈ s, (w.restrict (c.emb i)).stateArity = 1 ∧
          (w.restrict (c.emb i)).angleArity = 0
      · have hs : s.card ≤ w.stateArity := by
          calc
            _ = ∑ i ∈ s, (w.restrict (c.emb i)).stateArity := by
              symm
              calc
                _ = ∑ _i ∈ s, (1 : ℕ) :=
                  Finset.sum_congr rfl (fun i hi => (hid i hi).1)
                _ = s.card := by simp
            _ ≤ ∑ i, (w.restrict (c.emb i)).stateArity :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
                (fun _ _ _ => Nat.zero_le _)
            _ = _ := w.sum_restrict_stateArity c
        have hout := hforward c.length (by omega) c.length_le
          (StateAngleWord.ofBool (fun i => decide (i ∈ s)))
          (by simpa only [n04PositiveGeometry_selectedWord_stateArity] using hs.trans hw)
        have hout' : ‖n04PositiveGeometry_projectedJet (fun i => decide (i ∈ s)) f
            (n04PositiveGeometry_fiberLift g x)‖ ≤
            M * parameterHeightWeight H s.card *
              t ^ ((Finset.univ \ s).card + C * s.card - 1) := by
          simpa only [StateAngleWord.isState_ofBool,
            n04PositiveGeometry_selectedWord_stateArity,
            n04PositiveGeometry_selectedWord_angleArity] using hout
        apply n04PositiveGeometry_inverseSelectedTerm_weighted_bound hg w c hc s hid
          C d₁ hC hM hA₁ hH hHM ht hout'
        intro i _hi
        have hki : (w.restrict (c.emb i)).stateArity ≤ K :=
          ((Finset.single_le_sum
            (fun j _ => Nat.zero_le (w.restrict (c.emb j)).stateArity) (Finset.mem_univ i)).trans_eq
              (w.sum_restrict_stateArity c)).trans hw
        have hh := hinner (c.partSize i) (c.partSize_pos i)
          (flowJet_partition_partSize_lt c hc i) (w.restrict (c.emb i)) hki
        have he : (w.restrict (c.emb i)).isState = w.isState ∘ c.emb i := by
          funext j
          exact StateAngleWord.isState_restrict w (c.emb i) j
        simpa only [he] using hh
      · push_neg at hid
        obtain ⟨i, hi, hbad⟩ := hid
        rw [n04PositiveGeometry_inverseSelectedTerm_eq_zero hg w c s i hi
          (fun h => hbad h.1 h.2), norm_zero]
        exact hR
    have hsum : (∑ c : OrderedFinpartition n, if 2 ≤ c.length then
        ∑ s : Finset (Fin c.length),
          ‖n04PositiveGeometry_inverseSelectedTerm w.isState f g x c s‖ else 0) ≤ N * R := by
      calc
        _ ≤ ∑ c : OrderedFinpartition n, (Fintype.card (Finset (Fin c.length)) : ℝ) * R := by
          apply Finset.sum_le_sum
          intro c _
          by_cases hc : 2 ≤ c.length
          · rw [if_pos hc]
            exact (Finset.sum_le_sum (fun s _ => hterm c hc s)).trans_eq
              (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
          · rw [if_neg hc]
            exact mul_nonneg (Nat.cast_nonneg _) hR
        _ = _ := (Finset.sum_mul _ _ _).symm
    have hmain := n04PositiveGeometry_fiberInverse_projected_norm_terms
      hf hg hfg B hB hn2 w.isState
    have hsum₀ : 0 ≤ (∑ c : OrderedFinpartition n, if 2 ≤ c.length then
        ∑ s : Finset (Fin c.length),
          ‖n04PositiveGeometry_inverseSelectedTerm w.isState f g x c s‖ else 0) := by
      apply Finset.sum_nonneg
      intro c _
      split_ifs
      · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      · exact le_rfl
    calc
      _ ≤ M * (N * R) := hmain.trans (mul_le_mul hBM hsum hsum₀ hM₀)
      _ = (N * A₁ ^ n) * M ^ (d₁ * n + n + 3) * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + C * w.stateArity - 1) := by
        dsimp only [R]
        rw [show d₁ * n + n + 3 = (d₁ * n + n + 2) + 1 by omega, pow_succ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg hM₀ _))
          hheight₀) (pow_nonneg ht₀ _)

end ContinuousFlexibility.Analysis
