import ContinuousFlexibility.Analysis.N04NegativeChartSpeedSlots
import ContinuousFlexibility.Analysis.N04NegativeChartActualRootPrefix
import ContinuousFlexibility.Analysis.N04NegativeChartRootLowFlow

/-! The actual forcing heads inherit the physical root-field prefix.
Every extracted state direction is an original direction or zero. The
angular slots spend only their number in the spatial prefix. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

private theorem identityJet_inl {n : ℕ} (v : Fin n → P) :
    (flowParameterIdentityJet n (fun i => (v i, (0 : PolarPoint)))).1 =
      ((flowParameterIdentityJet n v).1, (0 : PolarPoint)) := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

private theorem forcing_stateArity {n : ℕ} (d : FlowForcingChoice n) :
    d.stateWord.stateArity = d.2.card := by
  classical
  simp [StateAngleWord.stateArity_eq_sum, FlowForcingChoice.stateWord]

/-- This is the head in the canonical variational equation of the same
flow. Its height factor is exactly the count of selected state slots. -/
theorem negativeChart_actual_forcing_head_prefix
    {G Θ : (P × PolarPoint) × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set (P × PolarPoint)) G)
    (hΘ : ContDiff ℝ ∞ Θ) (n K shift : ℕ) (v : Fin n → P)
    (p₀ p₁ : Seminorm ℝ P) {R M B H ρ : ℝ}
    (hR : 1 ≤ R) (hM : 0 ≤ M) (hB : 1 ≤ B) (hH : 0 ≤ H) (hρ : 1 ≤ ρ)
    (hv₀ : ∀ i, p₀ (v i) ≤ 1) (hv₁ : ∀ i, p₁ (v i) ≤ R)
    (t : ℝ) (q : N04FlowPoint)
    (hraw : ∀ k, k ≤ n → ∀ u : Fin k → P,
      (∀ i, p₀ (u i) ≤ 1) → (∀ i, p₁ (u i) ≤ R) →
      ∀ l, l ≤ K + n → ∀ θ,
        ‖iteratedFDeriv ℝ l (fun y : N04FlowPoint =>
          flowParameterField G k (0, y.1) (fun i => (u i, (0 : PolarPoint)))
            (t, y.2)) (q.1, θ)‖ ≤
          M * parameterHeightWeight H k * ρ ^ (l - 1 + shift * k))
    (hflow : ∀ j, 1 ≤ j → j ≤ K →
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint => Θ ((0, y.1), (t, y.2))) q‖ ≤
        B * ρ ^ (j - 1)) :
    ∀ d : FlowForcingChoice n, ∀ j, j ≤ K →
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        canonicalFlowForcingFactors J hΘ (0, y.1)
          (fun i => (v i, (0 : PolarPoint))) t d 0 y.2) q‖ ≤
        parameterHeightWeight H d.2.card *
          ((K.factorial : ℝ) * M * B ^ K) * ρ ^ ((shift + 1) * n + j) := by
  classical
  intro d j hj
  let a : Fin d.1.length → P := fun i =>
    (flowParameterIdentityJet (d.1.partSize i) (v ∘ d.1.emb i)).1
  let b : Fin d.1.length → Bool := fun i => decide (i ∈ d.2)
  let u := flowForcingStateDirections d (ContinuousLinearMap.id ℝ P) v
  have hu₀ : ∀ i, p₀ (u i) ≤ 1 :=
    flowForcingStateDirections_seminorm_le d (ContinuousLinearMap.id ℝ P) v p₀
      zero_le_one hv₀
  have hu₁ : ∀ i, p₁ (u i) ≤ R :=
    flowForcingStateDirections_seminorm_le d (ContinuousLinearMap.id ℝ P) v p₁
      (zero_le_one.trans hR) hv₁
  have hstate := flowForcingStateDirections_stateArity_le d
  have hcard := forcing_stateArity d
  have htotal := d.stateWord.arity_sum
  have hlen := d.1.length_le
  have hslots (l : ℕ) (hl : l ≤ K) :
      ‖iteratedFDeriv ℝ l (fun y : N04FlowPoint =>
        flowSpeedJointField J d.1.length (0, y.1)
          (fun i => if b i then ((a i, (0 : PolarPoint)), 0) else (0, 1)) (t, y.2))
          (q.1, Θ ((0, q.1), (t, q.2)))‖ ≤
        (M * parameterHeightWeight H d.2.card) * ρ ^ ((shift + 1) * n + l) := by
    have hs := negativeChart_speed_selected_spatialJet_le hG J b a t l
      (q.1, Θ ((0, q.1), (t, q.2)))
    have hb := hraw d.stateWord.stateArity hstate u hu₀ hu₁
      (l + d.stateWord.angleArity) (by omega) _
    have hs' :
        ‖iteratedFDeriv ℝ l (fun y : N04FlowPoint =>
          flowSpeedJointField J d.1.length (0, y.1)
            (fun i => if b i then ((a i, (0 : PolarPoint)), 0) else (0, 1)) (t, y.2))
            (q.1, Θ ((0, q.1), (t, q.2)))‖ ≤
          M * parameterHeightWeight H d.stateWord.stateArity *
            ρ ^ (l + d.stateWord.angleArity - 1 + shift * d.stateWord.stateArity) := by
      apply hs.trans
      simpa only [u, flowForcingStateDirections, ContinuousLinearMap.id_apply,
        FlowForcingChoice.stateWord, a, b] using hb
    rw [forcing_stateArity] at hs'
    apply hs'.trans
    apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ ?_)
      (mul_nonneg hM (parameterHeightWeight_nonneg hH _))
    have hmul := Nat.mul_le_mul_left shift hstate
    rw [hcard] at hmul
    rw [Nat.add_mul, one_mul]
    omega
  have he : (fun y : N04FlowPoint => canonicalFlowForcingFactors J hΘ (0, y.1)
      (fun i => (v i, (0 : PolarPoint))) t d 0 y.2) =
      fun y : N04FlowPoint => flowSpeedJointField J d.1.length (0, y.1)
        (fun i => if b i then ((a i, (0 : PolarPoint)), 0) else (0, 1))
        (t, Θ ((0, y.1), (t, y.2))) := by
    funext y
    simp only [canonicalFlowForcingFactors, flowForcingFactors, Fin.cons_zero,
      flowSelectedSpeedCoefficient, flowSpeedJointField, flowTrajectoryGraph, flowInitialSlice]
    congr 1
    funext i
    by_cases hi : i ∈ d.2 <;> simp [b, a, hi, Function.comp_def, identityJet_inl]
  rw [he]
  have hh := n04NegativeChart_speedJet_along_flow_weighted_prefix hG J hΘ
    (fun z : PolarPoint => ((0 : P), z)) (contDiff_const.prodMk contDiff_id)
    d.1.length K ((shift + 1) * n)
    (fun i => if b i then ((a i, (0 : PolarPoint)), 0) else (0, 1)) t q
    (mul_nonneg hM (parameterHeightWeight_nonneg hH _)) hB hρ hslots hflow j hj
  exact hh.trans_eq (by ring)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.negativeChart_actual_forcing_head_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.negativeChart_actual_forcing_head_prefix
