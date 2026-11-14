module

public import ContinuousFlexibility.Analysis.N04NegativeChartVariationStep
public import ContinuousFlexibility.Analysis.N01cMixedPowerBounds

/-!
# The retained weight in every actual variational forcing term

A selected state slot puts the weight in the original speed derivative.
If no state slot is selected, a positive lower flow variation supplies
the weight. A block at the current state order is exactly zero in the
canonical truncated forcing. Thus no current unknown is estimated on
the right side of its own variational equation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

private theorem constant_one_jet_le (x : Q) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun _ : Q => (1 : ℝ)) x‖ ≤ 1 := by
  cases j with
  | zero => simp only [norm_iteratedFDeriv_zero, norm_one, le_refl]
  | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, zero_le_one]

private theorem constant_zero_jet_le (x : Q) (j : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ‖iteratedFDeriv ℝ j (fun _ : Q => (0 : ℝ)) x‖ ≤ A := by
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero, norm_zero] using hA
  | succ j => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using hA

/-- The same original speed head and actual strict lower variations
automatically supply a marked factor. The height ceiling R enters only
the ordinary material coefficient, while the distinguished W survives. -/
theorem n04NegativeChart_actualForcing_marked_factors
    {G Θ : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower (univ : Set E) G) (hΘ : ContDiff ℝ ∞ Θ)
    {n : ℕ} (hn : 0 < n) (K D : ℕ) (γ : Q → E) (α : Q → ℝ)
    (v : Fin n → E) (t : ℝ) (x : Q)
    {W M R ρ : ℝ} (hW : 0 ≤ W) (hWR : W ≤ R)
    (hM : 1 ≤ M) (hR : 1 ≤ R) (hρ : 1 ≤ ρ)
    (hhead : ∀ d : FlowForcingChoice n, ∀ j, j ≤ K →
      ‖iteratedFDeriv ℝ j (fun y : Q =>
        canonicalFlowForcingFactors J hΘ (γ y) v t d 0 (α y)) x‖ ≤
          parameterHeightWeight W d.2.card * M * ρ ^ (D + j))
    (hlower : ∀ k, 0 < k → k < n → ∀ e : Fin k → Fin n, ∀ j, j ≤ K →
      ‖iteratedFDeriv ℝ j (fun y : Q =>
        flowParameterField Θ k (γ y) (v ∘ e) (t, α y)) x‖ ≤
          W * M * ρ ^ (D + j)) :
    ∀ d : FlowForcingChoice n, ∃ i₀ : Fin (d.1.length + 1),
      (∀ j, j ≤ K → ‖iteratedFDeriv ℝ j (fun y : Q =>
        canonicalFlowForcingFactors J hΘ (γ y) v t d i₀ (α y)) x‖ ≤
          W * (M * R) * ρ ^ (D + j)) ∧
      (∀ i, i ≠ i₀ → ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j (fun y : Q =>
        canonicalFlowForcingFactors J hΘ (γ y) v t d i (α y)) x‖ ≤
          (M * R) * ρ ^ (D + j)) := by
  classical
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hMR : M ≤ M * R := le_mul_of_one_le_right hM0 hR
  have hWM : W * M ≤ M * R := by
    simpa only [mul_comm W M] using mul_le_mul_of_nonneg_left hWR hM0
  have hWMR : W * M ≤ W * (M * R) := mul_le_mul_of_nonneg_left hMR hW
  have hMR1 : 1 ≤ M * R := one_le_mul_of_one_le_of_one_le hM hR
  intro d
  have hlow (i : Fin d.1.length) (hi : i ∉ d.2) (j : ℕ) (hj : j ≤ K) :
      ‖iteratedFDeriv ℝ j (fun y : Q =>
        canonicalFlowForcingFactors J hΘ (γ y) v t d i.succ (α y)) x‖ ≤
          W * M * ρ ^ (D + j) := by
    by_cases hk : d.1.partSize i < n
    · have he : (fun y : Q =>
          canonicalFlowForcingFactors J hΘ (γ y) v t d i.succ (α y)) =
          fun y => flowParameterField Θ (d.1.partSize i) (γ y)
            (v ∘ d.1.emb i) (t, α y) := by
        funext y
        simp only [canonicalFlowForcingFactors, flowForcingFactors, Fin.cons_succ,
          flowSelectedLowerFactor, if_neg hi, lowerStateVariation, dif_pos hk,
          canonicalFlowVariation, flowInitialSlice, flowParameterField]
      rw [he]
      exact hlower (d.1.partSize i) (d.1.partSize_pos i) hk (d.1.emb i) j hj
    · have he : (fun y : Q =>
          canonicalFlowForcingFactors J hΘ (γ y) v t d i.succ (α y)) =
          fun _ : Q => (0 : ℝ) := by
        funext y
        exact flowSelectedLowerFactor_eq_zero_of_large
          (fun k (_ : k < n) => canonicalFlowVariation
            (contDiff_flowInitialSlice hΘ (α y)) k)
          d.1 d.2 (γ y, t) v i hi (Nat.le_of_not_gt hk)
      rw [he]
      exact constant_zero_jet_le x j
        (mul_nonneg (mul_nonneg hW hM0) (pow_nonneg (zero_le_one.trans hρ) _))
  have hordinary (i : Fin (d.1.length + 1)) (j : ℕ) (hj : j ≤ K) :
      ‖iteratedFDeriv ℝ j (fun y : Q =>
        canonicalFlowForcingFactors J hΘ (γ y) v t d i (α y)) x‖ ≤
          (M * R) * ρ ^ (D + j) := by
    refine Fin.cases ?_ (fun a => ?_) i
    · have hweight : parameterHeightWeight W d.2.card ≤ R := by
        by_cases hc : d.2.card = 0
        · simpa only [parameterHeightWeight, if_pos hc] using hR
        · simpa only [parameterHeightWeight, if_neg hc] using hWR
      exact (hhead d j hj).trans (mul_le_mul_of_nonneg_right
        (by simpa only [mul_comm _ M] using mul_le_mul_of_nonneg_left hweight hM0)
        (pow_nonneg (zero_le_one.trans hρ) _))
    · by_cases ha : a ∈ d.2
      · have he : (fun y : Q =>
            canonicalFlowForcingFactors J hΘ (γ y) v t d a.succ (α y)) =
            fun _ : Q => (1 : ℝ) := by
          funext y
          simp only [canonicalFlowForcingFactors, flowForcingFactors, Fin.cons_succ,
            flowSelectedLowerFactor, if_pos ha]
        rw [he]
        exact (constant_one_jet_le x j).trans
          (one_le_mul_of_one_le_of_one_le hMR1 (one_le_pow₀ hρ))
      · exact (hlow a ha j hj).trans
          (mul_le_mul_of_nonneg_right hWM (pow_nonneg (zero_le_one.trans hρ) _))
  by_cases hs : d.2.Nonempty
  · refine ⟨0, ?_, fun i _ j hj => hordinary i j hj⟩
    intro j hj
    have hc : d.2.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr hs)
    have hh : ‖iteratedFDeriv ℝ j (fun y : Q =>
        canonicalFlowForcingFactors J hΘ (γ y) v t d 0 (α y)) x‖ ≤
        W * M * ρ ^ (D + j) := by
      simpa only [parameterHeightWeight, if_neg hc] using hhead d j hj
    exact hh.trans (mul_le_mul_of_nonneg_right hWMR
      (pow_nonneg (zero_le_one.trans hρ) _))
  · let i : Fin d.1.length := ⟨0, d.1.length_pos hn⟩
    have hi : i ∉ d.2 := fun h => hs ⟨i, h⟩
    refine ⟨i.succ, ?_, fun a _ j hj => hordinary a j hj⟩
    intro j hj
    exact (hlow i hi j hj).trans (mul_le_mul_of_nonneg_right hWMR
      (pow_nonneg (zero_le_one.trans hρ) _))

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_actualForcing_marked_factors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_actualForcing_marked_factors
