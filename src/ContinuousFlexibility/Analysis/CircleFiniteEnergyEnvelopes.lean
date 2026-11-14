module

public import ContinuousFlexibility.Analysis.CircleEnergyEnvelope

/-!
# Finite sums of circle energy envelopes at different orders

Keeping each input order until after the sum over circles allows a later
interpolation estimate to use the actual derivative-order budget. No
summability assumption is made on the number of circle labels.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped ContDiff ENNReal BigOperators

variable {ι : Type*} [Fintype ι]

theorem finiteEnergyEnvelope_tsum
    (C : ι → ℝ) (E : ι → ℕ → ℝ≥0∞) :
    (∑' m, ∑ i, ENNReal.ofReal (C i ^ 2) * E i m) =
      ∑ i, ENNReal.ofReal (C i ^ 2) * ∑' m, E i m := by
  classical
  have h := ENNReal.tsum_comm
    (f := fun m i => ENNReal.ofReal (C i ^ 2) * E i m)
  simpa only [tsum_fintype, ENNReal.tsum_mul_left] using h

theorem finiteEnergyEnvelope_tsum_lt_top
    (C : ι → ℝ) (E : ι → ℕ → ℝ≥0∞)
    (hE : ∀ i, (∑' m, E i m) < ⊤) :
    (∑' m, ∑ i, ENNReal.ofReal (C i ^ 2) * E i m) < ⊤ := by
  rw [finiteEnergyEnvelope_tsum]
  exact ENNReal.sum_lt_top.mpr
    (fun i _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hE i))

/-- Each weighted summand is bounded by the square root of the common
finite energy envelope. -/
theorem finiteEnergyEnvelope_term_le
    (C : ι → ℝ) (E : ι → ℝ≥0∞)
    (hC : ∀ i, 0 ≤ C i) (hE : ∀ i, E i < ⊤) (i : ι) :
    C i * Real.sqrt (E i).toReal ≤
      Real.sqrt (∑ j, ENNReal.ofReal (C j ^ 2) * E j).toReal := by
  classical
  have hsum : (∑ j, ENNReal.ofReal (C j ^ 2) * E j) < ⊤ :=
    ENNReal.sum_lt_top.mpr
      (fun j _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hE j))
  have hsingle : ENNReal.ofReal (C i ^ 2) * E i ≤
      ∑ j, ENNReal.ofReal (C j ^ 2) * E j :=
    Finset.single_le_sum (f := fun j => ENNReal.ofReal (C j ^ 2) * E j)
      (fun j _ => zero_le) (Finset.mem_univ i)
  have h := Real.sqrt_le_sqrt (ENNReal.toReal_mono hsum.ne hsingle)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg (C i)),
    Real.sqrt_mul (sq_nonneg (C i)), Real.sqrt_sq (hC i)] using h

/-- The square root of a finite sum of weighted energies is bounded by
the sum of the separate norms, with all input orders preserved. -/
theorem finiteEnergyEnvelope_sqrt_le
    (C : ι → ℝ) (E : ι → ℝ≥0∞)
    (hC : ∀ i, 0 ≤ C i) (hE : ∀ i, E i < ⊤) :
    Real.sqrt (∑ i, ENNReal.ofReal (C i ^ 2) * E i).toReal ≤
      ∑ i, C i * Real.sqrt (E i).toReal := by
  classical
  have hreal : (∑ i, ENNReal.ofReal (C i ^ 2) * E i).toReal =
      ∑ i, (C i * Real.sqrt (E i).toReal) ^ 2 := by
    rw [ENNReal.toReal_sum (fun i _ =>
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hE i)).ne)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg (C i)),
      mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hnonneg (i : ι) : 0 ≤ C i * Real.sqrt (E i).toReal :=
    mul_nonneg (hC i) (Real.sqrt_nonneg _)
  rw [hreal]
  exact (Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg
    (fun i _ => hnonneg i))).trans_eq
      (Real.sqrt_sq (Finset.sum_nonneg (fun i _ => hnonneg i)))

/-- A finite family of summable envelopes may be kept at separate
orders through the complete circle norm estimate. -/
theorem circleNorm_le_of_finite_energy_envelopes
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ}
    (E : ι → ℕ → ℝ≥0∞) (C : ι → ℝ)
    (hE : ∀ i, (∑' m, E i m) < ⊤) (hC : ∀ i, 0 ≤ C i)
    (hv : ∀ m, ContDiff ℝ ∞ (v m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m))
    (hH : ∀ m, 0 ≤ T.H (T.sample m)) (s : ℕ)
    (hpoint : ∀ m b k, b + k ≤ s → ∀ θ,
      (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤ ∑ i, C i * Real.sqrt (E i m).toReal) :
    circleNorm T γ s v ≤
      Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) *
        (Real.pi * (Fintype.card ι : ℝ) ^ 2)) *
          ∑ i, C i * Real.sqrt (∑' m, E i m).toReal := by
  classical
  let total : ℕ → ℝ≥0∞ := fun m => ∑ i, ENNReal.ofReal (C i ^ 2) * E i m
  have htotal : (∑' m, total m) < ⊤ := finiteEnergyEnvelope_tsum_lt_top C E hE
  have hterm (i : ι) (m : ℕ) : E i m < ⊤ :=
    (ENNReal.le_tsum (f := E i) m).trans_lt (hE i)
  have hpoint' : ∀ m b k, b + k ≤ s → ∀ θ,
      (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤
      (Fintype.card ι : ℝ) * Real.sqrt (total m).toReal := by
    intro m b k horder θ
    apply (hpoint m b k horder θ).trans
    calc
      ∑ i, C i * Real.sqrt (E i m).toReal ≤
          ∑ _i : ι, Real.sqrt (total m).toReal :=
        Finset.sum_le_sum (fun i _ => finiteEnergyEnvelope_term_le C
          (fun j => E j m) hC (fun j => hterm j m) i)
      _ = (Fintype.card ι : ℝ) * Real.sqrt (total m).toReal := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnorm := circleNorm_le_of_envelope htotal hv hM hH s
    (Nat.cast_nonneg (Fintype.card ι)) hpoint'
  have hsqrt : Real.sqrt (∑' m, total m).toReal ≤
      ∑ i, C i * Real.sqrt (∑' m, E i m).toReal := by
    change Real.sqrt (∑' m, ∑ i, ENNReal.ofReal (C i ^ 2) * E i m).toReal ≤ _
    rw [finiteEnergyEnvelope_tsum]
    exact finiteEnergyEnvelope_sqrt_le C (fun i => ∑' m, E i m) hC hE
  exact hnorm.trans (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _))

/-- In the common case of actual circle energies the right hand side
contains precisely the separate physical input norms. -/
theorem circleNorm_le_of_finite_component_envelopes
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ}
    (u : ι → ℕ → ℝ → ℝ) (order : ι → ℕ) (C : ι → ℝ)
    (hu : ∀ i, CircleMember T γ (u i)) (hC : ∀ i, 0 ≤ C i)
    (hv : ∀ m, ContDiff ℝ ∞ (v m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m))
    (hH : ∀ m, 0 ≤ T.H (T.sample m)) (s : ℕ)
    (hpoint : ∀ m b k, b + k ≤ s → ∀ θ,
      (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤
      ∑ i, C i * Real.sqrt (circleComponentEnergy T γ (order i) (u i) m).toReal) :
    circleNorm T γ s v ≤
      Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) *
        (Real.pi * (Fintype.card ι : ℝ) ^ 2)) *
          ∑ i, C i * circleNorm T γ (order i) (u i) :=
  circleNorm_le_of_finite_energy_envelopes
    (fun i => circleComponentEnergy T γ (order i) (u i)) C
    (fun i => (hu i).2.2 (order i)) hC hv hM hH s hpoint

end ContinuousFlexibility.Statements
