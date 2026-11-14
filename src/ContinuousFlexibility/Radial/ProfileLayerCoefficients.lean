module

public import ContinuousFlexibility.Radial.ProfileLayerGeometry
public import ContinuousFlexibility.Radial.ProfileLayerWeights
public import ContinuousFlexibility.Analysis.IntervalLayerCutoffDeriv

/-!
# Uniform coefficient bounds on endpoint layers

The profile bounds and finite index window put the coefficient, its
inverse, the angular potential and the first cutoff derivative below a
single `A * exp (T * radialQ n)`. This is the fixed coefficient cost in the
layer Caccioppoli estimate.
-/

@[expose] public section

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Radial

noncomputable section

private theorem profile_cell_jet_exp_bound {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) (s m : ℕ) {r : ℝ} (hr : r ∈ D.cells m) :
    |radialJet s D.w r| ≤ C s * exp (C s * radialQ (D.cellIndex m)) := by
  rcases h with ⟨_, _, hC, _, _, _, _, _, hjet, _⟩
  have hp := Real.rpow_nonneg (Nat.cast_nonneg (D.cellIndex m)) (5 / 2 : ℝ)
  have hq := mul_le_mul_of_nonneg_left (radial_nat_sq_le_Q (D.cellIndex m)) (hC s).le
  exact (hjet m r hr s).trans (mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (by nlinarith only [hp, hq])) (hC s).le)

private theorem profile_cell_energy_bounds {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) :
    ∃ A T : ℝ, 1 ≤ A ∧ 0 ≤ T ∧ ∀ m : ℕ, ∀ r ∈ D.cells m,
      (D.w r)⁻¹ ≤ A * exp (T * radialQ (D.cellIndex m)) ∧
      D.w r ≤ A * exp (T * radialQ (D.cellIndex m)) ∧
      |deriv D.w r / r| ≤ A * exp (T * radialQ (D.cellIndex m)) := by
  have ha : 0 < D.a := h.1.1
  have hC : ∀ s, 0 < C s := h.2.2.1
  let A : ℝ := 1 + C 0 + C 1 + C 1 / D.a
  let T : ℝ := C 0 + C 1 + 1
  have hdiv : 0 < C 1 / D.a := div_pos (hC 1) ha
  have hA : 1 ≤ A := by dsimp [A]; linarith [hC 0, hC 1, hdiv]
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  have hT : 0 ≤ T := by dsimp [T]; linarith [hC 0, hC 1]
  have hT₀ : C 0 ≤ T := by dsimp [T]; linarith [hC 1]
  have hT₁ : C 1 ≤ T := by dsimp [T]; linarith [hC 0]
  have hA₀' : C 0 ≤ A := by dsimp [A]; linarith [hC 1, hdiv]
  have hA₁' : C 1 / D.a ≤ A := by dsimp [A]; linarith [hC 0, hC 1]
  refine ⟨A, T, hA, hT, ?_⟩
  intro m r hr
  have hrI : r ∈ radialCore D := h.2.1.2.2.2.1 m hr
  have hr₀ : 0 < r := ha.trans hrI.1
  have hq := radialQ_nonneg (D.cellIndex m)
  have hc₀ : C 0 * exp (C 0 * radialQ (D.cellIndex m)) ≤
      A * exp (T * radialQ (D.cellIndex m)) :=
    mul_le_mul hA₀' (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hT₀ hq))
      (exp_pos _).le hA₀
  have hc₁ : (C 1 / D.a) * exp (C 1 * radialQ (D.cellIndex m)) ≤
      A * exp (T * radialQ (D.cellIndex m)) :=
    mul_le_mul hA₁' (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hT₁ hq))
      (exp_pos _).le hA₀
  have hinv : |(D.w r)⁻¹| ≤ C 0 * exp (C 0 * radialQ (D.cellIndex m)) := by
    have hi := h.2.2.2.2.2.2.2.2.2.1 m r hr 0
    simpa only [radialJet, radialE, ← exp_mul, mul_comm] using hi
  have hw : |D.w r| ≤ C 0 * exp (C 0 * radialQ (D.cellIndex m)) := by
    simpa only [radialJet] using profile_cell_jet_exp_bound h 0 m hr
  have hwd : |deriv D.w r| ≤ C 1 * exp (C 1 * radialQ (D.cellIndex m)) := by
    simpa only [radialJet] using profile_cell_jet_exp_bound h 1 m hr
  refine ⟨(le_abs_self _).trans (hinv.trans hc₀),
    (le_abs_self _).trans (hw.trans hc₀), ?_⟩
  rw [abs_div, abs_of_pos hr₀]
  calc
    |deriv D.w r| / r ≤ |deriv D.w r| / D.a :=
      div_le_div_of_nonneg_left (abs_nonneg _) ha hrI.1.le
    _ ≤ (C 1 * exp (C 1 * radialQ (D.cellIndex m))) / D.a :=
      div_le_div_of_nonneg_right hwd ha.le
    _ = (C 1 / D.a) * exp (C 1 * radialQ (D.cellIndex m)) := by ring
    _ ≤ A * exp (T * radialQ (D.cellIndex m)) := hc₁

private theorem profile_exists_cell {D : ReferenceData} (h : RadialPartition D)
    {r : ℝ} (hr : r ∈ radialCore D) : ∃ m, r ∈ D.cells m := by
  obtain ⟨m, hm⟩ : ∃ m, D.localizer m r ≠ 0 := by
    by_contra hh
    have hz (m : ℕ) : D.localizer m r = 0 := by
      by_contra hm
      exact hh ⟨m, hm⟩
    have hzero : (∑' m, D.localizer m r) = 0 := by simp only [hz, tsum_zero]
    exact zero_ne_one (hzero.symm.trans (h.2.2.2.2.1 r hr).2)
  exact ⟨m, h.2.2.1 m hm⟩

theorem profile_layer_coefficient_exp_bound {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) :
    ∃ A T : ℝ, 1 ≤ A ∧ 0 ≤ T ∧ ∀ n : ℕ, ∀ r ∈ profileEndpointLayer D (C 0) n,
      (D.w r)⁻¹ ≤ A * exp (T * radialQ n) ∧
      D.w r ≤ A * exp (T * radialQ n) ∧
      |deriv D.w r / r| ≤ A * exp (T * radialQ n) := by
  obtain ⟨A₀, T₀, hA₀, hT₀, hcell⟩ := profile_cell_energy_bounds h
  obtain ⟨N, hN⟩ := profileEndpointLayer_index_window h
  obtain ⟨B, hB, hBQ⟩ := radialSQ_sub_le_Q_of_index_window N
  let T : ℝ := T₀ * (B + 1)
  let A : ℝ := A₀ * exp T
  have hT : 0 ≤ T := mul_nonneg hT₀ (by linarith)
  have heT : 1 ≤ exp T := one_le_exp hT
  have hA : 1 ≤ A := by
    have hp := mul_le_mul hA₀ heT zero_le_one (zero_le_one.trans hA₀)
    simpa only [one_mul] using hp
  refine ⟨A, T, hA, hT, ?_⟩
  intro n r hr
  have hrI := profileEndpointLayer_subset_core (h.2.2.1 0) n hr
  obtain ⟨m, hm⟩ := profile_exists_cell h.2.1 hrI
  obtain ⟨hnm, hmn⟩ := hN n m r hr hm
  have hQ := (hBQ n (D.cellIndex m) hnm hmn).2
  have hQk : radialQ (D.cellIndex m) ≤ (B + 1) * (1 + radialQ n) := by
    linarith only [hQ, le_abs_self (radialQ (D.cellIndex m) - radialQ n)]
  have hprod := mul_le_mul_of_nonneg_left hQk hT₀
  have hexp : exp (T₀ * radialQ (D.cellIndex m)) ≤ exp T * exp (T * radialQ n) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    dsimp only [T]
    nlinarith only [hprod]
  have hbound : A₀ * exp (T₀ * radialQ (D.cellIndex m)) ≤ A * exp (T * radialQ n) := by
    have hh := mul_le_mul_of_nonneg_left hexp (zero_le_one.trans hA₀)
    dsimp only [A]
    nlinarith only [hh]
  obtain ⟨hi, hw, hc⟩ := hcell m r hm
  exact ⟨hi.trans hbound, hw.trans hbound, hc.trans hbound⟩

theorem profile_layer_cutoff_deriv_exp_bound (D : ReferenceData) {C : ℝ} (hC : 1 ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, ∀ r : ℝ,
      |deriv (profileLayerCutoff D C n) r| ≤ A * exp (2 * radialQ n) := by
  obtain ⟨A₀, hA₀, hder⟩ := exists_intervalLayerCutoff_deriv_bound
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  refine ⟨A₀ * C * exp 2, by positivity, ?_⟩
  intro n r
  change |deriv (intervalLayerCutoff D.a D.b (profileLayerLower C n)
    (profileLayerUpper C n)) r| ≤ (A₀ * C * exp 2) * exp (2 * radialQ n)
  have hlow := profileLayerLower_pos hC₀ n
  have hband := profileLayerLower_le_upper hC n
  have hd := hder D.a D.b (profileLayerLower C n) (profileLayerUpper C n) r hlow hband
  have he : A₀ / profileLayerLower C n = A₀ * C * exp (((n : ℝ) + 1) ^ 2) := by
    unfold profileLayerLower
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv, ← exp_neg, neg_neg]
    ring
  have hpoly : ((n : ℝ) + 1) ^ 2 ≤ 2 + 2 * radialQ n := by
    nlinarith only [radial_nat_sq_le_Q n, sq_nonneg ((n : ℝ) - 1)]
  calc
    _ ≤ A₀ / profileLayerLower C n := hd
    _ = A₀ * C * exp (((n : ℝ) + 1) ^ 2) := he
    _ ≤ A₀ * C * exp (2 + 2 * radialQ n) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr hpoly) (mul_pos hA₀ hC₀).le
    _ = (A₀ * C * exp 2) * exp (2 * radialQ n) := by rw [exp_add]; ring

/-- One frequency-independent bound controls every coefficient required
by the endpoint-layer energy estimate. -/
theorem profile_layer_energy_constants {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) (hC : 1 ≤ C 0) :
    ∃ A T : ℝ, 1 ≤ A ∧ 0 ≤ T ∧ ∀ n : ℕ,
      1 ≤ A * exp (T * radialQ n) ∧
      ∀ r ∈ profileEndpointLayer D (C 0) n,
        1 / (A * exp (T * radialQ n)) ≤ D.w r ∧
        D.w r ≤ A * exp (T * radialQ n) ∧
        |deriv D.w r / r| ≤ A * exp (T * radialQ n) ∧
        |deriv (profileLayerCutoff D (C 0) n) r| ≤ A * exp (T * radialQ n) := by
  obtain ⟨A₀, T₀, hA₀, hT₀, hc⟩ := profile_layer_coefficient_exp_bound h
  obtain ⟨A₁, hA₁, hd⟩ := profile_layer_cutoff_deriv_exp_bound D hC
  let A : ℝ := A₀ + A₁ + 1
  let T : ℝ := T₀ + 2
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hT : 0 ≤ T := by dsimp [T]; linarith
  refine ⟨A, T, hA, hT, ?_⟩
  intro n
  have hQ := radialQ_nonneg n
  have hK : 1 ≤ A * exp (T * radialQ n) := by
    have hh := mul_le_mul hA (one_le_exp (mul_nonneg hT hQ)) zero_le_one
      (zero_le_one.trans hA)
    simpa only [one_mul] using hh
  refine ⟨hK, ?_⟩
  intro r hr
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have h₀ : A₀ * exp (T₀ * radialQ n) ≤ A * exp (T * radialQ n) :=
    mul_le_mul (by dsimp [A]; linarith)
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by dsimp [T]; linarith) hQ))
      (exp_pos _).le hApos.le
  have h₁ : A₁ * exp (2 * radialQ n) ≤ A * exp (T * radialQ n) :=
    mul_le_mul (by dsimp [A]; linarith)
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by dsimp [T]; linarith) hQ))
      (exp_pos _).le hApos.le
  obtain ⟨hi, hw, hpot⟩ := hc n r hr
  have hwpos : 0 < D.w r :=
    h.1.2.2.2.2.1 r (profileEndpointLayer_subset_core (h.2.2.1 0) n hr)
  have hilow := mul_le_mul_of_nonneg_left (hi.trans h₀) hwpos.le
  rw [mul_inv_cancel₀ hwpos.ne'] at hilow
  exact ⟨(div_le_iff₀ (zero_lt_one.trans_le hK)).mpr hilow,
    hw.trans h₀, hpot.trans h₀, (hd n r).trans h₁⟩

end

end ContinuousFlexibility.Radial
