import ContinuousFlexibility.Radial.OuterCoreIntervals

/-!
# The height scale of the transition-core Hilbert mass

The estimates use the actual cell charts and actual connector profile.
Only the previously proved Morse cell and adjacent-height estimates
enter the explicit bound.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

/-- The exact coefficient bound before the fixed constants and adjacent
height ratio are absorbed into `exp (C n²)`. -/
theorem morseOuterCore_mass_le_coefficients {T : MorseChainData} {σ : ℕ → ℝ}
    {D₀ D : ReferenceData} {C : ℕ → ℝ} {K : ℝ}
    (h₀ : MorseChainRealization T (fun _ => 1) D₀ C)
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K)
    (side : Bool) (n : ℕ) (hn : T.index < n) :
    let p := if side then n - 1 else n
    radialHilbertIntervalMass D (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n) ≤
      (12 / D.a ^ 8) *
        (morseChainAmplitude T σ n * K * (morseChainA T n ^ 2 + morseChainA T n ^ 6) +
          (C 0 * K * D₀.b ^ 6 * exp 300) * morseChainAmplitude T σ p * morseChainA T p ^ 6) := by
  have hn₀ : T.index ≤ n - 1 := by omega
  have hn₁ : n - 1 + 1 = n := by omega
  have hs (i k : ℕ) (hi : T.index ≤ i) (hk : T.index ≤ k)
      (hik : k = i + 1 ∨ i = k + 1) :=
    morseAdjacentScale_factors_bound T σ hσ hi hk hik (h.d_eq i hi) (h.d_eq k hk)
  have hj := morseRealizedJoin_bounds h₀ hcell hσ h hs side (n - 1) hn₀
  dsimp only at hj
  simp only [hn₁] at hj
  have hmass := (morseRealized_join_hilbert_mass_le h side (n - 1) hn₀).trans
    (mul_le_mul_of_nonneg_left hj.1 (by positivity : (0 : ℝ) ≤ 12 / D.a ^ 8))
  rw [morseOuterCore_mass_eq h side n hn]
  calc
    _ ≤ (12 / D.a ^ 8) * morseChainAmplitude T σ n * K *
          (morseChainA T n ^ 2 + morseChainA T n ^ 6) +
        (12 / D.a ^ 8) * ((C 0 * K * D₀.b ^ 6 * exp 300) *
          morseChainAmplitude T σ (if side then n - 1 else n) *
          morseChainA T (if side then n - 1 else n) ^ 6) :=
      add_le_add (morseRealized_cell_hilbert_mass_le h hσ hcell side n hn.le) hmass
    _ = _ := by ring

theorem morseChainA_le_nine (T : MorseChainData) (n : ℕ)
    (hd : T.d n = morseChainInteger n) : morseChainA T n ≤ 9 :=
  (morseChainA_exp_bounds T n hd).2.trans
    (mul_le_of_le_one_right (by norm_num)
      (exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))))

/-- Adjacent amplitudes cost at most a quadratic exponential, uniformly
over all allowed height choices. -/
theorem morseAdjacentScale_amplitude_le_exp_sq
    (T : MorseChainData) (σ : ℕ → ℝ) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    {n m : ℕ} (hn : 1 ≤ n) (hNn : T.index ≤ n) (hNm : T.index ≤ m)
    (hadj : m = n + 1 ∨ n = m + 1) :
    morseChainAmplitude T σ m ≤ morseChainAmplitude T σ n * exp (27 * (n : ℝ) ^ 2) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hquad : (n : ℝ) ^ 2 + 25 * (n : ℝ) + 1 ≤ 27 * (n : ℝ) ^ 2 := by
    nlinarith only [hn', sq_nonneg ((n : ℝ) - 1)]
  have hlog := (morseAdjacentScale_amplitude_log_bound T σ hσ hNn hNm hadj).trans hquad
  have hp : 0 < morseChainAmplitude T σ m / morseChainAmplitude T σ n :=
    div_pos (morseChainAmplitude_pos T σ hσ m) (morseChainAmplitude_pos T σ hσ n)
  have hratio : morseChainAmplitude T σ m / morseChainAmplitude T σ n ≤
      exp (27 * (n : ℝ) ^ 2) := by
    simpa only [exp_log hp] using exp_le_exp.mpr hlog
  have hmul := (div_le_iff₀ (morseChainAmplitude_pos T σ hσ n)).mp hratio
  exact hmul.trans_eq (mul_comm _ _)

/-- A fixed explicit constant times `λ_n exp(27 n²)` bounds the actual
core mass.  The explicit coefficient is independent of the frequency. -/
theorem morseOuterCore_mass_le_height_exp {T : MorseChainData} {σ : ℕ → ℝ}
    {D₀ D : ReferenceData} {C : ℕ → ℝ} {K : ℝ}
    (h₀ : MorseChainRealization T (fun _ => 1) D₀ C)
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K)
    (side : Bool) (n : ℕ) (hn : T.index < n) :
    radialHilbertIntervalMass D (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n) ≤
      ((12 / D.a ^ 8) *
        (K * (9 ^ 2 + 9 ^ 6) + (C 0 * K * D₀.b ^ 6 * exp 300) * 9 ^ 6)) *
          morseChainAmplitude T σ n * exp (27 * (n : ℝ) ^ 2) := by
  let p := if side then n - 1 else n
  let J := C 0 * K * D₀.b ^ 6 * exp 300
  let E := exp (27 * (n : ℝ) ^ 2)
  have hK : 0 ≤ K := hcell.pos.le
  have hnp : T.index ≤ p := by dsimp only [p]; split <;> omega
  have hn1 : 1 ≤ n := by omega
  have hA₀ : 0 ≤ morseChainA T n := by
    have hd := h.retained_data side n hn.le
    exact ((mul_pos (by norm_num) hd.1).trans hd.2.1).le
  have hAp₀ : 0 ≤ morseChainA T p := by
    have hd := h.retained_data side p hnp
    exact ((mul_pos (by norm_num) hd.1).trans hd.2.1).le
  have hA : morseChainA T n ≤ 9 := morseChainA_le_nine T n (h.d_eq n hn.le)
  have hAp : morseChainA T p ≤ 9 := morseChainA_le_nine T p (h.d_eq p hnp)
  have hE : 1 ≤ E := one_le_exp_iff.mpr (by positivity)
  have hlam : 0 ≤ morseChainAmplitude T σ n := (morseChainAmplitude_pos T σ hσ n).le
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact mul_nonneg (mul_nonneg (mul_nonneg (h.constants_pos 0).le hK)
      (by positivity : 0 ≤ D₀.b ^ 6)) (exp_pos _).le
  have hp : morseChainAmplitude T σ p ≤ morseChainAmplitude T σ n * E := by
    cases side with
    | false =>
        change morseChainAmplitude T σ n ≤ morseChainAmplitude T σ n * E
        exact le_mul_of_one_le_right hlam hE
    | true =>
        change morseChainAmplitude T σ (n - 1) ≤ morseChainAmplitude T σ n * E
        exact morseAdjacentScale_amplitude_le_exp_sq T σ hσ hn1 hn.le
          (by omega) (Or.inr (by omega))
  have hcellBound : morseChainAmplitude T σ n * K *
      (morseChainA T n ^ 2 + morseChainA T n ^ 6) ≤
      morseChainAmplitude T σ n * E * (K * (9 ^ 2 + 9 ^ 6)) := by
    have ha := add_le_add (pow_le_pow_left₀ hA₀ hA 2) (pow_le_pow_left₀ hA₀ hA 6)
    calc
      _ ≤ morseChainAmplitude T σ n * K * (9 ^ 2 + 9 ^ 6) :=
        mul_le_mul_of_nonneg_left ha (mul_nonneg hlam hcell.pos.le)
      _ ≤ (morseChainAmplitude T σ n * K * (9 ^ 2 + 9 ^ 6)) * E :=
        le_mul_of_one_le_right (by positivity) hE
      _ = _ := by ring
  have hjoinBound : J * morseChainAmplitude T σ p * morseChainA T p ^ 6 ≤
      morseChainAmplitude T σ n * E * (J * 9 ^ 6) := by
    calc
      _ ≤ (J * (morseChainAmplitude T σ n * E)) * 9 ^ 6 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp hJ)
          (pow_le_pow_left₀ hAp₀ hAp 6) (pow_nonneg hAp₀ 6)
          (mul_nonneg hJ (mul_nonneg hlam (exp_pos _).le))
      _ = _ := by ring
  calc
    _ ≤ (12 / D.a ^ 8) * (morseChainAmplitude T σ n * K *
          (morseChainA T n ^ 2 + morseChainA T n ^ 6) +
          J * morseChainAmplitude T σ p * morseChainA T p ^ 6) :=
      morseOuterCore_mass_le_coefficients h₀ h hσ hcell side n hn
    _ ≤ (12 / D.a ^ 8) * (morseChainAmplitude T σ n * E * (K * (9 ^ 2 + 9 ^ 6)) +
        morseChainAmplitude T σ n * E * (J * 9 ^ 6)) :=
      mul_le_mul_of_nonneg_left (add_le_add hcellBound hjoinBound) (by positivity)
    _ = _ := by dsimp only [J, E]; ring

/-- Fixed prefactors can be included in the quadratic exponential once
the cell index is positive. -/
theorem nonneg_le_exp_mul_nat_sq {M : ℝ} (hM : 0 ≤ M) {n : ℕ} (hn : 1 ≤ n) :
    M ≤ exp (M * (n : ℝ) ^ 2) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn', sq_nonneg ((n : ℝ) - 1)]
  calc
    M ≤ M * (n : ℝ) ^ 2 := le_mul_of_one_le_right hM hs
    _ ≤ M * (n : ℝ) ^ 2 + 1 := le_add_of_nonneg_right zero_le_one
    _ ≤ _ := add_one_le_exp _

/-- The manuscript's Hilbert-mass bound with the chosen state scale `scale`.
The only scale hypothesis is the permitted comparison with the actual
cell amplitude; the core-mass estimate is derived above. -/
theorem morseOuterCore_mass_le_state_scale {T : MorseChainData} {σ : ℕ → ℝ}
    {D₀ D : ReferenceData} {C : ℕ → ℝ} {K scale L : ℝ}
    (h₀ : MorseChainRealization T (fun _ => 1) D₀ C)
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K)
    (side : Bool) (n : ℕ) (hn : T.index < n) (hScalePos : 0 < scale)
    (hscale : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2)) :
    let M := (12 / D.a ^ 8) *
      (K * (9 ^ 2 + 9 ^ 6) + (C 0 * K * D₀.b ^ 6 * exp 300) * 9 ^ 6)
    radialHilbertIntervalMass D (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n) ≤
      scale * exp ((L + 27 + M) * (n : ℝ) ^ 2) := by
  let M := (12 / D.a ^ 8) *
    (K * (9 ^ 2 + 9 ^ 6) + (C 0 * K * D₀.b ^ 6 * exp 300) * 9 ^ 6)
  have hK : 0 ≤ K := hcell.pos.le
  have hC : 0 ≤ C 0 := (h.constants_pos 0).le
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hpref : M ≤ exp (M * (n : ℝ) ^ 2) := nonneg_le_exp_mul_nat_sq hM (by omega)
  have hlam : morseChainAmplitude T σ n ≤ scale * exp (L * (n : ℝ) ^ 2) := by
    exact ((div_le_iff₀ hScalePos).mp hscale).trans_eq (mul_comm _ _)
  calc
    _ ≤ M * morseChainAmplitude T σ n * exp (27 * (n : ℝ) ^ 2) :=
      morseOuterCore_mass_le_height_exp h₀ h hσ hcell side n hn
    _ ≤ (exp (M * (n : ℝ) ^ 2) * (scale * exp (L * (n : ℝ) ^ 2))) *
        exp (27 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hpref hlam (morseChainAmplitude_pos T σ hσ n).le (exp_pos _).le)
        (exp_pos _).le
    _ = scale * exp ((L + 27 + M) * (n : ℝ) ^ 2) := by
      rw [mul_left_comm (exp (M * (n : ℝ) ^ 2)) scale,
        mul_assoc, ← exp_add, ← exp_add]
      congr 2
      ring

end ContinuousFlexibility.Radial
