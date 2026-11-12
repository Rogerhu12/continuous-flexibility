import ContinuousFlexibility.Radial.MatchedOuterSelectedCut
import ContinuousFlexibility.Radial.OuterFrequencyScale
import ContinuousFlexibility.Radial.StandInBoundarySlope

/-!
# The actual selected boundary scale satisfies the uniform core bounds

The scale is the one used by the retained matching constructor,
j² w(p)/p at the preceding selected join.  The original cellwise profile
bounds, adjacent amplitude estimates and moving upper frequency cutoff
give both scale comparisons.  No operator estimate or scale comparison
is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- A profile value and its cell amplitude differ by at most a quadratic
exponential. The original accumulating-profile bounds supply both sides. -/
theorem matchedMorse_profile_amplitude_ratios
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    {m k : ℕ} (hm : 1 ≤ m) (hk : D.cellIndex k = m)
    {r : ℝ} (hr : r ∈ D.cells k) :
    D.w r / morseChainAmplitude T σ m ≤ exp ((2 * C 0) * (m : ℝ) ^ 2) ∧
      morseChainAmplitude T σ m / D.w r ≤ exp ((C 0 + 2) * (m : ℝ) ^ 2) := by
  rcases h.accumulating with ⟨_, _, hC, _, _, _, _, hlow, hjet, _, _, _, _⟩
  have hC₀ := hC 0
  have hlo : exp (-(m : ℝ) ^ (5 / 2 : ℝ) - C 0 * (m : ℝ) ^ 2) ≤ D.w r := by
    simpa only [hk] using hlow k r hr
  have hhi : D.w r ≤ C 0 *
      exp (-(m : ℝ) ^ (5 / 2 : ℝ) + C 0 * (m : ℝ) ^ 2) := by
    exact (le_abs_self _).trans (by simpa only [radialJet, hk] using hjet k r hr 0)
  have hw : 0 < D.w r := (exp_pos _).trans_le hlo
  have hμ : 0 < morseChainAmplitude T σ m := morseChainAmplitude_pos T σ hσ m
  have hloglo := log_le_log (exp_pos _) hlo
  rw [log_exp] at hloglo
  have hloghi := log_le_log hw hhi
  rw [log_mul hC₀.ne' (exp_ne_zero _), log_exp] at hloghi
  have hμlog := morseChainAmplitude_log_bounds T σ hσ m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hm', sq_nonneg ((m : ℝ) - 1)]
  have hCmul : C 0 ≤ C 0 * (m : ℝ) ^ 2 :=
    le_mul_of_one_le_right hC₀.le hmsq
  have hlogC := log_le_sub_one_of_pos hC₀
  have hlog2 : log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hmLog := mul_le_mul_of_nonneg_left hlog2
    (show 0 ≤ (m : ℝ) + 1 by positivity)
  have hmquad : (m : ℝ) + 1 ≤ 2 * (m : ℝ) ^ 2 := by
    nlinarith only [hm', sq_nonneg ((m : ℝ) - 1)]
  constructor
  · apply (log_le_log_iff (div_pos hw hμ) (exp_pos _)).mp
    rw [log_div hw.ne' hμ.ne', log_exp]
    nlinarith only [hloghi, hμlog.1, hlogC, hCmul]
  · apply (log_le_log_iff (div_pos hμ hw) (exp_pos _)).mp
    rw [log_div hμ.ne' hw.ne', log_exp]
    nlinarith only [hloglo, hμlog.2, hmLog, hmquad]

def matchedOuterSelectedScaleExponent (Cstar c a b : ℝ) : ℝ :=
  outerFrequencyExponent Cstar + 3 * c + 60 + a⁻¹ + b

theorem matchedOuterSelectedScaleExponent_pos {Cstar c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    0 < matchedOuterSelectedScaleExponent Cstar c a b := by
  dsimp only [matchedOuterSelectedScaleExponent, outerFrequencyExponent]
  positivity

/-- The same selected scale used by the actual matching shell meets the
two hypotheses of the uniform whole-core estimate. -/
theorem matchedMorse_selected_boundaryScale_bounds
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {Cstar : ℝ} (h : MorseChainRealization T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (right : Bool) {n j : ℕ} (hn : T.index < n) (hn₂ : 2 ≤ n)
    (hj : 2 ≤ j) (hupper : (j : ℝ) < radialFrequencyThreshold T Cstar n) :
    let p := r07PreviousCellJoin T right (n - 1)
    let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w p) p
    let L := matchedOuterSelectedScaleExponent Cstar (C 0) D.a D.b
    0 < lam ∧
      lam / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2) ∧
      morseChainAmplitude T σ n / lam ≤ exp (L * (n : ℝ) ^ 2) := by
  let p := r07PreviousCellJoin T right (n - 1)
  let μp := morseChainAmplitude T σ (n - 1)
  let μn := morseChainAmplitude T σ n
  let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w p) p
  let L := matchedOuterSelectedScaleExponent Cstar (C 0) D.a D.b
  change 0 < lam ∧ lam / μn ≤ exp (L * (n : ℝ) ^ 2) ∧
    μn / lam ≤ exp (L * (n : ℝ) ^ 2)
  have hn₁ : 1 ≤ n := by omega
  have hm₁ : 1 ≤ n - 1 := by omega
  have hm : T.index ≤ n - 1 := by omega
  obtain ⟨k, hk, hpCell⟩ := matchedMorse_previousJoin_cell h right (n - 1) hm
  have hpCore : p ∈ radialCore D := h.accumulating.2.1.2.2.2.1 k hpCell
  have hp : 0 < p := h.geometry.1.trans hpCore.1
  have hw : 0 < D.w p := h.geometry.2.2.2.2.1 p hpCore
  have hμp : 0 < μp := morseChainAmplitude_pos T σ hσ (n - 1)
  have hμn : 0 < μn := morseChainAmplitude_pos T σ hσ n
  have hC : 0 < C 0 := h.constants_pos 0
  have hb : 0 < D.b := h.geometry.1.trans h.geometry.2.1
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hjpos : 0 < (j : ℝ) := by linarith only [hj']
  have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith only [hj']
  have hlam : 0 < lam := standInBoundaryScale_pos (pow_pos hjpos 2) hw hp
  have hsq : ((n - 1 : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le n 1) 2
  have hpRatio := matchedMorse_profile_amplitude_ratios h hσ hm₁ hk hpCell
  have hprevn : μp / μn ≤ exp (27 * (n : ℝ) ^ 2) := by
    apply (div_le_iff₀ hμn).mpr
    simpa only [mul_comm] using
      morseAdjacentScale_amplitude_le_exp_sq T σ hσ hn₁ hn.le hm (Or.inr (by omega))
  have hnprev : μn / μp ≤ exp (27 * (n : ℝ) ^ 2) := by
    have hq : μn / μp ≤ exp (27 * ((n - 1 : ℕ) : ℝ) ^ 2) := by
      apply (div_le_iff₀ hμp).mpr
      simpa only [mul_comm] using
        morseAdjacentScale_amplitude_le_exp_sq T σ hσ hm₁ hm hn.le (Or.inl (by omega))
    exact hq.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq (by norm_num)))
  have hwp : D.w p / μp ≤ exp ((2 * C 0) * (n : ℝ) ^ 2) :=
    hpRatio.1.trans (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hsq (by positivity)))
  have hpw : μp / D.w p ≤ exp ((C 0 + 2) * (n : ℝ) ^ 2) :=
    hpRatio.2.trans (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hsq (by positivity)))
  have hwn : D.w p / μn ≤ exp ((2 * C 0 + 27) * (n : ℝ) ^ 2) := by
    calc
      _ = (D.w p / μp) * (μp / μn) := by field_simp [hμp.ne', hμn.ne'] <;> ring
      _ ≤ exp ((2 * C 0) * (n : ℝ) ^ 2) * exp (27 * (n : ℝ) ^ 2) :=
        mul_le_mul hwp hprevn (div_pos hμp hμn).le (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1 <;> ring
  have hnw : μn / D.w p ≤ exp ((C 0 + 29) * (n : ℝ) ^ 2) := by
    calc
      _ = (μn / μp) * (μp / D.w p) := by field_simp [hμp.ne', hw.ne'] <;> ring
      _ ≤ exp (27 * (n : ℝ) ^ 2) * exp ((C 0 + 2) * (n : ℝ) ^ 2) :=
        mul_le_mul hnprev hpw (div_pos hμp hw).le (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1 <;> ring
  have hjexp := outer_frequency_sq_le_exp_of_upper hn₁ (h.d_eq n hn.le) hupper
  have hpinv : p⁻¹ ≤ exp (D.a⁻¹ * (n : ℝ) ^ 2) :=
    (inv_anti₀ h.geometry.1 hpCore.1.le).trans
      (nonneg_le_exp_mul_nat_sq (inv_nonneg.mpr h.geometry.1.le) hn₁)
  have hpdiv : p / (j : ℝ) ^ 2 ≤ exp (D.b * (n : ℝ) ^ 2) :=
    ((div_le_self hp.le hj2).trans hpCore.2.le).trans
      (nonneg_le_exp_mul_nat_sq hb.le hn₁)
  refine ⟨hlam, ?_, ?_⟩
  · calc
      lam / μn = ((j : ℝ) ^ 2 * p⁻¹) * (D.w p / μn) := by
        dsimp only [lam, standInBoundaryScale]
        ring
      _ ≤ (exp (outerFrequencyExponent Cstar * (n : ℝ) ^ 2) *
          exp (D.a⁻¹ * (n : ℝ) ^ 2)) *
          exp ((2 * C 0 + 27) * (n : ℝ) ^ 2) :=
        mul_le_mul
          (mul_le_mul hjexp hpinv (inv_nonneg.mpr hp.le) (exp_pos _).le)
          hwn (div_pos hw hμn).le (mul_pos (exp_pos _) (exp_pos _)).le
      _ = exp ((outerFrequencyExponent Cstar + D.a⁻¹ + 2 * C 0 + 27) *
          (n : ℝ) ^ 2) := by
        rw [← exp_add, ← exp_add]
        congr 1 <;> ring
      _ ≤ exp (L * (n : ℝ) ^ 2) := by
        apply exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        dsimp only [L, matchedOuterSelectedScaleExponent]
        linarith only [hC, hb]
  · calc
      μn / lam = (p / (j : ℝ) ^ 2) * (μn / D.w p) := by
        dsimp only [lam, standInBoundaryScale]
        field_simp [hw.ne', hp.ne', hjpos.ne'] <;> ring
      _ ≤ exp (D.b * (n : ℝ) ^ 2) *
          exp ((C 0 + 29) * (n : ℝ) ^ 2) :=
        mul_le_mul hpdiv hnw (div_pos hμn hw).le (exp_pos _).le
      _ = exp ((D.b + C 0 + 29) * (n : ℝ) ^ 2) := by
        rw [← exp_add]
        congr 1 <;> ring
      _ ≤ exp (L * (n : ℝ) ^ 2) := by
        apply exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have haInv : 0 ≤ D.a⁻¹ := inv_nonneg.mpr h.geometry.1.le
        have hF : 0 ≤ outerFrequencyExponent Cstar := by
          dsimp only [outerFrequencyExponent]
          positivity
        dsimp only [L, matchedOuterSelectedScaleExponent]
        linarith only [hC, haInv, hF]

end ContinuousFlexibility.Radial
