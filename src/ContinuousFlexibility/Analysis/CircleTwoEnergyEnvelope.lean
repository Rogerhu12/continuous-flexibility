module

public import ContinuousFlexibility.Analysis.CircleEnergyPointwiseBounds

/-!
# Two summable envelopes for one weighted circle jet

The two input energies retain their own derivative orders through the
sum over components. A numerical square estimate and the actual circle
L2 integral give the joint norm bound without a summable scalar majorant
for the component labels.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped ENNReal ContDiff BigOperators

theorem circleWeightedJetEnergy_le_two_envelopes
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ}
    {E F : ℕ → ℝ≥0∞} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : (∑' m, E m) < ⊤) (hF : (∑' m, F m) < ⊤)
    (hv : ∀ m, ContDiff ℝ ∞ (v m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (b c : ℕ)
    (hpoint : ∀ m θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤
      A * Real.sqrt (E m).toReal + B * Real.sqrt (F m).toReal) :
    (∑' m : ℕ, ENNReal.ofReal
      ((T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv b (v m)) 2 angleMeasure ^ 2) ≤
      ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (A ^ 2) * ∑' m, E m +
          ENNReal.ofReal (B ^ 2) * ∑' m, F m) := by
  have htwoPi : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
  have hterm (m : ℕ) :
      ENNReal.ofReal ((T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) ^ 2) *
          eLpNorm (iteratedDeriv b (v m)) 2 angleMeasure ^ 2 ≤
      ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (A ^ 2) * E m + ENNReal.ofReal (B ^ 2) * F m) := by
    have hEm : E m < ⊤ := (ENNReal.le_tsum (f := E) m).trans_lt hE
    have hFm : F m < ⊤ := (ENNReal.le_tsum (f := F) m).trans_lt hF
    have hJ := (hv m).continuous_iteratedDeriv b (by simp)
    have hJfin := (memLp_angleMeasure_of_continuous hJ).eLpNorm_lt_top
    have hl :
        ENNReal.ofReal ((T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) ^ 2) *
          eLpNorm (iteratedDeriv b (v m)) 2 angleMeasure ^ 2 < ⊤ := by
      apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      rw [pow_two]
      exact ENNReal.mul_lt_top hJfin hJfin
    have hAE : ENNReal.ofReal (A ^ 2) * E m < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEm
    have hBF : ENNReal.ofReal (B ^ 2) * F m < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFm
    have hr : ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (A ^ 2) * E m + ENNReal.ofReal (B ^ 2) * F m) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hAE, hBF⟩)
    have hK : 0 ≤ A * Real.sqrt (E m).toReal + B * Real.sqrt (F m).toReal :=
      add_nonneg (mul_nonneg hA (Real.sqrt_nonneg _))
        (mul_nonneg hB (Real.sqrt_nonneg _))
    have hreal := circleWeighted_L2_square_le_of_bound hK
      (show (0 : ℝ) ≤ 1 by norm_num) hJ
      (fun θ => by simpa only [Real.sqrt_one, mul_one] using hpoint m θ)
      (hM m) (hH m)
    simp only [mul_one] at hreal
    have hsq :
        (A * Real.sqrt (E m).toReal + B * Real.sqrt (F m).toReal) ^ 2 ≤
        2 * (A ^ 2 * (E m).toReal + B ^ 2 * (F m).toReal) := by
      have hn :
          (A * Real.sqrt (E m).toReal + B * Real.sqrt (F m).toReal) ^ 2 ≤
          2 * ((A * Real.sqrt (E m).toReal) ^ 2 +
            (B * Real.sqrt (F m).toReal) ^ 2) := by
        nlinarith only [sq_nonneg
          (A * Real.sqrt (E m).toReal - B * Real.sqrt (F m).toReal)]
      simpa only [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg] using hn
    have hbound := hreal.trans (mul_le_mul_of_nonneg_left hsq Real.pi_pos.le)
    apply (ENNReal.toReal_le_toReal hl.ne hr.ne).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal htwoPi,
      ENNReal.toReal_add hAE.ne hBF.ne]
    exact hbound.trans_eq (by ring)
  calc
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (A ^ 2) * E m + ENNReal.ofReal (B ^ 2) * F m) :=
      ENNReal.tsum_le_tsum hterm
    _ = _ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_add,
        ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

theorem circleWeightedJetNorm_le_two_envelopes
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ}
    {E F : ℕ → ℝ≥0∞} {A B U V : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hE : (∑' m, E m) ≤ ENNReal.ofReal (U ^ 2))
    (hF : (∑' m, F m) ≤ ENNReal.ofReal (V ^ 2))
    (hv : ∀ m, ContDiff ℝ ∞ (v m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (b c : ℕ)
    (hpoint : ∀ m θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤
      A * Real.sqrt (E m).toReal + B * Real.sqrt (F m).toReal) :
    Real.sqrt
      (∑' m : ℕ, ENNReal.ofReal
        ((T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) ^ 2) *
          eLpNorm (iteratedDeriv b (v m)) 2 angleMeasure ^ 2).toReal ≤
      Real.sqrt (2 * Real.pi) * (A * U + B * V) := by
  have htwoPi : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
  have henergy :=
    circleWeightedJetEnergy_le_two_envelopes hA hB
      (hE.trans_lt ENNReal.ofReal_lt_top) (hF.trans_lt ENNReal.ofReal_lt_top)
      hv hM hH b c hpoint
  have htotal :
      (∑' m : ℕ, ENNReal.ofReal
        ((T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) ^ 2) *
          eLpNorm (iteratedDeriv b (v m)) 2 angleMeasure ^ 2) ≤
      ENNReal.ofReal (2 * Real.pi * ((A * U) ^ 2 + (B * V) ^ 2)) := by
    refine henergy.trans ?_
    calc
      _ ≤ ENNReal.ofReal (2 * Real.pi) *
          (ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (U ^ 2) +
            ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (V ^ 2)) :=
        by gcongr <;> assumption
      _ = _ := by
        rw [ENNReal.ofReal_mul htwoPi,
          ENNReal.ofReal_add (sq_nonneg (A * U)) (sq_nonneg (B * V)),
          mul_pow, mul_pow, ENNReal.ofReal_mul (sq_nonneg A),
          ENNReal.ofReal_mul (sq_nonneg B)]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htotal
  rw [ENNReal.toReal_ofReal
    (mul_nonneg htwoPi (add_nonneg (sq_nonneg _) (sq_nonneg _)))] at hreal
  have hsum : Real.sqrt ((A * U) ^ 2 + (B * V) ^ 2) ≤ A * U + B * V := by
    apply (Real.sqrt_le_sqrt (show (A * U) ^ 2 + (B * V) ^ 2 ≤
      (A * U + B * V) ^ 2 by
        nlinarith only [mul_nonneg (mul_nonneg hA hU) (mul_nonneg hB hV)])).trans_eq
    exact Real.sqrt_sq (add_nonneg (mul_nonneg hA hU) (mul_nonneg hB hV))
  calc
    _ ≤ Real.sqrt (2 * Real.pi * ((A * U) ^ 2 + (B * V) ^ 2)) :=
      Real.sqrt_le_sqrt hreal
    _ = Real.sqrt (2 * Real.pi) * Real.sqrt ((A * U) ^ 2 + (B * V) ^ 2) :=
      Real.sqrt_mul htwoPi _
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)

end ContinuousFlexibility.Statements
