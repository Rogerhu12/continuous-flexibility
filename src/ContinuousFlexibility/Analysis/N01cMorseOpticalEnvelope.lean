module

public import ContinuousFlexibility.Analysis.N01cMorseOpticalLowerBound

/-!
# One coefficient envelope for the actual Morse optical lower bound

The explicit geometric coefficient is bounded below by one negative power
of the reference envelope. The constant is chosen before the side and the
cell index. No optical or nonlinear estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Real Set
open ContinuousFlexibility.Radial

namespace MorseChainRealization

variable {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}

/-- The explicit whole-component coefficient has the required fixed
negative-envelope-power scale. -/
theorem opticalCoefficient_ge_radialE (h : MorseChainRealization T σ D C)
    (n : ℕ) (hn : T.index ≤ n) :
    (1372 * D.b ^ 3 * (9 : ℝ) ^ 9 * (3 : ℝ) ^ 6)⁻¹ *
        radialE n ^ (-6 : ℝ) ≤
      morseChainB T n / (1372 * D.b ^ 3 * morseChainA T n ^ 3) := by
  let A : ℝ := morseChainA T n
  let B : ℝ := morseChainB T n
  have hb : 0 < D.b := h.geometry.1.trans h.geometry.2.1
  have hd1 : (1 : ℝ) ≤ T.d n :=
    (one_le_exp_iff.mpr (sq_nonneg (n : ℝ))).trans (h.1 n hn).1
  have hBA : A ^ 9 / (9 : ℝ) ^ 9 ≤ B := (morseChainB_A_bounds T n hd1).1
  have hAlower : exp (-(n : ℝ) ^ 2) / 3 ≤ A :=
    (morseChainA_exp_bounds T n (h.d_eq n hn)).1
  have hA : 0 < A := (div_pos (exp_pos _) (by norm_num)).trans_le hAlower
  have hpow : (exp (-(n : ℝ) ^ 2) / 3) ^ 6 ≤ A ^ 6 :=
    pow_le_pow_left₀ (by positivity) hAlower 6
  have hE : radialE n ^ (-6 : ℝ) ≤ exp (-(n : ℝ) ^ 2) ^ 6 := by
    rw [radialE, ← exp_mul, ← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    have hQ := radial_nat_sq_le_Q n
    nlinarith only [hQ]
  have hscale : radialE n ^ (-6 : ℝ) / (3 : ℝ) ^ 6 ≤ A ^ 6 := by
    calc
      radialE n ^ (-6 : ℝ) / (3 : ℝ) ^ 6 ≤
          exp (-(n : ℝ) ^ 2) ^ 6 / (3 : ℝ) ^ 6 :=
        div_le_div_of_nonneg_right hE (by positivity)
      _ = (exp (-(n : ℝ) ^ 2) / 3) ^ 6 := (div_pow _ _ _).symm
      _ ≤ A ^ 6 := hpow
  have hfirst :
      (1372 * D.b ^ 3 * (9 : ℝ) ^ 9 * (3 : ℝ) ^ 6)⁻¹ *
          radialE n ^ (-6 : ℝ) ≤
        A ^ 6 / (1372 * D.b ^ 3 * (9 : ℝ) ^ 9) := by
    calc
      _ = (radialE n ^ (-6 : ℝ) / (3 : ℝ) ^ 6) /
          (1372 * D.b ^ 3 * (9 : ℝ) ^ 9) := by field_simp [hb.ne']
      _ ≤ _ := div_le_div_of_nonneg_right hscale (by positivity)
  apply hfirst.trans
  change A ^ 6 / (1372 * D.b ^ 3 * (9 : ℝ) ^ 9) ≤
    B / (1372 * D.b ^ 3 * A ^ 3)
  apply (le_div_iff₀ (by positivity : 0 < 1372 * D.b ^ 3 * A ^ 3)).mpr
  calc
    (A ^ 6 / (1372 * D.b ^ 3 * (9 : ℝ) ^ 9)) *
        (1372 * D.b ^ 3 * A ^ 3) = A ^ 9 / (9 : ℝ) ^ 9 := by
      field_simp [hb.ne']
    _ ≤ B := hBA

/-- A common constant gives a negative-power optical lower bound on every
actual Morse component after index 100, simultaneously on both tails. -/
theorem exists_opticalRatio_radialE_lower_bound
    (h : MorseChainRealization T σ D C) :
    ∃ K : ℝ, 0 < K ∧ ∀ side : Bool, ∀ n : ℕ,
      T.index ≤ n → 100 ≤ n → ∀ r : ℝ,
      r ∈ Ioo
        (T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
        (T.radius side n (morseChainRightTurn T n)) →
      K⁻¹ * radialE n ^ (-K) *
        min (r - T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
          (T.radius side n (morseChainRightTurn T n) - r) ≤
        -deriv D.w r / (r * D.w r) := by
  let A : ℝ := 1372 * D.b ^ 3 * (9 : ℝ) ^ 9 * (3 : ℝ) ^ 6
  let K : ℝ := max 6 A
  have hb : 0 < D.b := h.geometry.1.trans h.geometry.2.1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hK : 0 < K := (by norm_num : (0 : ℝ) < 6).trans_le (le_max_left _ _)
  have h6K : (6 : ℝ) ≤ K := le_max_left _ _
  have hAK : A ≤ K := le_max_right _ _
  refine ⟨K, hK, fun side n hn h100 r hr => ?_⟩
  have hE : 1 ≤ radialE n := one_le_exp_iff.mpr
    ((sq_nonneg (n : ℝ)).trans (radial_nat_sq_le_Q n))
  have hinv : K⁻¹ ≤ A⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hA hAK
  have hpower : radialE n ^ (-K) ≤ radialE n ^ (-6 : ℝ) :=
    rpow_le_rpow_of_exponent_le hE (neg_le_neg h6K)
  have hcoeff : K⁻¹ * radialE n ^ (-K) ≤
      morseChainB T n / (1372 * D.b ^ 3 * morseChainA T n ^ 3) := by
    apply (mul_le_mul hinv hpower (rpow_nonneg (by positivity) _) (inv_nonneg.mpr hA.le)).trans
    exact h.opticalCoefficient_ge_radialE n hn
  have hδ : 0 ≤ min
      (r - T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
      (T.radius side n (morseChainRightTurn T n) - r) :=
    le_min (sub_nonneg.mpr hr.1.le) (sub_nonneg.mpr hr.2.le)
  exact (mul_le_mul_of_nonneg_right hcoeff hδ).trans
    (h.opticalRatio_lower_bound_on_component side n hn h100 r hr)

end MorseChainRealization

end ContinuousFlexibility.Statements
