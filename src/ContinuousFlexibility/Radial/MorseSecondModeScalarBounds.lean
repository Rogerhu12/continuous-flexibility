module

public import ContinuousFlexibility.Radial.MorseSecondModeMassTransport
public import ContinuousFlexibility.Radial.MorseCellMassResistanceBounds

/-!
# Scalar bounds for a second-mode Morse tail

The actual mass/resistance estimates give the small-edge and large-product
quantities needed for the deep-tail hypotheses. The normalization of the
physical logarithmic coordinate cancels from every product.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- The integer in any realized chain is the canonical least nonsquare
integer, so the proved scale estimates apply to arbitrary realized data. -/
theorem morseSecondMode_chainInteger {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {n : ℕ} (hn : T.index ≤ n) :
    T.d n = morseChainInteger n := by
  obtain ⟨hlo, hns, hmin⟩ := h.1 n hn
  apply Nat.le_antisymm
  · apply le_of_not_gt
    intro hlt
    exact (morseChainInteger_spec n).2
      (hmin (morseChainInteger n) (morseChainInteger_spec n).1 hlt)
  · apply le_of_not_gt
    intro hlt
    exact hns (morseChainInteger_minimal n (T.d n) hlo hlt)

/-- Elementary algebra behind the deep-tail products and adjacent mass
comparisons; it uses no unproved analytic input. -/
theorem morseSecondMode_massBounds_algebra
    {lam lam' A A' C L μ μ' I ν R : ℝ}
    (hlam : 0 < lam) (hlam' : 0 < lam') (hA : 0 < A) (hA' : 0 < A')
    (hC : 0 < C) (hL : 0 ≤ L)
    (hμlo : lam * A ^ 2 / C ≤ μ) (hμhi : μ ≤ C * lam * A ^ 2)
    (hμ'lo : lam' * A' ^ 2 / C ≤ μ')
    (hI : I ≤ C / lam * L) (hν : ν ≤ C * lam * A ^ 6)
    (hRlo : lam⁻¹ * (A ^ 4)⁻¹ / C ≤ R)
    (hRhi : R ≤ C * lam⁻¹ * (A ^ 4)⁻¹) :
    0 < μ ∧ 0 < R ∧
      μ * I ≤ C ^ 2 * A ^ 2 * L ∧
      ν * R ≤ C ^ 2 * A ^ 2 ∧
      (lam' / lam) * (A' ^ 2 / A ^ 4) / C ^ 2 ≤ μ' * R ∧
      ν ≤ (C ^ 2 * (lam / lam') * (A ^ 6 / A' ^ 2)) * μ' := by
  have hμ : 0 < μ := (by positivity : 0 < lam * A ^ 2 / C).trans_le hμlo
  have hμ' : 0 < μ' := (by positivity : 0 < lam' * A' ^ 2 / C).trans_le hμ'lo
  have hR : 0 < R := (by positivity : 0 < lam⁻¹ * (A ^ 4)⁻¹ / C).trans_le hRlo
  refine ⟨hμ, hR, ?_, ?_, ?_, ?_⟩
  · calc
      μ * I ≤ μ * (C / lam * L) := mul_le_mul_of_nonneg_left hI hμ.le
      _ ≤ (C * lam * A ^ 2) * (C / lam * L) :=
        mul_le_mul_of_nonneg_right hμhi (by positivity)
      _ = _ := by field_simp [hlam.ne'] <;> ring
  · calc
      ν * R ≤ (C * lam * A ^ 6) * R := mul_le_mul_of_nonneg_right hν hR.le
      _ ≤ (C * lam * A ^ 6) * (C * lam⁻¹ * (A ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left hRhi (by positivity)
      _ = _ := by field_simp [hlam.ne', hA.ne'] <;> ring
  · calc
      (lam' / lam) * (A' ^ 2 / A ^ 4) / C ^ 2 =
          (lam' * A' ^ 2 / C) * (lam⁻¹ * (A ^ 4)⁻¹ / C) := by
        field_simp [hlam.ne', hA.ne', hC.ne']
        <;> ring
      _ ≤ μ' * R := mul_le_mul hμ'lo hRlo (by positivity) hμ'.le
  · have hcoef : 0 ≤ C ^ 2 * (lam / lam') * (A ^ 6 / A' ^ 2) := by positivity
    calc
      ν ≤ C * lam * A ^ 6 := hν
      _ = (C ^ 2 * (lam / lam') * (A ^ 6 / A' ^ 2)) *
          (lam' * A' ^ 2 / C) := by
        field_simp [hlam'.ne', hA'.ne', hC.ne']
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hμ'lo hcoef

/-- All four scalar bounds for arbitrary actual retained indices. The
second index is the mass index paired with the departure resistance. -/
theorem morseSecondMode_scalarBounds {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hmass : MorseMassResistanceBounds T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) (right : Bool)
    {n m : ℕ} (hn : T.index ≤ n) (hm : T.index ≤ m) :
    let An := morseChainA T n
    let Am := morseChainA T m
    let ln := morseChainAmplitude T σ n
    let lm := morseChainAmplitude T σ m
    0 < morseCellMass T D right n ∧ 0 < morseJoinResistance T D right n ∧
      morseCellMass T D right n * morseCellResistance T D right n ≤
        (C 0) ^ 2 * An ^ 2 * log (An / morseChainB T n) ∧
      morseJoinMass T D right n * morseJoinResistance T D right n ≤ (C 0) ^ 2 * An ^ 2 ∧
      (lm / ln) * (Am ^ 2 / An ^ 4) / (C 0) ^ 2 ≤
        morseCellMass T D right m * morseJoinResistance T D right n ∧
      morseJoinMass T D right n ≤
        ((C 0) ^ 2 * (ln / lm) * (An ^ 6 / Am ^ 2)) * morseCellMass T D right m := by
  obtain ⟨_, hgeometry, _, _, _, _, _, _, _, hacc⟩ := hreal
  have hAn : 0 < morseChainA T n := by
    have hB := (hgeometry right n hn).1
    have hAB := (hgeometry right n hn).2.1
    linarith
  have hAm : 0 < morseChainA T m := by
    have hB := (hgeometry right m hm).1
    have hAB := (hgeometry right m hm).2.1
    linarith
  have hC : 0 < C 0 := hacc.2.2.1 0
  have hL : 0 ≤ log (morseChainA T n / morseChainB T n) := by
    apply log_nonneg
    apply (le_div_iff₀ (hgeometry right n hn).1).mpr
    have hAB := (hgeometry right n hn).2.1
    have hB := (hgeometry right n hn).1
    nlinarith
  have hpow : morseChainA T n ^ (-4 : ℝ) = ((morseChainA T n) ^ 4)⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hAn.le, Real.rpow_natCast]
  obtain ⟨hμlo, hμhi, hI, hν, hRlo, hRhi⟩ := hmass right n hn
  have hμ'lo := (hmass right m hm).1
  rw [hpow] at hRlo hRhi
  exact morseSecondMode_massBounds_algebra (morseChainAmplitude_pos T σ hσ n)
    (morseChainAmplitude_pos T σ hσ m) hAn hAm hC hL
    hμlo hμhi hμ'lo hI hν hRlo hRhi

/-- The adjacent mass-resistance coefficient retains the precise
quadratic exponent needed for cubic attenuation of node values. -/
theorem morseSecondMode_adjacent_coefficient {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m : ℕ}
    (hn₁ : 1 ≤ n) (hn : T.index ≤ n) (hm : T.index ≤ m)
    (hadj : m = n + 1 ∨ n = m + 1) :
    exp (2 * (n : ℝ) ^ 2 -
        (10 * (n : ℝ) ^ (3 / 2 : ℝ) + 4 * (n : ℝ) + 75)) ≤
      (morseChainAmplitude T σ m / morseChainAmplitude T σ n) *
        (morseChainA T m ^ 2 / morseChainA T n ^ 4) := by
  have hlog := morseCell_cross_scale_log_error T σ hσ hn₁ hn hm hadj
    (morseSecondMode_chainInteger hreal hn) (morseSecondMode_chainInteger hreal hm)
    (sL := 1) (sR := 1) (by norm_num) (by norm_num) (by norm_num)
  simp only [div_self (one_ne_zero : (1 : ℝ) ≠ 0), one_pow, mul_one] at hlog
  have hlo := (abs_le.mp hlog.2).1
  have hexp := exp_le_exp.mpr
    (show 2 * (n : ℝ) ^ 2 -
      (10 * (n : ℝ) ^ (3 / 2 : ℝ) + 4 * (n : ℝ) + 75) ≤
      log ((morseChainAmplitude T σ m / morseChainAmplitude T σ n) *
        (morseChainA T m ^ 2 / morseChainA T n ^ 4)) by linarith only [hlo])
  rwa [exp_log hlog.1] at hexp

end ContinuousFlexibility.Radial
