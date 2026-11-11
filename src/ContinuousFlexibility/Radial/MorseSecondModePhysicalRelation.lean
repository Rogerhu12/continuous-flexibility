import ContinuousFlexibility.Radial.MorseSecondModeDeepTail

/-!
# Physical growth for the actual second-mode Morse tail

The normalized logarithmic density and the original cell localization
satisfy the full physical relation. The cross products retain their
quadratic exponent, including the index shift on the left.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

theorem morseSecondMode_same_coefficient {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n : ℕ} (hn : T.index ≤ n) :
    exp (2 * (n : ℝ) ^ 2 - 16) ≤
      (morseChainAmplitude T σ n / morseChainAmplitude T σ n) *
        (morseChainA T n ^ 2 / morseChainA T n ^ 4) := by
  have hAlog := (abs_le.mp (morseChainA_log_error T n
    (morseSecondMode_chainInteger hreal hn))).2
  have hA := morseSecondMode_A_pos hreal hn
  have hlam := morseChainAmplitude_pos T σ hσ n
  have he : 2 * (n : ℝ) ^ 2 - 16 ≤ log ((morseChainA T n ^ 2)⁻¹) := by
    rw [log_inv, log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hAlog]
  have hh := exp_le_exp.mpr he
  rw [exp_log (by positivity : 0 < (morseChainA T n ^ 2)⁻¹)] at hh
  calc
    _ ≤ (morseChainA T n ^ 2)⁻¹ := hh
    _ = _ := by field_simp [hlam.ne', hA.ne'] <;> ring

theorem morseSecondMode_outward_coefficient {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) (right : Bool) {n : ℕ}
    (hn₁ : 1 ≤ n) (hn : T.index ≤ n) :
    exp (2 * (n : ℝ) ^ 2 -
        (10 * (n : ℝ) ^ (3 / 2 : ℝ) + 4 * (n : ℝ) + 75)) ≤
      (morseChainAmplitude T σ (n + 1) /
        morseChainAmplitude T σ (if right then n else n + 1)) *
        (morseChainA T (n + 1) ^ 2 /
          morseChainA T (if right then n else n + 1) ^ 4) := by
  have hn' : T.index ≤ n + 1 := by omega
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply le_trans _ (morseSecondMode_same_coefficient hreal hσ hn')
    apply exp_le_exp.mpr
    push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) n,
      Real.rpow_nonneg (Nat.cast_nonneg n) (3 / 2 : ℝ)]
  · simp only [↓reduceIte]
    exact morseSecondMode_adjacent_coefficient hreal hσ hn₁ hn hn' (Or.inl rfl)

theorem morseSecondMode_physicalGrowth {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hmass : MorseMassResistanceBounds T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {N : ℕ} (hN : T.index < N)
    (right : Bool) :
    ∃ B : ℝ, 0 < B ∧ ∀ n,
      exp (2 * ((N + n : ℕ) : ℝ) ^ 2 -
        B * (((N + n : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (N + n : ℕ))) ≤
        (morseSecondModeTail D T N right).Λ *
          tailMass (morseSecondModeTail D T N right) (n + 1) *
          tailResistance (morseSecondModeTail D T N right) n := by
  have hC : 0 < C 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hacc⟩ := hreal
    exact hacc.2.2.1 0
  let B : ℝ := 100 + 2 * |log (C 0)|
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro n
  let k : ℕ := N + n
  have hk : T.index ≤ k := by dsimp [k]; omega
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hke : T.index ≤ (if right then k else k + 1) := by
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hkm : T.index ≤ k + 1 := by omega
  have hsc := morseSecondMode_scalarBounds hreal hmass hσ right hke hkm
  have hcoef := morseSecondMode_outward_coefficient hreal hσ right hk1 hk
  have he : exp (2 * (k : ℝ) ^ 2 -
        B * ((k : ℝ) ^ (3 / 2 : ℝ) + (k : ℝ))) ≤
      exp (2 * (k : ℝ) ^ 2 -
        (10 * (k : ℝ) ^ (3 / 2 : ℝ) + 4 * (k : ℝ) + 75)) / (C 0) ^ 2 := by
    calc
      _ ≤ exp (2 * (k : ℝ) ^ 2 -
          (10 * (k : ℝ) ^ (3 / 2 : ℝ) + 4 * (k : ℝ) + 75) -
          log ((C 0) ^ 2)) := by
        apply exp_le_exp.mpr
        rw [log_pow]
        norm_num only [Nat.cast_ofNat]
        have hs := Real.rpow_nonneg (Nat.cast_nonneg k) (3 / 2 : ℝ)
        have ha := le_abs_self (log (C 0))
        have hm := mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ (k : ℝ) ^ (3 / 2 : ℝ) + (k : ℝ) by linarith only [hs, hkR])
          (abs_nonneg (log (C 0)))
        dsimp only [B]
        nlinarith only [hs, hkR, ha, hm]
      _ = _ := by rw [exp_sub, exp_log (sq_pos_of_pos hC)]
  have hcross := (he.trans (div_le_div_of_nonneg_right hcoef (sq_nonneg (C 0)))).trans
    hsc.2.2.2.2.1
  change exp (2 * ((N + n : ℕ) : ℝ) ^ 2 -
      B * (((N + n : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (N + n : ℕ))) ≤
    12 * tailMass (morseSecondModeTail D T N right) (n + 1) *
      tailResistance (morseSecondModeTail D T N right) n
  rw [mul_assoc, morseSecondMode_mass_gap_product hreal hN.le]
  dsimp only [k] at hcross
  simp only [Nat.add_assoc] at hcross ⊢
  have hepos := exp_pos (2 * ((N + n : ℕ) : ℝ) ^ 2 -
    B * (((N + n : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (N + n : ℕ)))
  nlinarith only [hcross, hepos]

/-- The full physical relation holds for both signed coordinates,
without replacing any original cell or endpoint data. -/
theorem morseSecondMode_physicalRelation {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hmass : MorseMassResistanceBounds T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {N : ℕ} (hN : T.index < N)
    (right : Bool) :
    TailPhysicalRelation D (morseSecondModeTail D T N right) right 2 N := by
  refine ⟨by norm_num [morseSecondModeTail], rfl, ?_,
    morseSecondMode_physicalLocalization hreal hN right,
    morseSecondMode_physicalGrowth hreal hmass hσ hN right⟩
  intro x hx
  have hr := morseSecondMode_radius_mem_core hreal hN right ⟨hx.1.le, hx.2⟩
  have hR := morseSecondMode_endpoint_pos (morseSecondMode_profileGeometry hreal) right
  refine ⟨hr, ?_⟩
  rw [show 2 * ((2 : ℕ) : ℝ) ^ 2 = ((8 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  cases right <;>
    simp only [morseSecondModeTail, morseSecondModeDensity, tailPhysicalRadius,
      Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at hR ⊢ <;>
    field_simp [hR.ne', exp_ne_zero] <;> ring

/-- Both endpoints admit arbitrarily deep data carrying all the scalar
and physical hypotheses of the concrete natural-line and flatness theorems. -/
theorem morseSecondMode_exists_physicalDeepTail {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hmass : MorseMassResistanceBounds T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) :
    ∃ N : ℕ, T.index < N ∧ ∀ M, N ≤ M → ∀ right : Bool,
      DeepTailHypotheses (morseSecondModeTail D T M right) ∧
      TailPhysicalRelation D (morseSecondModeTail D T M right) right 2 M := by
  obtain ⟨N, hN, hdeep⟩ := morseSecondMode_exists_deepHypotheses hreal hmass hσ
  exact ⟨N, hN, fun M hM right =>
    ⟨hdeep M hM right, morseSecondMode_physicalRelation hreal hmass hσ
      (hN.trans_le hM) right⟩⟩

end ContinuousFlexibility.Radial
