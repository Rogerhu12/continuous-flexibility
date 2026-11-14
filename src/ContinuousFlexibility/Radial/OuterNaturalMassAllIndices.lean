module

public import ContinuousFlexibility.Radial.OuterNaturalMassScale

/-!
# The first-mass estimate at every positive transition index

The asymptotic small-gauge estimate leaves only finitely many frequency
bands. Each of those bands has a finite upper frequency, and the actual
annulus bounds its gauge ratio by b/a. The resulting finite maximum is
independent of the height ratios. Thus the constant below is chosen
before the profile and all height choices, and includes the initial band.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Two realizations of the same charts have the same radial endpoints,
because both endpoints are limits of the same actual chart sequence. -/
theorem morseChainRealization_endpoints_eq
    {T : MorseChainData} {σ₀ σ : ℕ → ℝ} {D₀ D : ReferenceData}
    {C₀ C : ℕ → ℝ}
    (h₀ : MorseChainRealization T σ₀ D₀ C₀)
    (h : MorseChainRealization T σ D C) :
    D.a = D₀.a ∧ D.b = D₀.b := by
  rcases h₀ with ⟨_, _, _, _, _, _, hlim₀, _⟩
  rcases h with ⟨_, _, _, _, _, _, hlim, _⟩
  constructor
  · simpa using tendsto_nhds_unique (hlim false).1 (hlim₀ false).1
  · simpa using tendsto_nhds_unique (hlim true).1 (hlim₀ true).1

/-- A finite upper frequency controls the gauge on the full annulus.
This bound applies even when the asymptotic condition j² A ≤ 1 fails. -/
theorem radialGauge_annulus_power_le {D : ReferenceData}
    (hD : RadialProfileGeometry D) (j : ℕ) {q entrance x : ℝ}
    (hj : (j : ℝ) ≤ q) (hentry : D.a ≤ entrance) (hx : x ∈ radialCore D) :
    (x / entrance) ^ (2 * j ^ 2) ≤ exp (2 * q ^ 2 * log (D.b / D.a)) := by
  have hepos : 0 < entrance := hD.1.trans_le hentry
  have hxpos : 0 < x := hD.1.trans hx.1
  have hratio : x / entrance ≤ D.b / D.a := calc
    _ ≤ x / D.a := div_le_div_of_nonneg_left hxpos.le hD.1 hentry
    _ ≤ D.b / D.a := div_le_div_of_nonneg_right hx.2.le hD.1.le
  have hlogratio : log (x / entrance) ≤ log (D.b / D.a) :=
    log_le_log (div_pos hxpos hepos) hratio
  have hlog : 0 ≤ log (D.b / D.a) := by
    apply log_nonneg
    apply (le_div_iff₀ hD.1).mpr
    simpa only [one_mul] using hD.2.1.le
  have hsq : (j : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg j) hj 2
  calc
    _ = exp ((((2 * j ^ 2 : ℕ) : ℝ)) * log (x / entrance)) := by
      rw [exp_nat_mul, exp_log (div_pos hxpos hepos)]
    _ ≤ _ := by
      apply exp_le_exp.mpr
      push_cast
      calc
        2 * (j : ℝ) ^ 2 * log (x / entrance) ≤
            2 * (j : ℝ) ^ 2 * log (D.b / D.a) :=
          mul_le_mul_of_nonneg_left hlogratio (by positivity)
        _ ≤ 2 * q ^ 2 * log (D.b / D.a) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq (by norm_num)) hlog

/-- A frequency-band coefficient involving only the actual annulus,
the charts, and the cell-estimate constant; it contains no height ratio. -/
def outerNaturalBandMassCoefficient (T : MorseChainData)
    (a b K Cstar : ℝ) (n : ℕ) : ℝ :=
  (exp (2 * radialFrequencyThreshold T Cstar n ^ 2 * log (b / a)) / a ^ 8) * K * 81

/-- The true next mass is uniformly bounded on every single frequency
band, with no asymptotic lower bound on the transition index. -/
theorem morseRealized_next_normalized_mass_band_bound_of_upper
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ} {K Cstar : ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K)
    (side : Bool) (n : ℕ) (hn : 1 ≤ n) (hnidx : T.index ≤ n) (j : ℕ)
    (hj : (j : ℝ) < radialFrequencyThreshold T Cstar n) {entrance : ℝ}
    (hentry : T.radius side (n + 1) (T.leftX side (n + 1)) ≤ entrance) :
    normalizedRadialGaugeMass D j entrance
        (T.radius side (n + 1) (T.leftX side (n + 1)))
        (morseChainMassEnd T side (n + 1)) ≤
      outerNaturalBandMassCoefficient T D.a D.b K Cstar n *
        morseChainAmplitude T σ n * exp (27 * (n : ℝ) ^ 2) := by
  let m := n + 1
  let l := T.radius side m (T.leftX side m)
  let s := morseChainMassEnd T side m
  let G := exp (2 * radialFrequencyThreshold T Cstar n ^ 2 * log (D.b / D.a))
  have hm : T.index ≤ m := hnidx.trans (Nat.le_succ n)
  obtain ⟨hB, hAB, _, hlt, htr, _, _⟩ := h.retained_data side m hm
  have hA₀ : 0 ≤ morseChainA T m := ((mul_pos (by norm_num) hB).trans hAB).le
  have hA := morseChainA_le_nine T m (h.d_eq m hm)
  have hA₂ : morseChainA T m ^ 2 ≤ 81 := by
    simpa only [show (9 : ℝ) ^ 2 = 81 by norm_num] using pow_le_pow_left₀ hA₀ hA 2
  have hlcore : l ∈ radialCore D := h.radius_mem_core side m hm _
    (left_mem_Icc.mpr (hlt.trans htr).le)
  have hscore : s ∈ radialCore D := h.radius_mem_core side m hm _ ⟨hlt.le, htr.le⟩
  have hls : l ≤ s := (h.radius_strictMonoOn side m hm).monotoneOn
    (left_mem_Icc.mpr (hlt.trans htr).le) ⟨hlt.le, htr.le⟩ hlt.le
  have hsub : Icc l s ⊆ radialCore D := fun _ hx =>
    ⟨hlcore.1.trans_le hx.1, hx.2.trans_lt hscore.2⟩
  have hgauge (x : ℝ) (hx : x ∈ Icc l s) :
      (x / entrance) ^ (2 * j ^ 2) ≤ G :=
    radialGauge_annulus_power_le h.geometry j hj.le
      (hlcore.1.le.trans hentry) (hsub hx)
  have hmoment : morseCellMass T D side m ≤
      morseChainAmplitude T σ m * (K * 81) := by
    rw [(morseRealized_model_integrals h hσ side m hm).1]
    exact mul_le_mul_of_nonneg_left
      ((hcell.mass_upper side m hm).trans
        (mul_le_mul_of_nonneg_left hA₂ hcell.pos.le))
      (morseChainAmplitude_pos T σ hσ m).le
  have hamp := morseAdjacentScale_amplitude_le_exp_sq T σ hσ hn hnidx hm (Or.inl rfl)
  calc
    _ ≤ (G / D.a ^ 8) * morseCellMass T D side m :=
      normalizedRadialGaugeMass_le_moment h.geometry j hls hsub (exp_pos _).le hgauge
    _ ≤ (G / D.a ^ 8) * (morseChainAmplitude T σ m * (K * 81)) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = (G / D.a ^ 8 * K * 81) * morseChainAmplitude T σ m := by ring
    _ ≤ (G / D.a ^ 8 * K * 81) *
        (morseChainAmplitude T σ n * exp (27 * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hamp
        (mul_nonneg (mul_nonneg (by positivity) hcell.pos.le) (by norm_num))
    _ = _ := by dsimp only [outerNaturalBandMassCoefficient, G]; ring

/-- The original frequency-band statement follows from its upper bound. -/
theorem morseRealized_next_normalized_mass_band_bound
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ} {K Cstar : ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K)
    (side : Bool) (n : ℕ) (hn : 1 ≤ n) (j : ℕ)
    (hj : radialFrequencyBand T Cstar n j) {entrance : ℝ}
    (hentry : T.radius side (n + 1) (T.leftX side (n + 1)) ≤ entrance) :
    normalizedRadialGaugeMass D j entrance
        (T.radius side (n + 1) (T.leftX side (n + 1)))
        (morseChainMassEnd T side (n + 1)) ≤
      outerNaturalBandMassCoefficient T D.a D.b K Cstar n *
        morseChainAmplitude T σ n * exp (27 * (n : ℝ) ^ 2) :=
  morseRealized_next_normalized_mass_band_bound_of_upper
    h hσ hcell side n hn hj.1 j hj.2.2 hentry

/-- Every positive transition index, including the initial frequency
band, satisfies the first-mass estimate. The single constant is chosen
before every allowed height sequence and every realization of the charts. -/
theorem morseRealized_next_normalized_mass_all_indices_uniform_of_upper
    {T : MorseChainData} {σ₀ : ℕ → ℝ} {D₀ : ReferenceData} {C₀ : ℕ → ℝ}
    {K Cstar : ℝ} (h₀ : MorseChainRealization T σ₀ D₀ C₀)
    (hcell : MorseRealizedCellEstimates T K) (hCstar : 0 < Cstar) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
      ∀ (σ : ℕ → ℝ) (D : ReferenceData) (C : ℕ → ℝ),
        (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) → MorseChainRealization T σ D C →
        ∀ n : ℕ, 1 ≤ n → T.index ≤ n →
          ∀ j : ℕ, (j : ℝ) < radialFrequencyThreshold T Cstar n →
          ∀ side : Bool, ∀ entrance : ℝ,
            T.radius side (n + 1) (T.leftX side (n + 1)) ≤ entrance →
            normalizedRadialGaugeMass D j entrance
                (T.radius side (n + 1) (T.leftX side (n + 1)))
                (morseChainMassEnd T side (n + 1)) ≤
              morseChainAmplitude T σ n * exp (Cbound * (n : ℝ) ^ 2) := by
  have hlarge := (morseTransition_eventually_gauge_small_of_upper h₀ hCstar).and
    (eventually_ge_atTop (100 : ℕ))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hlarge
  let H : ℕ → ℝ := outerNaturalBandMassCoefficient T D₀.a D₀.b K Cstar
  obtain ⟨B, hB⟩ := (Set.finite_range (fun k : Fin N => H k)).bddAbove
  let M := exp 24 / D₀.a ^ 8 * K * 81
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (mul_nonneg (by positivity) hcell.pos.le) (by norm_num)
  let P := |B| + 1 + M
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  refine ⟨27 + P, by linarith only [hP], ?_⟩
  intro σ D C hσ h n hn hnidx j hj side entrance hentry
  obtain ⟨ha, hb⟩ := morseChainRealization_endpoints_eq h₀ h
  have hcoeff : normalizedRadialGaugeMass D j entrance
      (T.radius side (n + 1) (T.leftX side (n + 1)))
      (morseChainMassEnd T side (n + 1)) ≤
        P * morseChainAmplitude T σ n * exp (27 * (n : ℝ) ^ 2) := by
    by_cases hNn : N ≤ n
    · have hlarge_n := hN n hNn
      have hh := morseRealized_next_normalized_mass_le_height_exp h hσ hcell
        side n hnidx hlarge_n.2 j
        (hlarge_n.1 j hnidx hj (n + 1) (Nat.lt_succ_self n)) hentry
      rw [ha] at hh
      have hMP : M ≤ P := by dsimp only [P]; linarith only [abs_nonneg B]
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMP (morseChainAmplitude_pos T σ hσ n).le)
        (exp_pos _).le)
    · have hnN : n < N := Nat.lt_of_not_ge hNn
      have hHB : H n ≤ B := hB (Set.mem_range_self (⟨n, hnN⟩ : Fin N))
      have hHP : H n ≤ P := by
        dsimp only [P]
        linarith only [hHB, le_abs_self B, hM]
      have hh := morseRealized_next_normalized_mass_band_bound_of_upper
        h hσ hcell side n hn hnidx j hj hentry
      rw [ha, hb] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hHP (morseChainAmplitude_pos T σ hσ n).le)
        (exp_pos _).le)
  have hpref := nonneg_le_exp_mul_nat_sq hP hn
  calc
    _ ≤ P * morseChainAmplitude T σ n * exp (27 * (n : ℝ) ^ 2) := hcoeff
    _ ≤ (exp (P * (n : ℝ) ^ 2) * morseChainAmplitude T σ n) *
        exp (27 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpref (morseChainAmplitude_pos T σ hσ n).le)
        (exp_pos _).le
    _ = morseChainAmplitude T σ n * exp ((27 + P) * (n : ℝ) ^ 2) := by
      rw [mul_comm (exp (P * (n : ℝ) ^ 2)) (morseChainAmplitude T σ n),
        mul_assoc, ← exp_add]
      congr 2
      ring

/-- Retain the frequency-band API as a direct consequence of the
estimate which uses only the upper frequency threshold. -/
theorem morseRealized_next_normalized_mass_all_indices_uniform
    {T : MorseChainData} {σ₀ : ℕ → ℝ} {D₀ : ReferenceData} {C₀ : ℕ → ℝ}
    {K Cstar : ℝ} (h₀ : MorseChainRealization T σ₀ D₀ C₀)
    (hcell : MorseRealizedCellEstimates T K) (hCstar : 0 < Cstar) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
      ∀ (σ : ℕ → ℝ) (D : ReferenceData) (C : ℕ → ℝ),
        (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) → MorseChainRealization T σ D C →
        ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, radialFrequencyBand T Cstar n j →
          ∀ side : Bool, ∀ entrance : ℝ,
            T.radius side (n + 1) (T.leftX side (n + 1)) ≤ entrance →
            normalizedRadialGaugeMass D j entrance
                (T.radius side (n + 1) (T.leftX side (n + 1)))
                (morseChainMassEnd T side (n + 1)) ≤
              morseChainAmplitude T σ n * exp (Cbound * (n : ℝ) ^ 2) := by
  obtain ⟨Cbound, hCbound, hbound⟩ :=
    morseRealized_next_normalized_mass_all_indices_uniform_of_upper h₀ hcell hCstar
  refine ⟨Cbound, hCbound, ?_⟩
  intro σ D C hσ h n hn j hj side entrance hentry
  exact hbound σ D C hσ h n hn hj.1 j hj.2.2 side entrance hentry

end ContinuousFlexibility.Radial
