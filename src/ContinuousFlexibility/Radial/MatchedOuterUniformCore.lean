import ContinuousFlexibility.Radial.MatchedOuterCoreBounds

/-!
# One actual core-pair envelope before the height choices

Beyond the original first cell, the full-core constants depend on the
common geometry and coefficient bounds. The upper frequency cutoff
suffices, including every low frequency assigned to an enlarged initial
band. The same supplied fundamental pair is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- The original full-core estimate, reflected by the already proved
coordinate identity, needs only the moving upper cutoff. -/
theorem matchedMorse_fullCore_outward_energy_of_upper
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {B Cstar L lam entry s t : ℝ} {n j : ℕ} {u z : ℝ → ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates M B) (hlam : 0 < lam) (hL : 0 ≤ L)
    (right : Bool) (hn : M.index < n)
    (hupper : (j : ℝ) < radialFrequencyThreshold M Cstar n)
    (hhi : lam / morseChainAmplitude M σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude M σ n / lam ≤ exp (L * (n : ℝ) ^ 2))
    (hstate : OuterFirstOrderSystem
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      u z (Icc (morseTransitionOutwardLeft M entry right n)
        (morseTransitionOutwardRight M entry right n)))
    (hs : s ∈ Icc (morseTransitionOutwardLeft M entry right n)
      (morseTransitionOutwardRight M entry right n))
    (ht : t ∈ Icc (morseTransitionOutwardLeft M entry right n)
      (morseTransitionOutwardRight M entry right n)) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      exp (outerFullCoreQuadraticExponent C B D.a Cstar L * (n : ℝ) ^ 2 +
        outerFullCoreActionExponent C B D.a * ((j : ℝ) * sqrt (morseChainA M n))) := by
  have hne : n ≠ M.index := Nat.ne_of_gt hn
  let l := morseOuterCoreLeft M right n
  let r := morseOuterFullCoreRight M right n
  have hstate' : OuterFirstOrderSystem
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      u z (Icc (if right then l else -r) (if right then r else -l)) := by
    simpa only [morseTransitionOutwardLeft, morseTransitionOutwardRight,
      morseTransitionCoreLeft, morseTransitionCoreRight, if_neg hne] using hstate
  have hs' : s ∈ Icc (if right then l else -r) (if right then r else -l) := by
    simpa only [morseTransitionOutwardLeft, morseTransitionOutwardRight,
      morseTransitionCoreLeft, morseTransitionCoreRight, if_neg hne] using hs
  have ht' : t ∈ Icc (if right then l else -r) (if right then r else -l) := by
    simpa only [morseTransitionOutwardLeft, morseTransitionOutwardRight,
      morseTransitionCoreLeft, morseTransitionCoreRight, if_neg hne] using ht
  have hrad := outerFirstOrderSystem_radial_of_outward h.geometry right hstate'
  have hsrad := (outerOutwardRadius_mem_core_interval right l r s).mpr hs'
  have htrad := (outerOutwardRadius_mem_core_interval right l r t).mpr ht'
  have hb := morseOuterFullCore_energy_on_exp_of_upper h hσ hcell hlam hL right
    hn hupper hhi hlo hrad hsrad htrad
  have hsq (v : ℝ) : (outerTailSign right * v) ^ 2 = v ^ 2 := by
    cases right <;> simp [outerTailSign]
  simpa only [outerOutwardRadius_twice, hsq] using hb

/-- The common exponent is selected before every height sequence and
frequency. All low frequencies below the selected cutoff are allowed.
Only actual profile coefficients and the actual unit-normalized pair
occur in the hypotheses. -/
theorem exists_matchedMorse_uniform_actual_core_pair_bound
    {M : MorseChainData} {C : ℕ → ℝ}
    {family : (ℕ → ℝ) → ReferenceData} {Cstar L : ℝ}
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization M σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧
      (family σ).b = (family τ).b)
    (hCstar : 0 < Cstar) (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 < A ∧
      ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      ∀ (entry : ℝ), entry ∈ morseInitialMiddle M →
      ∀ (right : Bool) (n j : ℕ), M.index < n →
        (j : ℝ) < radialFrequencyThreshold M Cstar n →
      ∀ (lam : ℝ), 0 < lam →
        lam / morseChainAmplitude M σ n ≤ exp (L * (n : ℝ) ^ 2) →
        morseChainAmplitude M σ n / lam ≤ exp (L * (n : ℝ) ^ 2) →
      ∀ (b : ℝ) (P ZP Q ZQ : ℝ → ℝ)
        (H : OuterFundamentalStatePair
          (fun x => lam / outerTailOutwardWeight (family σ) right x)
          (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight (family σ) right) x /
            (lam * x))
          P ZP Q ZQ (morseTransitionOutwardLeft M entry right n)
            (morseTransitionOutwardRight M entry right n) b),
        morseTransitionOutwardRight M entry right n < b →
        ∀ x ∈ Icc (morseTransitionOutwardLeft M entry right n)
            (morseTransitionOutwardRight M entry right n),
          |H.U x| ≤ exp (A * radialQ n) ∧
            |H.ZU x| ≤ exp (A * radialQ n) ∧
            |H.V x| ≤ exp (A * radialQ n) ∧
            |H.ZV x| ≤ exp (A * radialQ n) := by
  let σ₀ : ℕ → ℝ := fun _ => 1
  have h₀ := hfamily σ₀ (fun _ => ⟨le_rfl, by norm_num [σ₀]⟩)
  obtain ⟨B, hcell⟩ := exists_morseRealizedCellEstimates h₀
  let q := outerFullCoreQuadraticExponent C B (family σ₀).a Cstar L
  let co := outerFullCoreActionExponent C B (family σ₀).a
  let A := |q| + |co| * Cstar + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro σ hσ entry he right n j hn hupper lam hlam hhi hlo b P ZP Q ZQ H hcb x hx
  have h := hfamily σ hσ
  have hQ : 0 ≤ radialQ n := (sq_nonneg (n : ℝ)).trans (radial_nat_sq_le_Q n)
  have hcost : q * (n : ℝ) ^ 2 + co * ((j : ℝ) * sqrt (morseChainA M n)) ≤
      A * radialQ n :=
    (matchedTransition_exponent_le_of_upper (h.d_eq n hn.le) hupper q co).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith) hQ)
  have hcost' : outerFullCoreQuadraticExponent C B (family σ).a Cstar L * (n : ℝ) ^ 2 +
      outerFullCoreActionExponent C B (family σ).a * ((j : ℝ) * sqrt (morseChainA M n)) ≤
        A * radialQ n := by
    rw [(hends σ σ₀).1]
    exact hcost
  let a := morseTransitionOutwardLeft M entry right n
  let c := morseTransitionOutwardRight M entry right n
  have hac : a ≤ c := (morseTransitionOutward_interval h he right n hn.le).1.le
  have hstate (u z : ℝ → ℝ)
      (hsys : OuterFirstOrderSystem
        (fun y => lam / outerTailOutwardWeight (family σ) right y)
        (fun y => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight (family σ) right) y /
          (lam * y)) u z (Ico a b))
      (hunit : u a ^ 2 + z a ^ 2 = 1) :
      |u x| ≤ exp (A * radialQ n) ∧ |z x| ≤ exp (A * radialQ n) := by
    have hb := matchedMorse_fullCore_outward_energy_of_upper h hσ hcell hlam hL
      right hn hupper hhi hlo
      (fun y hy => hsys y ⟨hy.1, hy.2.trans_lt hcb⟩)
      (left_mem_Icc.mpr hac) hx
    rw [hunit, one_mul] at hb
    exact outer_state_abs_le_exp (mul_nonneg hA.le hQ) (hb.trans (exp_le_exp.mpr hcost'))
  have hU := hstate H.U H.ZU H.U_system
    ((congrArg (fun v : ℝ × ℝ => v.1 ^ 2 + v.2 ^ 2) H.U_initial).trans
      (outerStatePerp_unit H.unit))
  have hV := hstate H.V H.ZV H.V_system
    ((congrArg (fun v : ℝ × ℝ => v.1 ^ 2 + v.2 ^ 2) H.V_initial).trans H.unit)
  exact ⟨hU.1, hU.2, hV.1, hV.2⟩

end ContinuousFlexibility.Radial
