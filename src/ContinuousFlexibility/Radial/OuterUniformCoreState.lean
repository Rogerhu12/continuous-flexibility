module

public import ContinuousFlexibility.Radial.OuterOutwardCoreState

/-!
# Uniform actual core states from the upper frequency threshold

For a cutoff strictly beyond the original initial cell the full-core
constants depend only on the common geometric bounds. The lower
frequency threshold plays no role, so the new initial frequency band
is covered by the same estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem OuterFundamentalStatePair.core_bounds_of_state_energy
    {a c b E : ℝ} {alpha beta P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    (hac : a ≤ c) (hcb : c < b) (hE : 0 ≤ E)
    (henergy : ∀ u z : ℝ → ℝ, OuterFirstOrderSystem alpha beta u z (Icc a c) →
      ∀ s ∈ Icc a c, ∀ t ∈ Icc a c,
        u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) * exp E) :
    ∀ x ∈ Icc a c,
      |H.U x| ≤ exp E ∧ |H.ZU x| ≤ exp E ∧
        |H.V x| ≤ exp E ∧ |H.ZV x| ≤ exp E := by
  have hU : OuterFirstOrderSystem alpha beta H.U H.ZU (Icc a c) :=
    fun x hx => H.U_system x ⟨hx.1, hx.2.trans_lt hcb⟩
  have hV : OuterFirstOrderSystem alpha beta H.V H.ZV (Icc a c) :=
    fun x hx => H.V_system x ⟨hx.1, hx.2.trans_lt hcb⟩
  have hUinit : H.U a ^ 2 + H.ZU a ^ 2 = 1 :=
    (congrArg (fun v : ℝ × ℝ => v.1 ^ 2 + v.2 ^ 2) H.U_initial).trans
      (outerStatePerp_unit H.unit)
  have hVinit : H.V a ^ 2 + H.ZV a ^ 2 = 1 :=
    (congrArg (fun v : ℝ × ℝ => v.1 ^ 2 + v.2 ^ 2) H.V_initial).trans H.unit
  intro x hx
  have hu := henergy H.U H.ZU hU a (left_mem_Icc.mpr hac) x hx
  have hv := henergy H.V H.ZV hV a (left_mem_Icc.mpr hac) x hx
  rw [hUinit, one_mul] at hu
  rw [hVinit, one_mul] at hv
  exact ⟨(outer_state_abs_le_exp hE hu).1, (outer_state_abs_le_exp hE hu).2,
    (outer_state_abs_le_exp hE hv).1, (outer_state_abs_le_exp hE hv).2⟩

theorem morseOuterFullCore_outward_energy_of_upper
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
  let l := morseOuterCoreLeft M right n
  let r := morseOuterFullCoreRight M right n
  have hne : n ≠ M.index := ne_of_gt hn
  have hleft : morseTransitionOutwardLeft M entry right n = if right then l else -r := by
    simp only [morseTransitionOutwardLeft, morseTransitionCoreLeft,
      morseTransitionCoreRight, if_neg hne, l, r]
  have hright : morseTransitionOutwardRight M entry right n = if right then r else -l := by
    simp only [morseTransitionOutwardRight, morseTransitionCoreLeft,
      morseTransitionCoreRight, if_neg hne, l, r]
  rw [hleft, hright] at hstate hs ht
  have hrad := outerFirstOrderSystem_radial_of_outward h.geometry right
    (l := l) (r := r) hstate
  have hs' : outerOutwardRadius right s ∈ Icc l r :=
    (outerOutwardRadius_mem_core_interval right l r s).mpr hs
  have ht' : outerOutwardRadius right t ∈ Icc l r :=
    (outerOutwardRadius_mem_core_interval right l r t).mpr ht
  have hb := morseOuterFullCore_energy_on_exp_of_upper h hσ hcell hlam hL right
    hn hupper hhi hlo hrad hs' ht'
  have hsq (v : ℝ) : (outerTailSign right * v) ^ 2 = v ^ 2 := by
    cases right <;> simp [outerTailSign]
  simpa only [outerOutwardRadius_twice, hsq] using hb

/-- The same normalized pair has bounds with constants independent of
the height sequence and of every frequency below the moving upper cutoff. -/
theorem OuterFundamentalStatePair.morseFullCore_bounds_of_upper
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {B Cstar L lam entry b : ℝ} {n j : ℕ} {P ZP Q ZQ : ℝ → ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates M B) (hlam : 0 < lam) (hL : 0 ≤ L)
    (he : entry ∈ morseInitialMiddle M) (right : Bool) (hn : M.index < n)
    (hupper : (j : ℝ) < radialFrequencyThreshold M Cstar n)
    (hhi : lam / morseChainAmplitude M σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude M σ n / lam ≤ exp (L * (n : ℝ) ^ 2))
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      P ZP Q ZQ (morseTransitionOutwardLeft M entry right n)
        (morseTransitionOutwardRight M entry right n) b)
    (hcb : morseTransitionOutwardRight M entry right n < b) :
    ∀ x ∈ Icc (morseTransitionOutwardLeft M entry right n)
      (morseTransitionOutwardRight M entry right n),
      let E := exp (outerFullCoreQuadraticExponent C B D.a Cstar L * (n : ℝ) ^ 2 +
        outerFullCoreActionExponent C B D.a * ((j : ℝ) * sqrt (morseChainA M n)))
      |H.U x| ≤ E ∧ |H.ZU x| ≤ E ∧ |H.V x| ≤ E ∧ |H.ZV x| ≤ E := by
  have hB := hcell.pos
  have hC := h.constants_pos 0
  have ha := h.geometry.1
  have hQ : 0 ≤ outerFullCoreQuadraticExponent C B D.a Cstar L := by
    dsimp only [outerFullCoreQuadraticExponent, outerCoreInteriorQuadraticExponent,
      outerCoreQuadraticExponent, outerOutgoingQuadraticExponent, outerFrequencyExponent,
      outerJoinPrefactor]
    positivity
  have hCo : 0 ≤ outerFullCoreActionExponent C B D.a := by
    dsimp only [outerFullCoreActionExponent, outerCoreActionExponent, outerOutgoingActionExponent]
    positivity
  apply H.core_bounds_of_state_energy
    (morseTransitionOutward_interval h he right n hn.le).1.le hcb
    (add_nonneg (mul_nonneg hQ (sq_nonneg _))
      (mul_nonneg hCo (mul_nonneg (Nat.cast_nonneg _) (sqrt_nonneg _))))
  intro u z hstate s hs t ht
  exact morseOuterFullCore_outward_energy_of_upper h hσ hcell hlam hL right
    hn hupper hhi hlo hstate hs ht

/-- The same estimate with the exact physical endpoints used by the
whole Green operator. The basis object is retained without a coordinate cast. -/
theorem OuterFundamentalStatePair.morseFullCore_physical_bounds_of_upper
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {B Cstar L lam entry : ℝ} {n j : ℕ} {P ZP Q ZQ : ℝ → ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates M B) (hlam : 0 < lam) (hL : 0 ≤ L)
    (he : entry ∈ morseInitialMiddle M) (right : Bool) (hn : M.index < n)
    (hupper : (j : ℝ) < radialFrequencyThreshold M Cstar n)
    (hhi : lam / morseChainAmplitude M σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude M σ n / lam ≤ exp (L * (n : ℝ) ^ 2))
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      P ZP Q ZQ
      (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
      (outerOutwardRadius right (morseOuterDeepEntrance M right n))
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    ∀ x ∈ Icc
      (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
      (outerOutwardRadius right (morseOuterDeepEntrance M right n)),
      let E := exp (outerFullCoreQuadraticExponent C B D.a Cstar L * (n : ℝ) ^ 2 +
        outerFullCoreActionExponent C B D.a * ((j : ℝ) * sqrt (morseChainA M n)))
      |H.U x| ≤ E ∧ |H.ZU x| ≤ E ∧ |H.V x| ≤ E ∧ |H.ZV x| ≤ E := by
  have hB := hcell.pos
  have hC := h.constants_pos 0
  have ha := h.geometry.1
  have hQ : 0 ≤ outerFullCoreQuadraticExponent C B D.a Cstar L := by
    dsimp only [outerFullCoreQuadraticExponent, outerCoreInteriorQuadraticExponent,
      outerCoreQuadraticExponent, outerOutgoingQuadraticExponent, outerFrequencyExponent,
      outerJoinPrefactor]
    positivity
  have hCo : 0 ≤ outerFullCoreActionExponent C B D.a := by
    dsimp only [outerFullCoreActionExponent, outerCoreActionExponent, outerOutgoingActionExponent]
    positivity
  have hi := morseTransitionOutward_interval h he right n hn.le
  rw [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] at hi
  apply H.core_bounds_of_state_energy hi.1.le hi.2
    (add_nonneg (mul_nonneg hQ (sq_nonneg _))
      (mul_nonneg hCo (mul_nonneg (Nat.cast_nonneg _) (sqrt_nonneg _))))
  intro u z hstate s hs t ht
  have hstate' : OuterFirstOrderSystem
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      u z (Icc (morseTransitionOutwardLeft M entry right n)
        (morseTransitionOutwardRight M entry right n)) := by
    simpa only [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] using hstate
  have hs' : s ∈ Icc (morseTransitionOutwardLeft M entry right n)
      (morseTransitionOutwardRight M entry right n) := by
    simpa only [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] using hs
  have ht' : t ∈ Icc (morseTransitionOutwardLeft M entry right n)
      (morseTransitionOutwardRight M entry right n) := by
    simpa only [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] using ht
  exact morseOuterFullCore_outward_energy_of_upper h hσ hcell hlam hL right
    hn hupper hhi hlo hstate' hs' ht'

end ContinuousFlexibility.Radial
