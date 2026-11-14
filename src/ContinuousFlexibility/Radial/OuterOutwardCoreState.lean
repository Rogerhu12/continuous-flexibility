module

public import ContinuousFlexibility.Radial.OuterTransitionCoordinates
public import ContinuousFlexibility.Radial.OuterFundamentalPair
public import ContinuousFlexibility.Radial.OuterPhysicalTailBasis

/-!
# Actual core bounds for the normalized outer fundamental pair

The outward system is reflected back to the original radial system.
The already proved Morse-core energy estimate then applies directly to
each unit initial state. No core value estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- Reversing outward radius reverses the scaled flux as well, and
recovers exactly the original radial value/flux equation. -/
theorem outerFirstOrderSystem_radial_of_outward
    {D : ReferenceData} (hD : RadialProfileGeometry D) (right : Bool)
    {lam J l r : ℝ} {u z : ℝ → ℝ}
    (hsys : OuterFirstOrderSystem
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => J * deriv (outerTailOutwardWeight D right) x / (lam * x))
      u z (Icc (if right then l else -r) (if right then r else -l))) :
    OuterFirstOrderSystem (fun x => lam / D.w x)
      (fun x => J * deriv D.w x / (lam * x))
      (fun x => u (outerOutwardRadius right x))
      (fun x => outerTailSign right * z (outerOutwardRadius right x)) (Icc l r) := by
  intro x hx
  cases right with
  | true =>
      have hw : outerTailOutwardWeight D true = D.w := by
        funext y
        simp [outerTailOutwardWeight, outerTailSign]
      simpa only [hw, outerOutwardRadius, outerTailSign,
        ite_true, one_mul] using hsys x hx
  | false =>
      have hh := hsys (-x)
        (show -x ∈ Icc (-r) (-l) from
          ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩)
      have hw : outerTailOutwardWeight D false = fun y => D.w (-y) := by
        funext y
        simp [outerTailOutwardWeight, outerTailSign]
      rw [hw] at hh
      simp only [outerTailOutwardWeight, outerTailSign, Bool.false_eq_true,
        ite_false, neg_one_mul, neg_neg] at hh
      have hwd : deriv (fun y => D.w (-y)) (-x) = -deriv D.w x := by
        have hd := (hD.2.2.1.1.differentiable (by simp) (-(-x))).hasDerivAt.comp
          (-x) (hasDerivAt_id (-x)).neg
        simpa only [Function.comp_def, neg_neg, mul_neg_one] using hd.deriv
      rw [hwd] at hh
      simp only [outerOutwardRadius, outerTailSign, Bool.false_eq_true,
        ite_false, neg_one_mul]
      constructor
      · exact (hh.1.comp x (hasDerivAt_id x).neg).congr_deriv (by ring)
      · exact ((hh.2.comp x (hasDerivAt_id x).neg).neg).congr_deriv (by
          simp only [mul_neg, div_neg, neg_div, neg_mul, neg_neg, mul_one] <;> ring)

/-- Both components of a state obey the same exponential energy bound. -/
theorem outer_state_abs_le_exp {u z E : ℝ} (hE : 0 ≤ E)
    (hstate : u ^ 2 + z ^ 2 ≤ exp E) :
    |u| ≤ exp E ∧ |z| ≤ exp E := by
  have he : 1 ≤ exp E := one_le_exp_iff.mpr hE
  have he2 : exp E ≤ (exp E) ^ 2 := by nlinarith only [he]
  have hu : u ^ 2 ≤ (exp E) ^ 2 :=
    (by nlinarith only [hstate, sq_nonneg z] : u ^ 2 ≤ exp E).trans he2
  have hz : z ^ 2 ≤ (exp E) ^ 2 :=
    (by nlinarith only [hstate, sq_nonneg u] : z ^ 2 ≤ exp E).trans he2
  constructor
  · apply (sq_le_sq₀ (abs_nonneg u) (exp_pos E).le).mp
    simpa only [sq_abs] using hu
  · apply (sq_le_sq₀ (abs_nonneg z) (exp_pos E).le).mp
    simpa only [sq_abs] using hz

/-- The actual Morse energy estimate in increasing outward radius. -/
theorem morseTransitionCore_outward_energy
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {B Cstar L lam entry s t : ℝ} {n j : ℕ} {u z : ℝ → ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates M B) (hlam : 0 < lam) (hL : 0 ≤ L)
    (he : entry ∈ morseInitialMiddle M) (right : Bool)
    (hband : radialFrequencyBand M Cstar n j)
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
      exp (morseTransitionEnergyConstant M σ D C B Cstar L * (n : ℝ) ^ 2 +
        outerFullCoreActionExponent C B D.a * ((j : ℝ) * sqrt (morseChainA M n))) := by
  let l := morseTransitionCoreLeft M entry right n
  let r := morseTransitionCoreRight M entry right n
  have hrad := outerFirstOrderSystem_radial_of_outward h.geometry right
    (l := l) (r := r) hstate
  have hs' : outerOutwardRadius right s ∈ Icc l r :=
    (outerOutwardRadius_mem_core_interval right l r s).mpr hs
  have ht' : outerOutwardRadius right t ∈ Icc l r :=
    (outerOutwardRadius_mem_core_interval right l r t).mpr ht
  have hb := morseTransitionCore_energy_on_exp h hσ hcell hlam hL he right
    hband hhi hlo hrad hs' ht'
  have hsq (v : ℝ) : (outerTailSign right * v) ^ 2 = v ^ 2 := by
    cases right <;> simp [outerTailSign]
  simpa only [outerOutwardRadius_twice, hsq] using hb

/-- Unit normalization at the actual outer entrance gives all four
core value/flux bounds for the same constructed homogeneous pair. -/
theorem OuterFundamentalStatePair.morseTransition_core_bounds
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {B Cstar L lam entry b : ℝ} {n j : ℕ} {P ZP Q ZQ : ℝ → ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates M B) (hlam : 0 < lam) (hL : 0 ≤ L)
    (he : entry ∈ morseInitialMiddle M) (right : Bool)
    (hband : radialFrequencyBand M Cstar n j)
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
      let E := exp (morseTransitionEnergyConstant M σ D C B Cstar L * (n : ℝ) ^ 2 +
        outerFullCoreActionExponent C B D.a * ((j : ℝ) * sqrt (morseChainA M n)))
      |H.U x| ≤ E ∧ |H.ZU x| ≤ E ∧ |H.V x| ≤ E ∧ |H.ZV x| ≤ E := by
  let a := morseTransitionOutwardLeft M entry right n
  let c := morseTransitionOutwardRight M entry right n
  have hac : a ≤ c := (morseTransitionOutward_interval h he right n hband.1).1.le
  have hU : OuterFirstOrderSystem
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      H.U H.ZU (Icc a c) :=
    fun x hx => H.U_system x ⟨hx.1, hx.2.trans_lt hcb⟩
  have hV : OuterFirstOrderSystem
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      H.V H.ZV (Icc a c) :=
    fun x hx => H.V_system x ⟨hx.1, hx.2.trans_lt hcb⟩
  have hUinit : H.U a ^ 2 + H.ZU a ^ 2 = 1 :=
    (congrArg (fun v : ℝ × ℝ => v.1 ^ 2 + v.2 ^ 2) H.U_initial).trans
      (outerStatePerp_unit H.unit)
  have hVinit : H.V a ^ 2 + H.ZV a ^ 2 = 1 :=
    (congrArg (fun v : ℝ × ℝ => v.1 ^ 2 + v.2 ^ 2) H.V_initial).trans H.unit
  have hE : 0 ≤ morseTransitionEnergyConstant M σ D C B Cstar L * (n : ℝ) ^ 2 +
      outerFullCoreActionExponent C B D.a * ((j : ℝ) * sqrt (morseChainA M n)) := by
    apply add_nonneg
    · exact mul_nonneg (morseTransitionEnergyConstant_nonneg h hσ B Cstar L) (sq_nonneg _)
    · dsimp only [outerFullCoreActionExponent, outerCoreActionExponent, outerOutgoingActionExponent]
      positivity
  intro x hx
  have hu := morseTransitionCore_outward_energy h hσ hcell hlam hL he right
    hband hhi hlo hU (left_mem_Icc.mpr hac) hx
  have hv := morseTransitionCore_outward_energy h hσ hcell hlam hL he right
    hband hhi hlo hV (left_mem_Icc.mpr hac) hx
  rw [hUinit, one_mul] at hu
  rw [hVinit, one_mul] at hv
  exact ⟨(outer_state_abs_le_exp hE hu).1, (outer_state_abs_le_exp hE hu).2,
    (outer_state_abs_le_exp hE hv).1, (outer_state_abs_le_exp hE hv).2⟩

end ContinuousFlexibility.Radial
