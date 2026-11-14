module

public import ContinuousFlexibility.Radial.OuterNaturalMassScale
public import ContinuousFlexibility.Radial.DeepTailPhysicalLift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# First-mass transport for the actual radial deep tail

The signed logarithmic substitution is proved on both orientations.
The actual tail data below use the left endpoint and right turning point
of each retained Morse mass interval, in outward order. Consequently
the first mass is the normalized radial mass from the preceding module
by its definition, not by an assumed mass comparison.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The actual logarithmic gauge density, written with its integer power. -/
def outerMassLogDensity (D : ReferenceData) (j : ℕ) (endpoint : ℝ)
    (right : Bool) (x : ℝ) : ℝ :=
  (tailPhysicalRadius right x / endpoint) ^ (2 * j ^ 2) *
    D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x

theorem continuous_outerMassLogDensity {D : ReferenceData} (hw : Continuous D.w)
    (j : ℕ) (endpoint : ℝ) (right : Bool) :
    Continuous (outerMassLogDensity D j endpoint right) := by
  exact ((((continuous_tailPhysicalRadius right).div_const endpoint).pow (2 * j ^ 2)).mul
    (hw.comp (continuous_tailPhysicalRadius right))).div
      (continuous_tailPhysicalRadius right) (fun x => (tailPhysicalRadius_pos right x).ne')

/-- The orientation at the left endpoint reverses both the integration
limits and the sign of the logarithmic Jacobian. -/
theorem outerMassLogDensity_integral {D : ReferenceData} (hw : Continuous D.w)
    (j : ℕ) (endpoint : ℝ) (right : Bool) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r) :
    (∫ x in (if right then log l else -log r)..(if right then log r else -log l),
      outerMassLogDensity D j endpoint right x) =
      normalizedRadialGaugeMass D j endpoint l r := by
  have hxpos (x : ℝ) (hx : x ∈ uIcc l r) : 0 < x :=
    hl.trans_le (show x ∈ Icc l r by simpa only [uIcc_of_le hlr] using hx).1
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc l r) :=
    continuousOn_id.inv₀ (fun x hx => (hxpos x hx).ne')
  cases right with
  | true =>
      have hchange := intervalIntegral.integral_comp_mul_deriv
        (a := l) (b := r) (f := log) (f' := fun x => x⁻¹)
        (g := outerMassLogDensity D j endpoint true)
        (fun x hx => hasDerivAt_log (hxpos x hx).ne') hinv
        (continuous_outerMassLogDensity hw j endpoint true)
      calc
        _ = ∫ x in l..r, (outerMassLogDensity D j endpoint true ∘ log) x * x⁻¹ :=
          hchange.symm
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro x hx
          change ((exp (log x) / endpoint) ^ (2 * j ^ 2) *
            D.w (exp (log x)) / exp (log x)) * x⁻¹ =
              (x / endpoint) ^ (2 * j ^ 2) * D.w x / x ^ 2
          rw [exp_log (hxpos x hx)]
          ring
  | false =>
      have hchange := intervalIntegral.integral_comp_mul_deriv
        (a := l) (b := r) (f := fun x => -log x) (f' := fun x => -x⁻¹)
        (g := outerMassLogDensity D j endpoint false)
        (fun x hx => (hasDerivAt_log (hxpos x hx).ne').neg) hinv.neg
        (continuous_outerMassLogDensity hw j endpoint false)
      have hnegative :
          (∫ x in l..r, (outerMassLogDensity D j endpoint false ∘ (fun y => -log y)) x *
            (-x⁻¹)) = -normalizedRadialGaugeMass D j endpoint l r := by
        calc
          _ = ∫ x in l..r, -((x / endpoint) ^ (2 * j ^ 2) * D.w x / x ^ 2) := by
            apply intervalIntegral.integral_congr
            intro x hx
            change ((exp (-(-log x)) / endpoint) ^ (2 * j ^ 2) *
              D.w (exp (-(-log x))) / exp (-(-log x))) * (-x⁻¹) =
                -((x / endpoint) ^ (2 * j ^ 2) * D.w x / x ^ 2)
            rw [neg_neg, exp_log (hxpos x hx)]
            ring
          _ = _ := intervalIntegral.integral_neg
      calc
        _ = -(∫ x in -log l..-log r, outerMassLogDensity D j endpoint false x) :=
          intervalIntegral.integral_symm _ _
        _ = -(-normalizedRadialGaugeMass D j endpoint l r) := by
          rw [← hchange, hnegative]
        _ = _ := neg_neg _

/-- Dividing by the squared entrance gauge changes the normalization
radius of the actual radial mass integral. -/
theorem normalizedRadialGaugeMass_div {D : ReferenceData} (j : ℕ)
    {endpoint entrance l r : ℝ} (hend : 0 < endpoint) (hentry : 0 < entrance) :
    normalizedRadialGaugeMass D j endpoint l r /
        (entrance / endpoint) ^ (2 * j ^ 2) =
      normalizedRadialGaugeMass D j entrance l r := by
  have hden : (entrance / endpoint) ^ (2 * j ^ 2) ≠ 0 :=
    pow_ne_zero _ (div_ne_zero hentry.ne' hend.ne')
  unfold normalizedRadialGaugeMass
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro x _
  have hratio : x / endpoint = (x / entrance) * (entrance / endpoint) := by
    field_simp [hentry.ne', hend.ne']
  change (x / endpoint) ^ (2 * j ^ 2) * D.w x / x ^ 2 /
      (entrance / endpoint) ^ (2 * j ^ 2) =
    (x / entrance) ^ (2 * j ^ 2) * D.w x / x ^ 2
  rw [hratio, mul_pow]
  calc
    _ = ((entrance / endpoint) ^ (2 * j ^ 2) /
        (entrance / endpoint) ^ (2 * j ^ 2)) *
          ((x / entrance) ^ (2 * j ^ 2) * D.w x / x ^ 2) := by ring
    _ = _ := by rw [div_self hden, one_mul]

/-- The true mass nodes in signed logarithmic radius. The left-hand
resistance edge following mass m runs through join m and cap m+1. -/
def morsePhysicalDeepTail (M : MorseChainData) (D : ReferenceData)
    (right : Bool) (j start : ℕ) (entrance η K : ℝ) : DeepTailData where
  entrance := tailPhysicalLog right entrance
  endpoint := tailPhysicalLog right (tailPhysicalEndpoint D right)
  p := outerMassLogDensity D j (tailPhysicalEndpoint D right) right
  node := fun k => tailPhysicalLog right
    (if right then M.radius right (start + k) (M.leftX right (start + k))
      else morseChainMassEnd M right (start + k))
  massEnd := fun k => tailPhysicalLog right
    (if right then morseChainMassEnd M right (start + k)
      else M.radius right (start + k) (M.leftX right (start + k)))
  Λ := (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)
  η := η
  K := K

/-- The density is exactly the real-power expression used by the
physical relation and the signed gauge identity. -/
theorem morsePhysicalDeepTail_density_eq (M : MorseChainData) (D : ReferenceData)
    (right : Bool) (j start : ℕ) (entrance η K x : ℝ) :
    (morsePhysicalDeepTail M D right j start entrance η K).p x =
      (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ (2 * (j : ℝ) ^ 2) *
        D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x := by
  have hcast : 2 * (j : ℝ) ^ 2 = ((2 * j ^ 2 : ℕ) : ℝ) := by simp
  rw [hcast, rpow_natCast]
  rfl

/-- The first actual logarithmic mass is exactly the increasing-radius
Morse mass with its normalized gauge weight. -/
theorem morsePhysicalDeepTail_first_mass {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (j start : ℕ) (hstart : M.index ≤ start) (entrance η K : ℝ) :
    tailMass (morsePhysicalDeepTail M D right j start entrance η K) 0 =
      normalizedRadialGaugeMass D j (tailPhysicalEndpoint D right)
        (M.radius right start (M.leftX right start)) (morseChainMassEnd M right start) := by
  obtain ⟨_, _, _, hlt, htr, _, _⟩ := h.retained_data right start hstart
  have hl : 0 < M.radius right start (M.leftX right start) :=
    h.radius_positive right start hstart _ (left_mem_Icc.mpr (hlt.trans htr).le)
  have hls : M.radius right start (M.leftX right start) ≤ morseChainMassEnd M right start :=
    (h.radius_strictMonoOn right start hstart).monotoneOn
      (left_mem_Icc.mpr (hlt.trans htr).le) ⟨hlt.le, htr.le⟩ hlt.le
  have hh := outerMassLogDensity_integral h.geometry.2.2.1.1.continuous
    j (tailPhysicalEndpoint D right) right hl hls
  cases right <;>
    simpa [tailMass, morsePhysicalDeepTail, tailPhysicalLog] using hh

/-- Exact conversion to the entrance normalization used by Lemma 6.4,
including the square of the real-power gauge from the manuscript. -/
theorem morsePhysicalDeepTail_normalized_first_mass {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (j start : ℕ) (hstart : M.index ≤ start)
    {entrance : ℝ} (hentry : 0 < entrance) (η K : ℝ) :
    tailMass (morsePhysicalDeepTail M D right j start entrance η K) 0 /
        ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2 =
      normalizedRadialGaugeMass D j entrance
        (M.radius right start (M.leftX right start)) (morseChainMassEnd M right start) := by
  have hend : 0 < tailPhysicalEndpoint D right := by
    cases right
    · exact h.geometry.1
    · exact h.geometry.1.trans h.geometry.2.1
  have hcast : (j : ℝ) ^ 2 = ((j ^ 2 : ℕ) : ℝ) := by simp
  rw [morsePhysicalDeepTail_first_mass h right j start hstart entrance η K,
    hcast, rpow_natCast, ← pow_mul, Nat.mul_comm (j ^ 2) 2]
  exact normalizedRadialGaugeMass_div j hend hentry

/-- The physical first-mass input is obtained from the actual tail's
fields and the already proved Morse interval estimate. -/
theorem morsePhysicalDeepTail_normalized_first_mass_le
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ} {B : ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates M B) (right : Bool)
    (j start : ℕ) (hstart : M.index ≤ start) (h100 : 100 ≤ start)
    (hfrequency : (j : ℝ) ^ 2 * morseChainA M start ≤ 1)
    {entrance : ℝ}
    (hentry : M.radius right start (M.leftX right start) ≤ entrance) (η K : ℝ) :
    tailMass (morsePhysicalDeepTail M D right j start entrance η K) 0 /
        ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2 ≤
      (exp 24 / D.a ^ 8) * morseChainAmplitude M σ start * B * morseChainA M start ^ 2 := by
  obtain ⟨_, _, _, hlt, htr, _, _⟩ := h.retained_data right start hstart
  have hepos : 0 < entrance :=
    (h.radius_positive right start hstart _ (left_mem_Icc.mpr (hlt.trans htr).le)).trans_le hentry
  rw [morsePhysicalDeepTail_normalized_first_mass h right j start hstart hepos η K]
  exact morseRealized_normalized_mass_le h hσ hcell right start hstart h100
    j hfrequency hentry

/-- Every frequency band has a uniform first-mass bound for the actual
tail starting at the next cell, in either outward orientation. -/
theorem morsePhysicalDeepTail_first_mass_eventually_le
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ} {B Cstar : ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates M B) (hCstar : 0 < Cstar) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
      ∀ᶠ n : ℕ in atTop, ∀ j, radialFrequencyBand M Cstar n j →
        ∀ right : Bool, ∀ entrance η K : ℝ,
          M.radius right (n + 1) (M.leftX right (n + 1)) ≤ entrance →
          tailMass (morsePhysicalDeepTail M D right j (n + 1) entrance η K) 0 /
              ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2 ≤
            morseChainAmplitude M σ n * exp (Cbound * (n : ℝ) ^ 2) := by
  obtain ⟨Cbound, hCbound, hbound⟩ :=
    morseRealized_next_normalized_mass_eventually_le h hσ hcell hCstar
  refine ⟨Cbound, hCbound, ?_⟩
  filter_upwards [hbound] with n hn
  intro j hj right entrance η K hentry
  have hstart : M.index ≤ n + 1 := hj.1.trans (Nat.le_succ n)
  obtain ⟨_, _, _, hlt, htr, _, _⟩ := h.retained_data right (n + 1) hstart
  have hepos : 0 < entrance :=
    (h.radius_positive right (n + 1) hstart _
      (left_mem_Icc.mpr (hlt.trans htr).le)).trans_le hentry
  rw [morsePhysicalDeepTail_normalized_first_mass h right j (n + 1) hstart hepos η K]
  exact hn j hj right entrance hentry

end ContinuousFlexibility.Radial
