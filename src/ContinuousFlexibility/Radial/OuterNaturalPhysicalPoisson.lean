module

public import ContinuousFlexibility.Radial.OuterNaturalPhysicalMass
public import ContinuousFlexibility.Radial.OuterNaturalPoisson
public import ContinuousFlexibility.Radial.DeepTailParameterContinuity

/-!
# The actual physical natural solution normalized at the deep entrance

The data use the true radial profile. The radial equation follows from
the local signed gauge identity, and the norm in logarithmic variables
has exactly the factor required by the physical Hilbert measure.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- For the actual radial density the homogeneous source identity uses
no independent physical-cell localization or recurrence assumption. -/
theorem morsePhysicalDeepTail_naturalLift_radialJacobi
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ}
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u : ℝ → ℝ}
    (hu : TailNaturalEquation (morsePhysicalDeepTail M D right j start entrance η K) u)
    {x : ℝ} (hx : x ∈ Ioo
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      (morsePhysicalDeepTail M D right j start entrance η K).endpoint) :
    radialJacobi ((j : ℝ) ^ 2) D.w (tailPhysicalLift D right j u)
      (tailPhysicalRadius right x) = 0 := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  let s : ℝ := if right then 1 else -1
  let R := tailPhysicalEndpoint D right
  have hs : s * s = 1 := by cases right <;> norm_num [s]
  have hR : 0 < R := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hradius : tailPhysicalRadius right = fun y => exp (s * y) := by
    funext y
    cases right <;> simp [tailPhysicalRadius, s]
  have hp : ∀ y ∈ Ioo T.entrance T.endpoint,
      T.p y = (exp (s * y) / R) ^ (2 * (j : ℝ) ^ 2) *
        D.w (exp (s * y)) / exp (s * y) := by
    intro y _
    simpa only [hradius, R] using
      morsePhysicalDeepTail_density_eq M D right j start entrance η K y
  have hpx : T.p x ≠ 0 := (deepTail_pos hT x ⟨hx.1.le, hx.2⟩).ne'
  have hw₀ : D.w (exp (s * x)) ≠ 0 := by
    intro hz
    have hh := hp x hx
    rw [hz, mul_zero, zero_div] at hh
    exact hpx hh
  have hUV : ∀ y ∈ Ioo T.entrance T.endpoint,
      tailPhysicalLift D right j u (exp (s * y)) =
        (exp (s * y) / R) ^ ((j : ℝ) ^ 2) * u y := by
    intro y _
    simpa only [hradius, R] using tailPhysicalLift_radius D right j u y
  have hsource := radialJacobi_signed_physical_source_at hs hR hx
    (hD.2.2.1.1.differentiable (by simp) (exp (s * x))) hw₀
    ((tailNatural_contDiffAt hu hx).of_le (by simp)) hp hUV
  have heq : deriv (fun y => T.p y * deriv u y) x = -T.Λ * T.p x * u x := by
    linarith only [hu.2.2.2 x hx]
  have hzero : -(T.p x)⁻¹ * deriv (fun y => T.p y * deriv u y) x -
      (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1) * u x = 0 := by
    rw [heq]
    change -(T.p x)⁻¹ * (-((j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)) * T.p x * u x) -
      (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1) * u x = 0
    field_simp [hpx] <;> ring
  rw [hzero, mul_zero] at hsource
  simpa only [hradius] using hsource

/-- The actual physical lift is one at the regular entrance and solves
the actual radial equation. Its logarithmic squared norm, multiplied
by twelve, is the physical Hilbert squared norm. -/
theorem exists_morsePhysicalDeepTail_natural_norm_bound
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    (right : Bool) (j start : ℕ) {entrance η K : ℝ} (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    ∃ u : ℝ → ℝ, TailNaturalEquation T u ∧
      tailPhysicalLift D right j u entrance = 1 ∧
      (∀ x ∈ Ioo T.entrance T.endpoint,
        radialJacobi ((j : ℝ) ^ 2) D.w (tailPhysicalLift D right j u)
          (tailPhysicalRadius right x) = 0) ∧
      12 * (∫ x, u x ^ 2 ∂deepTailMeasure T) ≤
        396 * (tailMass T 0 /
          ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  let g : ℝ := (entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)
  have hend : 0 < tailPhysicalEndpoint D right := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hg : 0 < g := rpow_pos_of_pos (div_pos hentry hend) _
  obtain ⟨P, Q, hP, _, _, _, _, hPe, _, _, hnorm, _⟩ :=
    exists_tailNaturalPoisson_norm_bound hT hη hK
  let u : ℝ → ℝ := fun x => g⁻¹ * P x
  have hu : TailNaturalEquation T u := tailNaturalEquation_const_mul hP g⁻¹
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · change g * (g⁻¹ * P (tailPhysicalLog right entrance)) = 1
    change P (tailPhysicalLog right entrance) = 1 at hPe
    rw [hPe, mul_one, mul_inv_cancel₀ hg.ne']
  · exact fun x hx => morsePhysicalDeepTail_naturalLift_radialJacobi hD hT hu hx
  · have hscale : (∫ x, u x ^ 2 ∂deepTailMeasure T) =
        (∫ x, P x ^ 2 ∂deepTailMeasure T) / g ^ 2 := by
      change (∫ x, (g⁻¹ * P x) ^ 2 ∂deepTailMeasure T) = _
      simp_rw [mul_pow]
      rw [integral_const_mul, inv_pow]
      ring
    rw [hscale]
    have hdiv := div_le_div_of_nonneg_right hnorm (sq_nonneg g)
    have hmul := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 12)
    change 12 * ((∫ x, P x ^ 2 ∂deepTailMeasure T) / g ^ 2) ≤
      396 * (tailMass T 0 / g ^ 2)
    convert hmul using 1 <;> ring


/-- The complete quantitative natural-solution input in the actual
frequency bands, before replacing the exact logarithmic Hilbert
integral by its equal physical-radius integral. -/
theorem exists_morsePhysicalNatural_height_norm_bound
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ} {B Cstar : ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates M B) (hCstar : 0 < Cstar) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
      ∀ᶠ n : ℕ in atTop, ∀ j, radialFrequencyBand M Cstar n j →
        ∀ right : Bool, ∀ entrance η K : ℝ,
          M.radius right (n + 1) (M.leftX right (n + 1)) ≤ entrance →
          η ≤ 1 / 16 → 32 ≤ K →
          DeepTailHypotheses (morsePhysicalDeepTail M D right j (n + 1) entrance η K) →
          let T := morsePhysicalDeepTail M D right j (n + 1) entrance η K
          ∃ u : ℝ → ℝ, TailNaturalEquation T u ∧
            tailPhysicalLift D right j u entrance = 1 ∧
            (∀ x ∈ Ioo T.entrance T.endpoint,
              radialJacobi ((j : ℝ) ^ 2) D.w (tailPhysicalLift D right j u)
                (tailPhysicalRadius right x) = 0) ∧
            12 * (∫ x, u x ^ 2 ∂deepTailMeasure T) ≤
              morseChainAmplitude M σ n * exp (Cbound * (n : ℝ) ^ 2) := by
  obtain ⟨Cbase, hCbase, hmass⟩ :=
    morsePhysicalDeepTail_first_mass_eventually_le h hσ hcell hCstar
  refine ⟨Cbase + 396, by linarith only [hCbase], ?_⟩
  filter_upwards [hmass, eventually_ge_atTop (1 : ℕ)] with n hn hn₁
  intro j hj right entrance η K hentry hη hK hT
  have hstart : M.index ≤ n + 1 := hj.1.trans (Nat.le_succ n)
  obtain ⟨_, _, _, hlt, htr, _, _⟩ := h.retained_data right (n + 1) hstart
  have hepos : 0 < entrance :=
    (h.radius_positive right (n + 1) hstart _
      (left_mem_Icc.mpr (hlt.trans htr).le)).trans_le hentry
  obtain ⟨u, hu, hue, hODE, hnorm⟩ :=
    exists_morsePhysicalDeepTail_natural_norm_bound h.geometry
      right j (n + 1) hepos hT hη hK
  refine ⟨u, hu, hue, hODE, ?_⟩
  have hfirst := hn j hj right entrance η K hentry
  have hpref : (396 : ℝ) ≤ exp (396 * (n : ℝ) ^ 2) :=
    nonneg_le_exp_mul_nat_sq (by norm_num) hn₁
  calc
    _ ≤ 396 * (tailMass (morsePhysicalDeepTail M D right j (n + 1) entrance η K) 0 /
        ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2) := hnorm
    _ ≤ 396 * (morseChainAmplitude M σ n * exp (Cbase * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hfirst (by norm_num)
    _ ≤ exp (396 * (n : ℝ) ^ 2) *
        (morseChainAmplitude M σ n * exp (Cbase * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hpref
        (mul_nonneg (morseChainAmplitude_pos M σ hσ n).le (exp_pos _).le)
    _ = morseChainAmplitude M σ n * exp ((Cbase + 396) * (n : ℝ) ^ 2) := by
      rw [mul_left_comm, ← exp_add]
      congr 2
      ring

end ContinuousFlexibility.Radial
