import ContinuousFlexibility.Radial.SeedConeModes
import ContinuousFlexibility.Radial.SeedConnectorInterpolation

/-!
# Nonvanishing and C1 control of actual cone modes

The signed frequency treats both ends simultaneously.  Factoring out the
dominant exponential leaves q*exp(-2*s*y), which tends to zero as s*y
tends to positive infinity.  No global nonvanishing assumption is made.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

def coneModePair (s A B y : ℝ) : ℝ :=
  A * exp (s * y) + B * exp (-s * y)

def coneModeRatio (s q y : ℝ) : ℝ :=
  q * exp (-2 * (s * y))

def coneModeSlope (s q y : ℝ) : ℝ :=
  s * (1 - coneModeRatio s q y) / (1 + coneModeRatio s q y)

theorem coneModeRatio_contDiff (s q : ℝ) :
    ContDiff ℝ ∞ (coneModeRatio s q) := by
  unfold coneModeRatio
  fun_prop

theorem hasDerivAt_coneModeRatio (s q y : ℝ) :
    HasDerivAt (coneModeRatio s q) (-2 * s * coneModeRatio s q y) y := by
  have h := ((((hasDerivAt_id' y).const_mul s).const_mul (-2 : ℝ)).exp).const_mul q
  apply h.congr_deriv
  simp only [coneModeRatio, Function.comp_apply]
  ring

theorem hasDerivAt_coneModePair (s A B y : ℝ) :
    HasDerivAt (coneModePair s A B)
      (s * (A * exp (s * y) - B * exp (-s * y))) y := by
  have h := ((((hasDerivAt_id' y).const_mul s).exp).const_mul A).add
    ((((hasDerivAt_id' y).const_mul (-s)).exp).const_mul B)
  apply h.congr_deriv
  ring

private theorem coneModePair_tail_term {s A B : ℝ} (hA : A ≠ 0) (y : ℝ) :
    B * exp (-s * y) = (A * exp (s * y)) * coneModeRatio s (B / A) y := by
  have he : exp (s * y) * exp (-2 * (s * y)) = exp (-s * y) := by
    rw [← exp_add]
    congr 1
    ring
  symm
  calc
    _ = B * (exp (s * y) * exp (-2 * (s * y))) := by
      dsimp only [coneModeRatio]
      field_simp [hA]
    _ = _ := by rw [he]

theorem coneModePair_factor {s A B : ℝ} (hA : A ≠ 0) (y : ℝ) :
    coneModePair s A B y =
      (A * exp (s * y)) * (1 + coneModeRatio s (B / A) y) := by
  rw [coneModePair, coneModePair_tail_term hA y]
  ring

theorem coneModeSlope_contDiffAt {s q y : ℝ}
    (hd : 1 + coneModeRatio s q y ≠ 0) :
    ContDiffAt ℝ ∞ (coneModeSlope s q) y :=
  (contDiffAt_const.mul (contDiffAt_const.sub
    (coneModeRatio_contDiff s q).contDiffAt)).div
      (contDiffAt_const.add (coneModeRatio_contDiff s q).contDiffAt) hd

theorem hasDerivAt_coneModeSlope {s q y : ℝ}
    (hd : 1 + coneModeRatio s q y ≠ 0) :
    HasDerivAt (coneModeSlope s q)
      (4 * s ^ 2 * coneModeRatio s q y / (1 + coneModeRatio s q y) ^ 2) y := by
  have hz := hasDerivAt_coneModeRatio s q y
  have h := (((hasDerivAt_const y (1 : ℝ)).sub hz).const_mul s).div
    (hz.const_add 1) hd
  apply h.congr_deriv
  simp only [Pi.sub_apply]
  ring

theorem coneModeSlope_eq_logDerivative {s A B y : ℝ}
    (hA : A ≠ 0) (hd : 1 + coneModeRatio s (B / A) y ≠ 0) :
    coneModeSlope s (B / A) y =
      deriv (coneModePair s A B) y / coneModePair s A B y := by
  rw [(hasDerivAt_coneModePair s A B y).deriv,
    coneModePair_factor hA y, coneModePair_tail_term hA y]
  dsimp only [coneModeSlope]
  field_simp [hA, (exp_pos (s * y)).ne', hd]
  <;> ring

theorem coneModePair_neg_swap (s A B : ℝ) :
    coneModePair (-s) B A = coneModePair s A B := by
  funext y
  simp only [coneModePair, neg_neg, add_comm]

private theorem conePointwise_div (f g : ℝ → ℝ) :
    (f / g) = fun t => f t / g t := by
  funext t
  exact Pi.div_apply f g t

/-- A far enough signed half-line has no zero and gives arbitrary C1
control of the actual logarithmic slope. -/
theorem exists_coneModeSlope_tail_control {s A B ε : ℝ}
    (hA : A ≠ 0) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ y : ℝ, T ≤ s * y →
      coneModePair s A B y ≠ 0 ∧
      ContDiffAt ℝ ∞ (coneModeSlope s (B / A)) y ∧
      coneModeSlope s (B / A) y =
        deriv (coneModePair s A B) y / coneModePair s A B y ∧
      |coneModeSlope s (B / A) y - s| ≤ ε ∧
      |deriv (coneModeSlope s (B / A)) y| ≤ ε := by
  let q : ℝ := B / A
  let z : ℝ → ℝ := fun t => q * exp (-2 * t)
  have hz : Tendsto z atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => exp (-2 * t)) atTop (𝓝 0) :=
      tendsto_exp_atBot.comp
        (Tendsto.const_mul_atTop_of_neg (by norm_num) tendsto_id)
    simpa only [z, mul_zero] using (tendsto_const_nhds (x := q)).mul he
  have hk : Tendsto (fun t => s * (1 - z t) / (1 + z t)) atTop (𝓝 s) := by
    have h := ((tendsto_const_nhds (x := s)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hz)).div
        ((tendsto_const_nhds (x := (1 : ℝ))).add hz) (by norm_num)
    simpa only [conePointwise_div, sub_zero, add_zero, mul_one, div_one] using h
  have hd : Tendsto (fun t => 4 * s ^ 2 * z t / (1 + z t) ^ 2)
      atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := 4 * s ^ 2)).mul hz).div
      (((tendsto_const_nhds (x := (1 : ℝ))).add hz).pow 2) (by norm_num)
    simpa only [conePointwise_div, mul_zero, add_zero, one_pow, zero_div] using h
  have hevent : ∀ᶠ t in atTop,
      |z t| < 1 / 2 ∧ |s * (1 - z t) / (1 + z t) - s| ≤ ε ∧
      |4 * s ^ 2 * z t / (1 + z t) ^ 2| ≤ ε := by
    filter_upwards [(Metric.tendsto_nhds.mp hz) (1 / 2) (by norm_num),
      (Metric.tendsto_nhds.mp hk) ε hε, (Metric.tendsto_nhds.mp hd) ε hε]
      with t ht hk' hd'
    exact ⟨by simpa only [Real.dist_eq, sub_zero] using ht,
      by simpa only [Real.dist_eq] using hk'.le,
      by simpa only [Real.dist_eq, sub_zero] using hd'.le⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨T, ?_⟩
  intro y hy
  have h := hT (s * y) hy
  have hratio : coneModeRatio s (B / A) y = z (s * y) := rfl
  have hden : 0 < 1 + coneModeRatio s (B / A) y := by
    rw [hratio]
    have hh := abs_lt.mp h.1
    linarith
  have hn : coneModePair s A B y ≠ 0 := by
    rw [coneModePair_factor hA y]
    exact mul_ne_zero (mul_ne_zero hA (exp_pos _).ne') hden.ne'
  refine ⟨hn, coneModeSlope_contDiffAt hden.ne',
    coneModeSlope_eq_logDerivative hA hden.ne', ?_, ?_⟩
  · simpa only [coneModeSlope, hratio] using h.2.1
  · rw [(hasDerivAt_coneModeSlope hden.ne').deriv, hratio]
    exact h.2.2

end ContinuousFlexibility.Radial
