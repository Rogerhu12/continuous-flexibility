import ContinuousFlexibility.Radial.MorseRadiusODE

/-!
# Finite continuation of the logarithmic radial system

A scalar gauge reduces the logarithmic second-mode equation to the arbitrary
smooth second-order system. The first-order formulation also supplies interval
uniqueness and preservation of a nonzero Cauchy state.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff NNReal

/-- The scalar gauge removing the first derivative from the log-radius equation. -/
def seedLogGauge (H : ℝ → ℝ) (y : ℝ) : ℝ := (y - H y) / 2

def seedLogGaugeSlope (H : ℝ → ℝ) (y : ℝ) : ℝ := (1 - deriv H y) / 2

def seedLogPotential (H : ℝ → ℝ) (y : ℝ) : ℝ :=
  deriv (seedLogGaugeSlope H) y - (seedLogGaugeSlope H y) ^ 2 - 4 * deriv H y

theorem contDiff_seedLogGauge {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (seedLogGauge H) :=
  (contDiff_id.sub hH).div_const 2

theorem contDiff_seedLogGaugeSlope {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (seedLogGaugeSlope H) :=
  (contDiff_const.sub (contDiff_infty_iff_deriv.mp hH).2).div_const 2

theorem contDiff_seedLogPotential {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (seedLogPotential H) := by
  have hG := contDiff_seedLogGaugeSlope hH
  exact ((contDiff_infty_iff_deriv.mp hG).2.sub (hG.pow 2)).sub
    (contDiff_const.mul (contDiff_infty_iff_deriv.mp hH).2)

theorem hasDerivAt_seedLogGauge {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) (y : ℝ) :
    HasDerivAt (seedLogGauge H) (seedLogGaugeSlope H y) y :=
  ((hasDerivAt_id y).sub (hH.differentiable (by simp) y).hasDerivAt).div_const 2

/-- The gauge acts on both coordinates of the Cauchy state. -/
theorem seedLogGauge_system {H r v : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) {y : ℝ}
    (hr : HasDerivAt r (v y) y)
    (hv : HasDerivAt v (-seedLogPotential H y * r y) y) :
    HasDerivAt (fun t => exp (seedLogGauge H t) * r t)
      (exp (seedLogGauge H y) * (v y + seedLogGaugeSlope H y * r y)) y ∧
    HasDerivAt (fun t => exp (seedLogGauge H t) *
      (v t + seedLogGaugeSlope H t * r t))
      ((1 - deriv H y) * (exp (seedLogGauge H y) *
        (v y + seedLogGaugeSlope H y * r y)) +
        4 * deriv H y * (exp (seedLogGauge H y) * r y)) y := by
  have hE := (hasDerivAt_seedLogGauge hH y).exp
  have hG := ((contDiff_seedLogGaugeSlope hH).differentiable (by simp) y).hasDerivAt
  refine ⟨(hE.mul hr).congr_deriv (by ring), ?_⟩
  apply (hE.mul (hv.add (hG.mul hr))).congr_deriv
  simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  have htwo : 1 - deriv H y = 2 * seedLogGaugeSlope H y := by
    simp only [seedLogGaugeSlope]
    ring
  rw [htwo]
  simp only [seedLogPotential]
  ring

/-- Arbitrary Cauchy data for the actual logarithmic second-mode system. -/
theorem exists_seedLogSystem {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    {a b y₀ : ℝ} (hy₀ : y₀ ∈ Icc a b) (A B : ℝ) :
    ∃ u z : ℝ → ℝ, ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ z ∧
      u y₀ = A ∧ z y₀ = B ∧
      ∀ y ∈ Ioo (a - 1) (b + 1), HasDerivAt u (z y) y ∧
        HasDerivAt z ((1 - deriv H y) * z y + 4 * deriv H y * u y) y := by
  obtain ⟨r, v, hrs, hvs, hr₀, hv₀, hd⟩ :=
    exists_smoothSecondOrderSystem (contDiff_seedLogPotential hH) hy₀
      (exp (-seedLogGauge H y₀) * A)
      (exp (-seedLogGauge H y₀) * (B - seedLogGaugeSlope H y₀ * A))
  let u : ℝ → ℝ := fun y => exp (seedLogGauge H y) * r y
  let z : ℝ → ℝ := fun y => exp (seedLogGauge H y) *
    (v y + seedLogGaugeSlope H y * r y)
  have hc : exp (seedLogGauge H y₀) * exp (-seedLogGauge H y₀) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hu₀ : u y₀ = A := by
    dsimp only [u]
    rw [hr₀]
    calc
      _ = (exp (seedLogGauge H y₀) * exp (-seedLogGauge H y₀)) * A := by ring
      _ = A := by rw [hc, one_mul]
  have hz₀ : z y₀ = B := by
    dsimp only [z]
    rw [hr₀, hv₀]
    calc
      _ = (exp (seedLogGauge H y₀) * exp (-seedLogGauge H y₀)) * B := by ring
      _ = B := by rw [hc, one_mul]
  refine ⟨u, z, (contDiff_seedLogGauge hH).exp.mul hrs,
    (contDiff_seedLogGauge hH).exp.mul
      (hvs.add ((contDiff_seedLogGaugeSlope hH).mul hrs)), hu₀, hz₀, ?_⟩
  intro y hy
  exact seedLogGauge_system hH (hd y hy).1 (hd y hy).2

private def seedLogField (p : ℝ → ℝ) (y : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, (1 - p y) * z.2 + 4 * p y * z.1)

private theorem seedLogField_lipschitz {p : ℝ → ℝ} {y : ℝ} {K : ℝ≥0}
    (hK : 1 ≤ (K : ℝ)) (hp : ‖1 - p y‖ + ‖4 * p y‖ ≤ (K : ℝ)) :
    LipschitzWith K (seedLogField p y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [dist_eq_norm, seedLogField, Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
  have hM : 0 ≤ max ‖x.1 - z.1‖ ‖x.2 - z.2‖ :=
    (norm_nonneg _).trans (le_max_left _ _)
  refine max_le ((le_max_right _ _).trans (le_mul_of_one_le_left hM hK)) ?_
  have heq : (1 - p y) * x.2 + 4 * p y * x.1 -
      ((1 - p y) * z.2 + 4 * p y * z.1) =
      (1 - p y) * (x.2 - z.2) + (4 * p y) * (x.1 - z.1) := by ring
  rw [heq]
  calc
    _ ≤ ‖(1 - p y) * (x.2 - z.2)‖ + ‖(4 * p y) * (x.1 - z.1)‖ :=
      norm_add_le _ _
    _ = ‖1 - p y‖ * ‖x.2 - z.2‖ + ‖4 * p y‖ * ‖x.1 - z.1‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖1 - p y‖ * max ‖x.1 - z.1‖ ‖x.2 - z.2‖ +
        ‖4 * p y‖ * max ‖x.1 - z.1‖ ‖x.2 - z.2‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _))
    _ = (‖1 - p y‖ + ‖4 * p y‖) * max ‖x.1 - z.1‖ ‖x.2 - z.2‖ := by ring
    _ ≤ (K : ℝ) * max ‖x.1 - z.1‖ ‖x.2 - z.2‖ :=
      mul_le_mul_of_nonneg_right hp hM

/-- Cauchy uniqueness on a closed interval, including initial data at either end. -/
theorem seedLogSystem_eqOn {p u z v ξ : ℝ → ℝ} {a b y₀ : ℝ}
    (hp : ContinuousOn p (Icc a b)) (hy₀ : y₀ ∈ Icc a b)
    (hu : ∀ y ∈ Icc a b, HasDerivAt u (z y) y ∧
      HasDerivAt z ((1 - p y) * z y + 4 * p y * u y) y)
    (hv : ∀ y ∈ Icc a b, HasDerivAt v (ξ y) y ∧
      HasDerivAt ξ ((1 - p y) * ξ y + 4 * p y * v y) y)
    (h₀ : u y₀ = v y₀) (h₁ : z y₀ = ξ y₀) :
    EqOn u v (Icc a b) ∧ EqOn z ξ (Icc a b) := by
  let U : ℝ → ℝ × ℝ := fun y => (u y, z y)
  let V : ℝ → ℝ × ℝ := fun y => (v y, ξ y)
  have hUd (y : ℝ) (hy : y ∈ Icc a b) :
      HasDerivAt U (seedLogField p y (U y)) y :=
    (hu y hy).1.prodMk (hu y hy).2
  have hVd (y : ℝ) (hy : y ∈ Icc a b) :
      HasDerivAt V (seedLogField p y (V y)) y :=
    (hv y hy).1.prodMk (hv y hy).2
  have hc : ContinuousOn (fun y => ‖1 - p y‖ + ‖4 * p y‖) (Icc a b) :=
    (continuousOn_const.sub hp).norm.add (continuousOn_const.mul hp).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hc
  let K : ℝ≥0 := ⟨max 1 C, zero_le_one.trans (le_max_left _ _)⟩
  have hLip (y : ℝ) (hy : y ∈ Icc a b) :
      LipschitzWith K (seedLogField p y) := by
    apply seedLogField_lipschitz (le_max_left _ _)
    exact (le_abs_self _).trans ((hC y hy).trans (le_max_right _ _))
  have hstart : U y₀ = V y₀ := Prod.ext h₀ h₁
  have hleft : Icc a y₀ ⊆ Icc a b := Icc_subset_Icc_right hy₀.2
  have hright : Icc y₀ b ⊆ Icc a b := Icc_subset_Icc_left hy₀.1
  have hL := ODE_solution_unique_of_mem_Icc_left
    (v := seedLogField p) (s := fun _ => univ) (f := U) (g := V) (a := a) (b := y₀)
    (fun y hy => (hLip y (hleft (Ioc_subset_Icc_self hy))).lipschitzOnWith)
    ((HasDerivAt.continuousOn hUd).mono hleft)
    (fun y hy => (hUd y (hleft (Ioc_subset_Icc_self hy))).hasDerivWithinAt)
    (fun _ _ => mem_univ _)
    ((HasDerivAt.continuousOn hVd).mono hleft)
    (fun y hy => (hVd y (hleft (Ioc_subset_Icc_self hy))).hasDerivWithinAt)
    (fun _ _ => mem_univ _) hstart
  have hR := ODE_solution_unique_of_mem_Icc_right
    (v := seedLogField p) (s := fun _ => univ) (f := U) (g := V) (a := y₀) (b := b)
    (fun y hy => (hLip y (hright (Ico_subset_Icc_self hy))).lipschitzOnWith)
    ((HasDerivAt.continuousOn hUd).mono hright)
    (fun y hy => (hUd y (hright (Ico_subset_Icc_self hy))).hasDerivWithinAt)
    (fun _ _ => mem_univ _)
    ((HasDerivAt.continuousOn hVd).mono hright)
    (fun y hy => (hVd y (hright (Ico_subset_Icc_self hy))).hasDerivWithinAt)
    (fun _ _ => mem_univ _) hstart
  have he : EqOn U V (Icc a b) := by
    intro y hy
    by_cases h : y ≤ y₀
    · exact hL ⟨hy.1, h⟩
    · exact hR ⟨le_of_lt (lt_of_not_ge h), hy.2⟩
  exact ⟨fun y hy => congrArg Prod.fst (he hy), fun y hy => congrArg Prod.snd (he hy)⟩

/-- A nonzero logarithmic Cauchy state cannot become the zero state. -/
theorem seedLogSystem_state_ne_zero {p u z : ℝ → ℝ} {a b y₀ : ℝ}
    (hp : ContinuousOn p (Icc a b)) (hy₀ : y₀ ∈ Icc a b)
    (hu : ∀ y ∈ Icc a b, HasDerivAt u (z y) y ∧
      HasDerivAt z ((1 - p y) * z y + 4 * p y * u y) y)
    (h₀ : (u y₀, z y₀) ≠ (0, 0)) :
    ∀ y ∈ Icc a b, (u y, z y) ≠ (0, 0) := by
  intro y hy hz
  have hzero : ∀ t ∈ Icc a b,
      HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t ∧
        HasDerivAt (fun _ : ℝ => (0 : ℝ)) ((1 - p t) * 0 + 4 * p t * 0) t := by
    intro t ht
    simpa only [mul_zero, add_zero] using
      And.intro (hasDerivAt_const t (0 : ℝ)) (hasDerivAt_const t (0 : ℝ))
  have he := seedLogSystem_eqOn hp hy hu hzero
    (congrArg Prod.fst hz) (congrArg Prod.snd hz)
  exact h₀ (Prod.ext (he.1 hy₀) (he.2 hy₀))

end ContinuousFlexibility.Radial
