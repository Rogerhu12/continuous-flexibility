import ContinuousFlexibility.Radial.SeedLogSystem
import ContinuousFlexibility.Radial.LogSlopeConnector

/-!
# Smooth finite radial continuation through a positive profile

The logarithmic Cauchy system produces actual solutions of the radial Jacobi
equation. Interval uniqueness compares this continuation with an original
solution on an outward collar, including an entry point at the end of that
collar.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

def seedRadialProfile (H : ℝ → ℝ) (r : ℝ) : ℝ := exp (H (log r))

def seedRadialHeight (v : ℝ → ℝ) (r : ℝ) : ℝ := v (log r)

theorem seedRadialProfile_pos (H : ℝ → ℝ) (r : ℝ) :
    0 < seedRadialProfile H r := Real.exp_pos _

theorem seedRadialProfile_contDiffOn {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiffOn ℝ ∞ (seedRadialProfile H) (Ioi 0) :=
  (hH.comp_contDiffOn (Real.contDiffOn_log.mono Ioi_subset_compl_zero)).exp

theorem seedRadialHeight_contDiffOn {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) :
    ContDiffOn ℝ ∞ (seedRadialHeight v) (Ioi 0) :=
  hv.comp_contDiffOn (Real.contDiffOn_log.mono Ioi_subset_compl_zero)

theorem hasDerivAt_seedRadialProfile {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (seedRadialProfile H)
      (seedRadialProfile H r * deriv H (log r) / r) r := by
  have h := (((hH.differentiable (by simp) (log r)).hasDerivAt).comp r
    (Real.hasDerivAt_log hr.ne')).exp
  exact h.congr_deriv (by simp only [seedRadialProfile, Function.comp_apply]; ring)

theorem hasDerivAt_seedRadialHeight {v : ℝ → ℝ} {r d : ℝ}
    (hv : HasDerivAt v d (log r)) (hr : 0 < r) :
    HasDerivAt (seedRadialHeight v) (d / r) r := by
  exact (hv.comp r (Real.hasDerivAt_log hr.ne')).congr_deriv (by ring)

/-- The logarithmic system implies the actual divergence-form radial equation. -/
theorem radialJacobi_seedRadialHeight {H v z : ℝ → ℝ} {J : Set ℝ}
    (hH : ContDiff ℝ ∞ H) (hJ : IsOpen J)
    (hs : ∀ y ∈ J, HasDerivAt v (z y) y ∧
      HasDerivAt z ((1 - deriv H y) * z y + 4 * deriv H y * v y) y)
    {r : ℝ} (hr : 0 < r) (hlog : log r ∈ J) :
    radialJacobi 4 (seedRadialProfile H) (seedRadialHeight v) r = 0 := by
  have hlogd := Real.hasDerivAt_log hr.ne'
  have hloc : ∀ᶠ t in 𝓝 r, log t ∈ J :=
    hlogd.continuousAt.tendsto.eventually (hJ.mem_nhds hlog)
  have heq : (fun t => seedRadialProfile H t * deriv (seedRadialHeight v) t)
      =ᶠ[𝓝 r] (fun t => seedRadialProfile H t * (z (log t) / t)) := by
    filter_upwards [Ioi_mem_nhds hr, hloc] with t ht hJt
    rw [(hasDerivAt_seedRadialHeight (hs (log t) hJt).1 ht).deriv]
  have hd := ((hasDerivAt_seedRadialProfile hH hr).mul
    (((hs (log r) hlog).2.comp r hlogd).div (hasDerivAt_id r) hr.ne')).congr_of_eventuallyEq heq
  unfold radialJacobi
  rw [hd.deriv, (hasDerivAt_seedRadialProfile hH hr).deriv]
  simp only [seedRadialHeight, Function.comp_apply, Pi.div_apply, Pi.mul_apply, Pi.add_apply]
  field_simp [hr.ne']
  ring

/-- Conversely, an actual radial solution has the stated logarithmic Cauchy system. -/
theorem seedRadial_logSystem {H u : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) {y : ℝ}
    (hu : DifferentiableAt ℝ u (exp y))
    (hu' : DifferentiableAt ℝ (deriv u) (exp y))
    (hODE : radialJacobi 4 (seedRadialProfile H) u (exp y) = 0) :
    HasDerivAt (fun t => u (exp t)) (exp y * deriv u (exp y)) y ∧
    HasDerivAt (fun t => exp t * deriv u (exp t))
      ((1 - deriv H y) * (exp y * deriv u (exp y)) +
        4 * deriv H y * u (exp y)) y := by
  have hE := Real.hasDerivAt_exp y
  refine ⟨(hu.hasDerivAt.comp y hE).congr_deriv (by ring), ?_⟩
  have hd := hE.mul (hu'.hasDerivAt.comp y hE)
  have hw := hasDerivAt_seedRadialProfile hH (Real.exp_pos y)
  have hflux := hw.mul hu'.hasDerivAt
  change HasDerivAt (fun r => seedRadialProfile H r * deriv u r) _ (exp y) at hflux
  have hEq := hODE
  unfold radialJacobi at hEq
  rw [hflux.deriv, hw.deriv, Real.log_exp] at hEq
  have hEne : exp y ≠ 0 := (Real.exp_pos y).ne'
  field_simp [hEne] at hEq
  apply hd.congr_deriv
  have hz : seedRadialProfile H (exp y) *
      (exp y * deriv u (exp y) + exp y * (deriv (deriv u) (exp y) * exp y) -
        ((1 - deriv H y) * (exp y * deriv u (exp y)) +
          4 * deriv H y * u (exp y))) = 0 := by
    linear_combination hEq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (seedRadialProfile_pos H (exp y)).ne')

/-- Uniqueness for actual radial solutions on a finite log-radius interval.
The initial point may be either endpoint, which supplies outward collar matching. -/
theorem seedRadial_eqOn_exp {H u v : ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    {a b y₀ : ℝ} (hy₀ : y₀ ∈ Icc a b)
    (hu : ∀ y ∈ Icc a b, DifferentiableAt ℝ u (exp y) ∧
      DifferentiableAt ℝ (deriv u) (exp y))
    (hv : ∀ y ∈ Icc a b, DifferentiableAt ℝ v (exp y) ∧
      DifferentiableAt ℝ (deriv v) (exp y))
    (huODE : ∀ y ∈ Icc a b, radialJacobi 4 (seedRadialProfile H) u (exp y) = 0)
    (hvODE : ∀ y ∈ Icc a b, radialJacobi 4 (seedRadialProfile H) v (exp y) = 0)
    (h₀ : u (exp y₀) = v (exp y₀))
    (h₁ : deriv u (exp y₀) = deriv v (exp y₀)) :
    ∀ y ∈ Icc a b, u (exp y) = v (exp y) ∧
      deriv u (exp y) = deriv v (exp y) := by
  have he := seedLogSystem_eqOn
    (contDiff_infty_iff_deriv.mp hH).2.continuous.continuousOn hy₀
    (fun y hy => seedRadial_logSystem hH (hu y hy).1 (hu y hy).2 (huODE y hy))
    (fun y hy => seedRadial_logSystem hH (hv y hy).1 (hv y hy).2 (hvODE y hy))
    h₀ (congrArg (fun t : ℝ => exp y₀ * t) h₁)
  intro y hy
  exact ⟨he.1 hy, mul_left_cancel₀ (Real.exp_pos y).ne' (he.2 hy)⟩

/-- Changing the profile on the complement of a neighborhood does not change the equation. -/
theorem radialJacobi_eq_of_profile_germ {w W u : ℝ → ℝ} {J r : ℝ}
    (h : w =ᶠ[𝓝 r] W) :
    radialJacobi J w u r = radialJacobi J W u r := by
  have hflux : (fun t => w t * deriv u t) =ᶠ[𝓝 r] (fun t => W t * deriv u t) := by
    filter_upwards [h] with t ht
    rw [ht]
  simp only [radialJacobi, hflux.deriv_eq, h.deriv_eq]

/-- A finite smooth radial continuation with its original Cauchy state. -/
structure SeedRadialContinuation (H : ℝ → ℝ) (a b y₀ A B : ℝ) where
  height : ℝ → ℝ
  smooth : ContDiffOn ℝ ∞ height (Ioi 0)
  value : height (exp y₀) = A
  deriv_value : deriv height (exp y₀) = B
  homogeneous : ∀ r, 0 < r → log r ∈ Ioo (a - 1) (b + 1) →
    radialJacobi 4 (seedRadialProfile H) height r = 0
  nonzero : (A, B) ≠ (0, 0) → ∀ r, 0 < r → log r ∈ Icc a b →
    (height r, deriv height r) ≠ (0, 0)

theorem exists_seedRadialContinuation {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    {a b y₀ : ℝ} (hy₀ : y₀ ∈ Icc a b) (A B : ℝ) :
    Nonempty (SeedRadialContinuation H a b y₀ A B) := by
  obtain ⟨v, z, hvs, hzs, hv₀, hz₀, hd⟩ :=
    exists_seedLogSystem hH hy₀ A (exp y₀ * B)
  have hsub : Icc a b ⊆ Ioo (a - 1) (b + 1) := by
    intro y hy
    exact ⟨by linarith only [hy.1], by linarith only [hy.2]⟩
  have hvder : deriv (seedRadialHeight v) (exp y₀) = B := by
    have hlog : log (exp y₀) ∈ Ioo (a - 1) (b + 1) := by
      simpa only [Real.log_exp] using hsub hy₀
    rw [(hasDerivAt_seedRadialHeight (hd _ hlog).1 (Real.exp_pos y₀)).deriv,
      Real.log_exp, hz₀]
    field_simp [(Real.exp_pos y₀).ne']
  refine ⟨{
    height := seedRadialHeight v
    smooth := seedRadialHeight_contDiffOn hvs
    value := by simpa only [seedRadialHeight, Real.log_exp] using hv₀
    deriv_value := hvder
    homogeneous := fun r hr hlog => radialJacobi_seedRadialHeight hH isOpen_Ioo hd hr hlog
    nonzero := ?_
  }⟩
  intro hAB r hr hlog hz
  have hinit : (v y₀, z y₀) ≠ (0, 0) := by
    rw [hv₀, hz₀]
    intro he
    apply hAB
    apply Prod.ext (congrArg Prod.fst he)
    exact (mul_eq_zero.mp (congrArg Prod.snd he)).resolve_left (Real.exp_pos y₀).ne'
  have hne := seedLogSystem_state_ne_zero
    (contDiff_infty_iff_deriv.mp hH).2.continuous.continuousOn hy₀
    (fun y hy => hd y (hsub hy)) hinit (log r) hlog
  apply hne
  have hu0 : v (log r) = 0 := congrArg Prod.fst hz
  have hz0 : z (log r) = 0 := by
    have he : deriv (seedRadialHeight v) r = 0 := congrArg Prod.snd hz
    rw [(hasDerivAt_seedRadialHeight (hd _ (hsub hlog)).1 hr).deriv] at he
    exact (div_eq_zero_iff.mp he).resolve_right hr.ne'
  exact Prod.ext hu0 hz0

end ContinuousFlexibility.Radial
