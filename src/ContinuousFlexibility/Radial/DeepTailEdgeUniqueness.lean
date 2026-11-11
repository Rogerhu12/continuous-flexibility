import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniqueness on a deep-tail edge

A positive comparison solution excludes a nonzero solution with zero data
at both endpoints.  The argument uses the constant weighted Wronskian and
then the derivative of the quotient.  Only continuity up to the endpoints
and actual derivative identities in the open edge are needed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set

private theorem eq_endpoints_of_hasDerivAt_zero {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : f a = f b := by
  obtain ⟨x, hx, heq⟩ := exists_deriv_eq_slope f hab hc
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
  rw [(hd x hx).deriv] at heq
  have h := (eq_div_iff (sub_pos.mpr hab).ne').mp heq
  linarith

private theorem divergence_eq_zero_of_positive_solution_aux
    {a b Λ : ℝ} {p u du v dv : ℝ → ℝ} (hab : a < b)
    (hp : ContinuousOn p (Icc a b)) (hu : ContinuousOn u (Icc a b))
    (hdu : ContinuousOn du (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdv : ContinuousOn dv (Icc a b))
    (hp_pos : ∀ x ∈ Ioo a b, 0 < p x)
    (huD : ∀ x ∈ Ioo a b, HasDerivAt u (du x) x)
    (hvD : ∀ x ∈ Ioo a b, HasDerivAt v (dv x) x)
    (hpu : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y => p y * du y) (-(Λ * p x * u x)) x)
    (hpv : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y => p y * dv y) (-(Λ * p x * v x)) x)
    (hua : u a = 0) (hub : u b = 0) (hva : v a = 0)
    (hv_pos : ∀ x ∈ Ioc a b, 0 < v x) :
    ∀ x ∈ Icc a b, u x = 0 := by
  let W : ℝ → ℝ := fun x => (p x * du x) * v x - (p x * dv x) * u x
  have hWc : ContinuousOn W (Icc a b) :=
    ((hp.mul hdu).mul hv).sub ((hp.mul hdv).mul hu)
  have hWD : ∀ x ∈ Ioo a b, HasDerivAt W 0 x := by
    intro x hx
    have h := ((hpu x hx).mul (hvD x hx)).sub ((hpv x hx).mul (huD x hx))
    exact h.congr_deriv (by ring)
  have hWa : W a = 0 := by simp only [W, hua, hva, mul_zero, sub_zero]
  have hW : ∀ x ∈ Icc a b, W x = 0 := by
    intro x hx
    rcases lt_or_eq_of_le hx.1 with hax | hax
    · have heq : W a = W x := eq_endpoints_of_hasDerivAt_zero hax
        (hWc.mono (fun y hy => ⟨hy.1, hy.2.trans hx.2⟩))
        (fun y hy => hWD y ⟨hy.1, hy.2.trans_le hx.2⟩)
      exact heq.symm.trans hWa
    · simpa only [← hax] using hWa
  have hquot : ∀ x ∈ Ioo a b, HasDerivAt (fun y => u y / v y) 0 x := by
    intro x hx
    have hnum : du x * v x - u x * dv x = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (hp_pos x hx).ne'
      calc
        p x * (du x * v x - u x * dv x) = W x := by dsimp only [W]; ring
        _ = 0 := hW x ⟨hx.1.le, hx.2.le⟩
    apply ((huD x hx).fun_div (hvD x hx) (hv_pos x ⟨hx.1, hx.2.le⟩).ne').congr_deriv
    rw [hnum, zero_div]
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hax | hax
  · rcases lt_or_eq_of_le hx.2 with hxb | hxb
    · have hsub : Icc x b ⊆ Icc a b := fun y hy => ⟨hax.le.trans hy.1, hy.2⟩
      have hcont : ContinuousOn (fun y => u y / v y) (Icc x b) :=
        (hu.mono hsub).div (hv.mono hsub)
          (fun y hy => (hv_pos y ⟨hax.trans_le hy.1, hy.2⟩).ne')
      have heq := eq_endpoints_of_hasDerivAt_zero hxb hcont
        (fun y hy => hquot y ⟨hax.trans hy.1, hy.2⟩)
      have hzero : u x / v x = 0 := by simpa only [hub, zero_div] using heq
      exact (div_eq_zero_iff.mp hzero).resolve_right (hv_pos x ⟨hax, hx.2⟩).ne'
    · simpa only [hxb] using hub
  · simpa only [← hax] using hua

/-- A positive solution with a zero left endpoint excludes a nonzero
Dirichlet solution of the same divergence-form equation.  The derivatives
at the endpoints need only extend continuously from the edge. -/
theorem tailEdge_solution_eq_zero_of_positive_solution
    {a b Λ : ℝ} {p u v : ℝ → ℝ} (hab : a < b)
    (hp : ContinuousOn p (Icc a b)) (hu : ContinuousOn u (Icc a b))
    (hdu : ContinuousOn (deriv u) (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdv : ContinuousOn (deriv v) (Icc a b))
    (hp_pos : ∀ x ∈ Ioo a b, 0 < p x)
    (huD : ∀ x ∈ Ioo a b, HasDerivAt u (deriv u x) x)
    (hvD : ∀ x ∈ Ioo a b, HasDerivAt v (deriv v x) x)
    (hpu : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y => p y * deriv u y) (-(Λ * p x * u x)) x)
    (hpv : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y => p y * deriv v y) (-(Λ * p x * v x)) x)
    (hua : u a = 0) (hub : u b = 0) (hva : v a = 0)
    (hv_pos : ∀ x ∈ Ioc a b, 0 < v x) :
    ∀ x ∈ Icc a b, u x = 0 :=
  divergence_eq_zero_of_positive_solution_aux hab hp hu hdu hv hdv hp_pos
    huD hvD hpu hpv hua hub hva hv_pos

/-- Two actual solutions with the same two endpoint values coincide if
there is a positive comparison solution.  The proof subtracts their
derivative data, without demanding derivatives outside the closed edge. -/
theorem tailEdge_solutions_eq_of_positive_solution
    {a b Λ : ℝ} {p u₀ u₁ v : ℝ → ℝ} (hab : a < b)
    (hp : ContinuousOn p (Icc a b))
    (hu₀ : ContinuousOn u₀ (Icc a b)) (hdu₀ : ContinuousOn (deriv u₀) (Icc a b))
    (hu₁ : ContinuousOn u₁ (Icc a b)) (hdu₁ : ContinuousOn (deriv u₁) (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hdv : ContinuousOn (deriv v) (Icc a b))
    (hp_pos : ∀ x ∈ Ioo a b, 0 < p x)
    (hu₀D : ∀ x ∈ Ioo a b, HasDerivAt u₀ (deriv u₀ x) x)
    (hu₁D : ∀ x ∈ Ioo a b, HasDerivAt u₁ (deriv u₁ x) x)
    (hvD : ∀ x ∈ Ioo a b, HasDerivAt v (deriv v x) x)
    (hpu₀ : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y => p y * deriv u₀ y) (-(Λ * p x * u₀ x)) x)
    (hpu₁ : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y => p y * deriv u₁ y) (-(Λ * p x * u₁ x)) x)
    (hpv : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y => p y * deriv v y) (-(Λ * p x * v x)) x)
    (hua : u₀ a = u₁ a) (hub : u₀ b = u₁ b) (hva : v a = 0)
    (hv_pos : ∀ x ∈ Ioc a b, 0 < v x) :
    ∀ x ∈ Icc a b, u₀ x = u₁ x := by
  have hflux : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y => p y * (deriv u₀ y - deriv u₁ y))
        (-(Λ * p x * (u₀ x - u₁ x))) x := by
    intro x hx
    convert (hpu₀ x hx).sub (hpu₁ x hx) using 1
    · funext y
      ring
    · ring
  have hz := divergence_eq_zero_of_positive_solution_aux hab hp
    (hu₀.sub hu₁) (hdu₀.sub hdu₁) hv hdv hp_pos
    (fun x hx => (hu₀D x hx).sub (hu₁D x hx)) hvD hflux hpv
    (sub_eq_zero.mpr hua) (sub_eq_zero.mpr hub) hva hv_pos
  intro x hx
  exact sub_eq_zero.mp (hz x hx)

end ContinuousFlexibility.Radial
