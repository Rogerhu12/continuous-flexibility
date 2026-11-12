import ContinuousFlexibility.Analysis.N06RootRegularTransport
import ContinuousFlexibility.Analysis.N06RootBoundaryJetAlgebra

/-!
# Actual root boundary jets from the physical transport equations

The regular transport system determines the next even jet and the
current odd jet. The positive factor n + 3/2 is inverted explicitly.
Every term is a finite Leibniz polynomial in the physical coefficient
trace jets and already determined even and odd trace functions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem n06_even_boundary_recursion_of_regular_equation
    {e f g : ℝ → ℝ} (he : ContDiff ℝ ∞ e)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (heq : ∀ x ∈ Icc (0 : ℝ) 1, deriv e x = -f x + x ^ 2 * g x)
    (n : ℕ) :
    iteratedDeriv (n + 1) e 0 = -iteratedDeriv n f 0 +
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * iteratedDeriv (n - 2) g 0 := by
  have he' : ContDiff ℝ ∞ (deriv e) := (contDiff_infty_iff_deriv.mp he).2
  have h := n06_iteratedDeriv_congr_closed_interval
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    he'.contDiffAt (hf.neg.add ((contDiff_id.pow 2).mul hg)).contDiffAt heq n
  change iteratedDeriv n (deriv e) 0 =
    iteratedDeriv n (fun x : ℝ => -f x + x ^ 2 * g x) 0 at h
  have hneg : ContDiffAt ℝ (n : ℕ) (fun x : ℝ => -f x) 0 :=
    hf.neg.contDiffAt.of_le (by simp)
  have hsq : ContDiffAt ℝ (n : ℕ) (fun x : ℝ => x ^ 2 * g x) 0 :=
    ((contDiffAt_id.pow 2).mul hg.contDiffAt).of_le (by simp)
  rw [← iteratedDeriv_succ', iteratedDeriv_fun_add hneg hsq,
    iteratedDeriv_fun_neg,
    n06_iteratedDeriv_coord_sq_mul_zero hg.contDiffAt] at h
  exact h

private theorem n06_odd_boundary_recursion_of_regular_equation
    {o f g : ℝ → ℝ} (ho : ContDiff ℝ ∞ o)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a : ℝ)
    (heq : ∀ x ∈ Icc (0 : ℝ) 1,
      x * deriv o x + a * o x = f x - x * g x)
    (n : ℕ) :
    ((n : ℝ) + a) * iteratedDeriv n o 0 =
      iteratedDeriv n f 0 - (n : ℝ) * iteratedDeriv (n - 1) g 0 := by
  have ho' : ContDiff ℝ ∞ (deriv o) := (contDiff_infty_iff_deriv.mp ho).2
  have h := n06_iteratedDeriv_congr_closed_interval
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    ((contDiff_id.mul ho').add (contDiff_const.mul ho)).contDiffAt
    (hf.sub (contDiff_id.mul hg)).contDiffAt heq n
  change iteratedDeriv n (fun x : ℝ => x * deriv o x + a * o x) 0 =
    iteratedDeriv n (fun x : ℝ => f x - x * g x) 0 at h
  have hxg : ContDiffAt ℝ (n : ℕ) (fun x : ℝ => x * g x) 0 :=
    (contDiffAt_id.mul hg.contDiffAt).of_le (by simp)
  rw [n06_iteratedDeriv_euler_zero ho,
    iteratedDeriv_fun_sub (hf.contDiffAt.of_le (by simp)) hxg,
    n06_iteratedDeriv_coord_mul_zero hg.contDiffAt] at h
  exact h

namespace N04bRootCoordinateProperties

variable {d c₀ : PolarPoint → ℝ} {β : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
  {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
  (P : N04bRootCoordinateProperties d c₀ β Φ R σ G)

include P

theorem n06_even_boundary_jet_zero (θ : ℝ) :
    radialBoundaryJet (extendedRootEven G) 0 0 θ = β θ := by
  simp only [radialBoundaryJet, iteratedDeriv_zero,
    extendedRootEven_of_nonneg G (p := (0, θ)) (le_refl (0 : ℝ)),
    rootEven_zero, P.zero_section]

theorem n06_odd_boundary_jet_zero (θ : ℝ) :
    radialBoundaryJet (extendedRootOddCoefficient G) 0 0 θ =
      ((2 : ℝ) / 3) * c₀ (0, θ) * deriv β θ := by
  simp only [radialBoundaryJet, iteratedDeriv_zero,
    extendedRootOddCoefficient_of_nonneg G (p := (0, θ)) (le_refl (0 : ℝ)), P.odd_zero]

/-- The next actual even boundary trace is a finite expression in
physical coefficient jets and lower even and odd trace functions. -/
theorem n06_even_boundary_recursion
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀) (n : ℕ) (θ : ℝ) :
    radialBoundaryJet (extendedRootEven G) 0 (n + 1) θ =
      -n06RootJetProduct (radialBoundaryJet d 0)
        (radialBoundaryJet (extendedRootEven G) 0) n θ +
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
        n06RootJetProduct (radialBoundaryJet c₀ 0)
          (radialBoundaryJet (extendedRootOddCoefficient G) 0) (n - 2) θ := by
  have hE := P.n06_extendedEven_smooth
  have hO := P.n06_extendedOdd_smooth
  have hEt := contDiff_cylinder_angularPartial hE
  have hOt := contDiff_cylinder_angularPartial hO
  have hline : ContDiff ℝ ∞ (fun x : ℝ => (x, θ)) :=
    contDiff_id.prodMk contDiff_const
  have heq (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      deriv (fun r => extendedRootEven G (r, θ)) x =
        -(d (x, θ) * angularPartial (extendedRootEven G) (x, θ)) +
        x ^ 2 * (c₀ (x, θ) * angularPartial (extendedRootOddCoefficient G) (x, θ)) := by
    rw [deriv_cylinder_radial_slice (hE.differentiable (by simp))]
    simpa only [neg_mul, mul_assoc] using
      (P.n06_regular_transport_nonnegative hd hc₀ hx.1 θ).1
  have h := n06_even_boundary_recursion_of_regular_equation
    (hE.comp hline) ((hd.mul hEt).comp hline) ((hc₀.mul hOt).comp hline) heq n
  change radialBoundaryJet (extendedRootEven G) 0 (n + 1) θ =
    -radialBoundaryJet (fun p => d p * angularPartial (extendedRootEven G) p) 0 n θ +
    (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
      radialBoundaryJet (fun p => c₀ p * angularPartial (extendedRootOddCoefficient G) p)
        0 (n - 2) θ at h
  rw [n06_radialBoundaryJet_mul_angularPartial hd hE,
    n06_radialBoundaryJet_mul_angularPartial hc₀ hO] at h
  exact h

/-- The actual odd trace is multiplied by the nonzero number n + 3/2.
Its right side contains the even trace of order at most n and odd traces
of order at most n - 1. -/
theorem n06_odd_boundary_recursion
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀) (n : ℕ) (θ : ℝ) :
    ((n : ℝ) + (3 : ℝ) / 2) *
        radialBoundaryJet (extendedRootOddCoefficient G) 0 n θ =
      n06RootJetProduct (radialBoundaryJet c₀ 0)
        (radialBoundaryJet (extendedRootEven G) 0) n θ -
      (n : ℝ) * n06RootJetProduct (radialBoundaryJet d 0)
        (radialBoundaryJet (extendedRootOddCoefficient G) 0) (n - 1) θ := by
  have hE := P.n06_extendedEven_smooth
  have hO := P.n06_extendedOdd_smooth
  have hEt := contDiff_cylinder_angularPartial hE
  have hOt := contDiff_cylinder_angularPartial hO
  have hline : ContDiff ℝ ∞ (fun x : ℝ => (x, θ)) :=
    contDiff_id.prodMk contDiff_const
  have heq (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      x * deriv (fun r => extendedRootOddCoefficient G (r, θ)) x +
          ((3 : ℝ) / 2) * extendedRootOddCoefficient G (x, θ) =
        c₀ (x, θ) * angularPartial (extendedRootEven G) (x, θ) -
          x * (d (x, θ) * angularPartial (extendedRootOddCoefficient G) (x, θ)) := by
    rw [deriv_cylinder_radial_slice (hO.differentiable (by simp))]
    simpa only [mul_assoc] using
      (P.n06_regular_transport_nonnegative hd hc₀ hx.1 θ).2
  have h := n06_odd_boundary_recursion_of_regular_equation
    (hO.comp hline) ((hc₀.mul hEt).comp hline) ((hd.mul hOt).comp hline)
    ((3 : ℝ) / 2) heq n
  change ((n : ℝ) + (3 : ℝ) / 2) *
      radialBoundaryJet (extendedRootOddCoefficient G) 0 n θ =
    radialBoundaryJet (fun p => c₀ p * angularPartial (extendedRootEven G) p) 0 n θ -
      (n : ℝ) * radialBoundaryJet
        (fun p => d p * angularPartial (extendedRootOddCoefficient G) p) 0 (n - 1) θ at h
  rw [n06_radialBoundaryJet_mul_angularPartial hc₀ hE,
    n06_radialBoundaryJet_mul_angularPartial hd hO] at h
  exact h

theorem n06_odd_boundary_recursion_solved
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀) (n : ℕ) (θ : ℝ) :
    radialBoundaryJet (extendedRootOddCoefficient G) 0 n θ =
      (n06RootJetProduct (radialBoundaryJet c₀ 0)
        (radialBoundaryJet (extendedRootEven G) 0) n θ -
      (n : ℝ) * n06RootJetProduct (radialBoundaryJet d 0)
        (radialBoundaryJet (extendedRootOddCoefficient G) 0) (n - 1) θ) /
      ((n : ℝ) + (3 : ℝ) / 2) := by
  have hden : (0 : ℝ) < (n : ℝ) + (3 : ℝ) / 2 := by positivity
  apply (eq_div_iff hden.ne').mpr
  simpa only [mul_comm] using P.n06_odd_boundary_recursion hd hc₀ n θ

end N04bRootCoordinateProperties

end ContinuousFlexibility.Analysis
