import ContinuousFlexibility.Analysis.N07bReferenceGraphFromDecay
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual symmetries of the reference forcing

Periodicity and reflection pass through the actual one-dimensional
derivatives defining the radial expression. These identities also hold
for the totalized derivative, so no extra regularity premise is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

private theorem n07b_deriv_periodic {f : ℝ → ℝ} {c : ℝ}
    (hf : Function.Periodic f c) : Function.Periodic (deriv f) c := by
  intro x
  have heq : (fun y => f (y + c)) = f := funext hf
  rw [← deriv_comp_add_const f c x, heq]

private theorem n07b_second_deriv_even {f : ℝ → ℝ}
    (hf : ∀ θ, f (-θ) = f θ) (θ : ℝ) :
    deriv (deriv f) (-θ) = deriv (deriv f) θ := by
  have heq : (fun y => f (-y)) = f := funext hf
  have h := iteratedDeriv_comp_neg 2 f θ
  rw [heq] at h
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, neg_one_sq, one_smul] using h.symm

theorem n07b_radialPDE_periodic (w : ℝ → ℝ) {u : PolarPoint → ℝ}
    (hu : Function.Periodic u (0, Real.pi)) :
    Function.Periodic
      (fun p : PolarPoint => radialPDE w (fun r θ => u (r, θ)) p.1 p.2) (0, Real.pi) := by
  have hperiod (r : ℝ) : Function.Periodic (fun θ => u (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hu (r, θ)
  intro p
  rcases p with ⟨r, θ⟩
  have hslice : (fun t => u (t, θ + Real.pi)) = fun t => u (t, θ) :=
    funext (fun t => hperiod t θ)
  have hθ := n07b_deriv_periodic (n07b_deriv_periodic (hperiod r)) θ
  simp only [Prod.mk_add_mk, add_zero, radialPDE, hslice, hθ]

theorem n07b_radialPDE_even (w : ℝ → ℝ) {u : PolarPoint → ℝ}
    (hu : ∀ r θ, u (r, -θ) = u (r, θ)) :
    ∀ r θ, radialPDE w (fun s η => u (s, η)) r (-θ) =
      radialPDE w (fun s η => u (s, η)) r θ := by
  intro r θ
  have hslice : (fun t => u (t, -θ)) = fun t => u (t, θ) :=
    funext (fun t => hu t θ)
  simp only [radialPDE, hslice,
    n07b_second_deriv_even (f := fun η : ℝ => u (r, η)) (hu r) θ]

/-- The actual reference forcing, including the retained finite-dimensional
column, is determined by the reference field and its scalar coefficient. -/
def n07bReferenceForcing (D : ReferenceData) (μ : ℝ)
    (u : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2 +
    μ * referenceColumn D p.1 * cosineMode 2 p.2

theorem n07bReferenceForcing_periodic (D : ReferenceData) (μ : ℝ)
    {u : PolarPoint → ℝ} (hu : Function.Periodic u (0, Real.pi)) :
    Function.Periodic (n07bReferenceForcing D μ u) (0, Real.pi) := by
  have hcos : Function.Periodic (cosineMode 2) Real.pi := by
    simpa only [mul_one] using cosineMode_even_frequency_periodic 1
  intro p
  have hpde := n07b_radialPDE_periodic D.w hu p
  change radialPDE D.w (fun r θ => u (r, θ)) (p.1 + 0) (p.2 + Real.pi) =
    radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2 at hpde
  simp only [add_zero] at hpde
  simp only [n07bReferenceForcing, Prod.fst_add, Prod.snd_add, add_zero]
  rw [hpde, hcos p.2]

theorem n07bReferenceForcing_even (D : ReferenceData) (μ : ℝ)
    {u : PolarPoint → ℝ} (hu : ∀ r θ, u (r, -θ) = u (r, θ)) :
    ∀ r θ, n07bReferenceForcing D μ u (r, -θ) = n07bReferenceForcing D μ u (r, θ) := by
  intro r θ
  simp only [n07bReferenceForcing, n07b_radialPDE_even D.w hu r θ,
    cosineMode, mul_neg, Real.cos_neg]

end ContinuousFlexibility.Analysis
