module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

/-!
# Smoothness of classical buffer solutions

Once the weak equation has supplied a continuously differentiable field and
first derivative, the actual scalar differential equation bootstraps both
to smoothness.  This lemma treats any open set, hence both finite buffers
and exterior half-lines, with the same proof.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open scoped ContDiff

theorem positiveBuffer_classical_contDiffOn
    {Ω : Set ℝ} (hΩ : IsOpen Ω) {u d V f : ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ V Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hu : ∀ x ∈ Ω, HasDerivAt u (d x) x)
    (hd : ∀ x ∈ Ω, HasDerivAt d (V x * u x + f x) x) :
    ContDiffOn ℝ ∞ u Ω ∧ ContDiffOn ℝ ∞ d Ω := by
  have hn (n : ℕ) : ContDiffOn ℝ n u Ω ∧ ContDiffOn ℝ n d Ω := by
    induction n with
    | zero =>
      simp only [Nat.cast_zero, contDiffOn_zero]
      exact ⟨fun x hx => (hu x hx).continuousAt.continuousWithinAt,
        fun x hx => (hd x hx).continuousAt.continuousWithinAt⟩
    | succ n ih =>
      have hu' : ContDiffOn ℝ ((n : ℕ∞ω) + 1) u Ω := by
        apply (contDiffOn_succ_iff_deriv_of_isOpen hΩ).mpr
        refine ⟨fun x hx => (hu x hx).differentiableAt.differentiableWithinAt,
          by simp, ?_⟩
        apply ih.2.congr
        intro x hx
        exact (hu x hx).deriv
      have hd' : ContDiffOn ℝ ((n : ℕ∞ω) + 1) d Ω := by
        apply (contDiffOn_succ_iff_deriv_of_isOpen hΩ).mpr
        refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,
          by simp, ?_⟩
        apply ((hV.of_le (by simp)).mul ih.1 |>.add (hf.of_le (by simp))).congr
        intro x hx
        exact (hd x hx).deriv
      simpa only [Nat.cast_add, Nat.cast_one] using And.intro hu' hd'
  exact ⟨contDiffOn_infty.mpr fun n => (hn n).1,
    contDiffOn_infty.mpr fun n => (hn n).2⟩

theorem positiveBuffer_classical_equation
    {Ω : Set ℝ} (hΩ : IsOpen Ω) {u d V f : ℝ → ℝ}
    (hu : ∀ x ∈ Ω, HasDerivAt u (d x) x)
    (hd : ∀ x ∈ Ω, HasDerivAt d (V x * u x + f x) x)
    {x : ℝ} (hx : x ∈ Ω) :
    -deriv (deriv u) x + V x * u x = -f x := by
  have heq : deriv u =ᶠ[nhds x] d := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact (hu y hy).deriv
  rw [heq.deriv_eq, (hd x hx).deriv]
  ring

end ContinuousFlexibility.Radial
