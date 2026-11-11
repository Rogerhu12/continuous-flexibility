import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Ordinary derivatives determined from one side

Agreement on an open set determines all ordinary derivatives in its interior.
At a boundary point where that set has unique differentiation, an ordinary
derivative either vanishes by the definition of `fderiv`, or agrees with the
derivative of a differentiable comparison map.  Applying this fact to each
iterated derivative handles functions whose one-sided smooth extension need
not be smooth as a function on the whole ambient space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

section General

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f g : E → F} {s : Set E} {x : E}

/-- If two maps agree on a set with unique differentiation at `x`, a
differentiable comparison map determines the ordinary derivative whenever
that ordinary derivative exists.  Otherwise `fderiv` is zero. -/
theorem fderiv_eq_zero_or_eq_of_eqOn
    (hfg : EqOn f g s) (hs : UniqueDiffWithinAt ℝ s x)
    (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ f x = 0 ∨ fderiv ℝ f x = fderiv ℝ g x := by
  by_cases hf : DifferentiableAt ℝ f x
  · right
    have hx : f x = g x := by
      apply sub_eq_zero.mp
      exact (hf.continuousAt.sub hg.continuousAt).continuousWithinAt
        |>.eq_const_of_mem_closure hs.mem_closure
          (fun y hy => sub_eq_zero.mpr (hfg hy))
    exact hs.eq hf.hasFDerivAt.hasFDerivWithinAt
      (hg.hasFDerivAt.hasFDerivWithinAt.congr hfg hx)
  · exact Or.inl (fderiv_zero_of_not_differentiableAt hf)

/-- Agreement on an open set persists under every ordinary iterated
derivative, without differentiability assumptions on either map. -/
theorem iteratedFDeriv_eqOn_of_isOpen
    (hs : IsOpen s) (hfg : EqOn f g s) (n : ℕ) :
    EqOn (iteratedFDeriv ℝ n f) (iteratedFDeriv ℝ n g) s := by
  intro y hy
  have heq : f =ᶠ[𝓝 y] g :=
    Filter.eventually_of_mem (hs.mem_nhds hy) (fun _ hz => hfg hz)
  exact (heq.iteratedFDeriv ℝ n).self_of_nhds

/-- At a point of unique differentiation for an open set, every
positive-order ordinary jet of a map agreeing there with a smooth map is
either zero or the corresponding jet of that smooth map. -/
theorem iteratedFDeriv_succ_eq_zero_or_eq_of_eqOn_open
    (hs : IsOpen s) (hfg : EqOn f g s)
    (hx : UniqueDiffWithinAt ℝ s x) (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    iteratedFDeriv ℝ (n + 1) f x = 0 ∨
      iteratedFDeriv ℝ (n + 1) f x = iteratedFDeriv ℝ (n + 1) g x := by
  have hgj : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x :=
    hg.contDiffAt.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
  rcases fderiv_eq_zero_or_eq_of_eqOn
      (iteratedFDeriv_eqOn_of_isOpen hs hfg n) hx hgj with hzero | heq
  · left
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hzero,
      LinearIsometryEquiv.map_zero]
  · right
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, heq]

/-- The corresponding ordinary jet norm cannot exceed that of the smooth
comparison map. -/
theorem norm_iteratedFDeriv_succ_le_of_eqOn_open
    (hs : IsOpen s) (hfg : EqOn f g s)
    (hx : UniqueDiffWithinAt ℝ s x) (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ ‖iteratedFDeriv ℝ (n + 1) g x‖ := by
  rcases iteratedFDeriv_succ_eq_zero_or_eq_of_eqOn_open hs hfg hx hg n with hzero | heq
  · simpa only [hzero, norm_zero] using norm_nonneg (iteratedFDeriv ℝ (n + 1) g x)
  · exact le_of_eq (congrArg norm heq)

end General

section Halfspace

variable {P F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f g : ℝ × P → F}

/-- Ordinary jets on the boundary of a negative halfspace are determined
by a smooth comparison map on that halfspace, or vanish. -/
theorem iteratedFDeriv_succ_eq_zero_or_eq_at_zero_of_eqOn_neg
    (hfg : ∀ p : ℝ × P, p.1 < 0 → f p = g p)
    (hg : ContDiff ℝ ∞ g) (n : ℕ) (y : P) :
    iteratedFDeriv ℝ (n + 1) f (0, y) = 0 ∨
      iteratedFDeriv ℝ (n + 1) f (0, y) =
        iteratedFDeriv ℝ (n + 1) g (0, y) := by
  apply iteratedFDeriv_succ_eq_zero_or_eq_of_eqOn_open
    (s := Iio (0 : ℝ) ×ˢ (univ : Set P))
    (isOpen_Iio.prod isOpen_univ) (fun p hp => hfg p hp.1)
  · exact (uniqueDiffWithinAt_Iio 0).prod uniqueDiffWithinAt_univ
  · exact hg

/-- A smooth comparison map on the negative halfspace bounds all
positive-order ordinary jet norms at its boundary. -/
theorem norm_iteratedFDeriv_succ_le_at_zero_of_eqOn_neg
    (hfg : ∀ p : ℝ × P, p.1 < 0 → f p = g p)
    (hg : ContDiff ℝ ∞ g) (n : ℕ) (y : P) :
    ‖iteratedFDeriv ℝ (n + 1) f (0, y)‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) g (0, y)‖ := by
  rcases iteratedFDeriv_succ_eq_zero_or_eq_at_zero_of_eqOn_neg hfg hg n y with hzero | heq
  · simpa only [hzero, norm_zero] using
      norm_nonneg (iteratedFDeriv ℝ (n + 1) g (0, y))
  · exact le_of_eq (congrArg norm heq)

/-- A map which vanishes on the negative halfspace has zero ordinary
jets of every positive order at the boundary, even if its boundary value
is nonzero or it is not continuous there. -/
theorem iteratedFDeriv_succ_eq_zero_at_zero_of_eqOn_neg_zero
    (hf : ∀ p : ℝ × P, p.1 < 0 → f p = 0) (n : ℕ) (y : P) :
    iteratedFDeriv ℝ (n + 1) f (0, y) = 0 := by
  rcases iteratedFDeriv_succ_eq_zero_or_eq_at_zero_of_eqOn_neg
      (g := fun _ => (0 : F)) hf contDiff_const n y with hzero | heq
  · exact hzero
  · simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using heq

end Halfspace

end ContinuousFlexibility.Analysis
