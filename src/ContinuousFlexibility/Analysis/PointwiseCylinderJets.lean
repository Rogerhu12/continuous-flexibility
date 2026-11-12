import ContinuousFlexibility.Analysis.BoundaryTaylorExtension
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Actual cylinder jets from smoothness at a point

Smoothness of an actual slice derivative is obtained by differentiating
the corresponding parameterized scalar function. Iterating this argument
gives smoothness at the same point for every actual mixed slice jet.

This avoids replacing ContDiffAt infinity by smoothness on one common
open neighborhood. In particular pointwise smoothness along a boundary
circle is enough to make each radial boundary trace globally smooth in
the angle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem contDiffAt_parameterDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ → ℝ} {g : E → ℝ} {x : E} {m n : ℕ∞ω}
    (hf : ContDiffAt ℝ n (Function.uncurry f) (x, g x))
    (hg : ContDiffAt ℝ m g x) (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (fun q => deriv (f q) (g q)) x := by
  have hD : ContDiffAt ℝ m (fun q => fderiv ℝ (f q) (g q)) x :=
    hf.fderiv hg hmn
  simpa only [fderiv_apply_one_eq_deriv] using
    hD.clm_apply (contDiffAt_const (c := (1 : ℝ)))

/-- The actual radial slice jet is smooth at every point at which the
original field is smooth. No neighborhood of infinite order is selected. -/
theorem contDiffAt_radialSliceJet {F : PolarPoint → ℝ} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p) (n : ℕ) :
    ContDiffAt ℝ ∞
      (fun q : PolarPoint => iteratedDeriv n (fun r => F (r, q.2)) q.1) p := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ n ih =>
      have hmap : ContDiffAt ℝ ∞
          (fun z : PolarPoint × ℝ => (z.2, z.1.2)) (p, p.1) :=
        contDiffAt_snd.prodMk contDiffAt_fst.snd
      have haux : ContDiffAt ℝ ∞
          (Function.uncurry (fun q : PolarPoint => fun r : ℝ =>
            iteratedDeriv n (fun t => F (t, q.2)) r)) (p, p.1) :=
        ContDiffAt.comp
          (f := fun z : PolarPoint × ℝ => (z.2, z.1.2))
          (g := fun q : PolarPoint => iteratedDeriv n (fun r => F (r, q.2)) q.1)
          (p, p.1) ih hmap
      have hd := contDiffAt_parameterDeriv haux
        (contDiffAt_fst : ContDiffAt ℝ ∞ (fun q : PolarPoint => q.1) p) (by simp)
      simpa only [iteratedDeriv_succ] using hd

/-- The corresponding pointwise statement for actual angular slice jets. -/
theorem contDiffAt_angularSliceJet {F : PolarPoint → ℝ} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p) (n : ℕ) :
    ContDiffAt ℝ ∞
      (fun q : PolarPoint => iteratedDeriv n (fun θ => F (q.1, θ)) q.2) p := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ n ih =>
      have hmap : ContDiffAt ℝ ∞
          (fun z : PolarPoint × ℝ => (z.1.1, z.2)) (p, p.2) :=
        contDiffAt_fst.fst.prodMk contDiffAt_snd
      have haux : ContDiffAt ℝ ∞
          (Function.uncurry (fun q : PolarPoint => fun θ : ℝ =>
            iteratedDeriv n (fun t => F (q.1, t)) θ)) (p, p.2) :=
        ContDiffAt.comp
          (f := fun z : PolarPoint × ℝ => (z.1.1, z.2))
          (g := fun q : PolarPoint => iteratedDeriv n (fun θ => F (q.1, θ)) q.2)
          (p, p.2) ih hmap
      have hd := contDiffAt_parameterDeriv haux
        (contDiffAt_snd : ContDiffAt ℝ ∞ (fun q : PolarPoint => q.2) p) (by simp)
      simpa only [iteratedDeriv_succ] using hd

/-- Every actual mixed derivative is smooth at the same point. -/
theorem contDiffAt_mixedDerivative {F : PolarPoint → ℝ} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p) (a b : ℕ) :
    ContDiffAt ℝ ∞ (mixedDerivative a b F) p :=
  contDiffAt_radialSliceJet (contDiffAt_angularSliceJet hF b) a

/-- Pointwise infinite smoothness at every boundary point gives globally
smooth angular boundary data for each finite radial Taylor coefficient. -/
theorem contDiff_radialBoundaryJet_of_contDiffAt
    {F : PolarPoint → ℝ} (c : ℝ)
    (hF : ∀ θ : ℝ, ContDiffAt ℝ ∞ F (c, θ)) (n : ℕ) :
    ContDiff ℝ ∞ (radialBoundaryJet F c n) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact ContDiffAt.fun_comp (f := fun t : ℝ => (c, t))
    (g := fun q : PolarPoint => iteratedDeriv n (fun r => F (r, q.2)) q.1)
    θ (contDiffAt_radialSliceJet (hF θ) n)
      (contDiffAt_const.prodMk contDiffAt_id)

end ContinuousFlexibility.Analysis
