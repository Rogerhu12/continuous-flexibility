import ContinuousFlexibility.Statements.Analysis
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Joint smoothness from an actual two-coordinate derivative hierarchy

Each field has the stated genuine first derivative in both coordinate
directions, and the next fields are jointly continuous. The continuous
partial derivative theorem identifies the full Fréchet derivative.
Induction then gives all orders of joint smoothness. This applies to a
parameter line and the angular coordinate without imposing any norm on
the original parameter space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem scalarPlane_hasStrictFDerivAt_of_partials
    {U : Set PolarPoint} {f a b : PolarPoint → ℝ}
    (hU : IsOpen U)
    (ha : ContinuousOn a U) (hb : ContinuousOn b U)
    (hfirst : ∀ p ∈ U, HasDerivAt (fun t => f (t, p.2)) (a p) p.1)
    (hsecond : ∀ p ∈ U, HasDerivAt (fun t => f (p.1, t)) (b p) p.2)
    {p : PolarPoint} (hp : p ∈ U) :
    HasStrictFDerivAt f
      (a p • ContinuousLinearMap.fst ℝ ℝ ℝ +
        b p • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have hlin : Continuous (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c) := by
    have heq : (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c) =
        (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ : ℝ → (ℝ →L[ℝ] ℝ)) := by
      funext c
      exact (ContinuousLinearMap.toSpanSingletonLIE_apply ℝ ℝ c).symm
    rw [heq]
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous
  have hd := hasStrictFDerivAt_uncurry_coprod
    (f := fun t θ => f (t, θ))
    (f₁ := fun t θ => ContinuousLinearMap.toSpanSingleton ℝ (a (t, θ)))
    (f₂ := fun t θ => ContinuousLinearMap.toSpanSingleton ℝ (b (t, θ)))
    (by
      filter_upwards [hU.mem_nhds hp] with q hq
      simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using (hfirst q hq).hasFDerivAt)
    (by
      filter_upwards [hU.mem_nhds hp] with q hq
      simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using (hsecond q hq).hasFDerivAt)
    (by simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using
      hlin.continuousAt.comp (ha.continuousAt (hU.mem_nhds hp)))
    (by simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using
      hlin.continuousAt.comp (hb.continuousAt (hU.mem_nhds hp)))
  have heq : (ContinuousLinearMap.toSpanSingleton ℝ (a p)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ (b p)) =
      a p • ContinuousLinearMap.fst ℝ ℝ ℝ + b p • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro q
    change q.1 * a p + q.2 * b p = a p * q.1 + b p * q.2
    ring
  simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
    Function.hasUncurryInduction, id_eq, Function.comp_def, heq] using hd

theorem scalarPlane_jetHierarchy_contDiffOn
    {U : Set PolarPoint} (F : ℕ → ℕ → PolarPoint → ℝ) (hU : IsOpen U)
    (hcont : ∀ a b, ContinuousOn (F a b) U)
    (hfirst : ∀ a b p, p ∈ U →
      HasDerivAt (fun t => F a b (t, p.2)) (F (a + 1) b p) p.1)
    (hsecond : ∀ a b p, p ∈ U →
      HasDerivAt (fun t => F a b (p.1, t)) (F a (b + 1) p) p.2)
    (a b : ℕ) : ContDiffOn ℝ ∞ (F a b) U := by
  have hD (a b : ℕ) (p : PolarPoint) (hp : p ∈ U) :
      HasFDerivAt (F a b)
        (F (a + 1) b p • ContinuousLinearMap.fst ℝ ℝ ℝ +
          F a (b + 1) p • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (scalarPlane_hasStrictFDerivAt_of_partials hU (hcont (a + 1) b)
      (hcont a (b + 1)) (hfirst a b) (hsecond a b) hp).hasFDerivAt
  have hfinite : ∀ n a b : ℕ, ContDiffOn ℝ n (F a b) U := by
    intro n
    induction n with
    | zero =>
        intro a b
        exact contDiffOn_zero.mpr (hcont a b)
    | succ n ih =>
        intro a b p hp
        apply ContDiffAt.contDiffWithinAt
        apply contDiffAt_succ_iff_hasFDerivAt.mpr
        refine ⟨fun q : PolarPoint =>
          F (a + 1) b q • ContinuousLinearMap.fst ℝ ℝ ℝ +
            F a (b + 1) q • ContinuousLinearMap.snd ℝ ℝ ℝ,
          ⟨U, hU.mem_nhds hp, fun q hq => hD a b q hq⟩, ?_⟩
        exact (((ih (a + 1) b).contDiffAt (hU.mem_nhds hp)).smul contDiffAt_const).add
          (((ih a (b + 1)).contDiffAt (hU.mem_nhds hp)).smul contDiffAt_const)
  intro p hp
  exact (contDiffAt_infty.mpr (fun n =>
    (hfinite n a b).contDiffAt (hU.mem_nhds hp))).contDiffWithinAt

end ContinuousFlexibility.Analysis
