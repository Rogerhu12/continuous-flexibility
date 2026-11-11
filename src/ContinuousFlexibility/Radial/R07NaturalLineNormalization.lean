import ContinuousFlexibility.Statements.DeepTailOperator
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Normalization of the actual one-dimensional natural solution space

Equality on a one-sided open interval determines the value and derivative
at its smooth entrance.  Consequently a natural solution normalized to have
entrance value one spans the natural line with coefficient exactly equal to
the entrance value of any other natural solution.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

/-- Equal differentiable functions on a right-hand open interval have the
same entrance value and ordinary derivative. -/
theorem cauchyData_eq_of_eqOn_Ioo_right {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : DifferentiableAt ℝ f a) (hg : DifferentiableAt ℝ g a)
    (heq : EqOn f g (Ioo a b)) : f a = g a ∧ deriv f a = deriv g a := by
  have he : f =ᶠ[𝓝[>] a] g := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab), self_mem_nhdsWithin]
      with x hx hxa
    exact heq ⟨hxa, hx⟩
  have hv : f a = g a := tendsto_nhds_unique_of_eventuallyEq
    (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) he
  refine ⟨hv, ?_⟩
  have hdf : HasDerivWithinAt f (deriv f a) (Ioi a) a := hf.hasDerivAt.hasDerivWithinAt
  have hdg : HasDerivWithinAt g (deriv g a) (Ioi a) a := hg.hasDerivAt.hasDerivWithinAt
  exact (hdf.derivWithin (uniqueDiffWithinAt_Ioi a)).symm.trans
    ((he.derivWithin_eq hv).trans (hdg.derivWithin (uniqueDiffWithinAt_Ioi a)))

/-- A normalized member spans the R06 natural line; its coefficient is the
entrance value, and the same identity holds for the entrance derivative. -/
theorem tailNaturalLine_normalized_spans {T : Statements.DeepTailData}
    (hgap : T.entrance < T.endpoint) (hline : Statements.TailNaturalLineAndKernel T)
    {u : ℝ → ℝ} (hu : Statements.TailNaturalEquation T u) (hu₀ : u T.entrance = 1)
    {v : ℝ → ℝ} (hv : Statements.TailNaturalEquation T v) :
    EqOn v (fun x => v T.entrance * u x) (Ioo T.entrance T.endpoint) ∧
      deriv v T.entrance = v T.entrance * deriv u T.entrance := by
  rcases hline with ⟨base, hbase, _, hspan, _⟩
  obtain ⟨a, ha⟩ := hspan u hu
  obtain ⟨b, hb⟩ := hspan v hv
  have hbd : DifferentiableAt ℝ base T.entrance := hbase.1.differentiableAt (by simp)
  have hU := cauchyData_eq_of_eqOn_Ioo_right hgap (hu.1.differentiableAt (by simp))
    (differentiableAt_const.mul hbd) ha
  have hV := cauchyData_eq_of_eqOn_Ioo_right hgap (hv.1.differentiableAt (by simp))
    (differentiableAt_const.mul hbd) hb
  have hone : a * base T.entrance = 1 := hU.1.symm.trans hu₀
  have heq : EqOn v (fun x => v T.entrance * u x) (Ioo T.entrance T.endpoint) := by
    intro x hx
    dsimp only
    rw [hb x hx, ha x hx, hV.1]
    calc
      b * base x = b * (a * base T.entrance) * base x := by rw [hone, mul_one]
      _ = (b * base T.entrance) * (a * base x) := by ring
  refine ⟨heq, ?_⟩
  have hd := (cauchyData_eq_of_eqOn_Ioo_right hgap (hv.1.differentiableAt (by simp))
    (differentiableAt_const.mul (hu.1.differentiableAt (by simp))) heq).2
  simpa only [deriv_const_mul_field] using hd

/-- Two natural solutions with entrance value one have the same natural
line and the same ordinary entrance derivative. -/
theorem tailNaturalLine_normalized_unique {T : Statements.DeepTailData}
    (hgap : T.entrance < T.endpoint) (hline : Statements.TailNaturalLineAndKernel T)
    {u v : ℝ → ℝ} (hu : Statements.TailNaturalEquation T u) (hu₀ : u T.entrance = 1)
    (hv : Statements.TailNaturalEquation T v) (hv₀ : v T.entrance = 1) :
    EqOn v u (Ioo T.entrance T.endpoint) ∧ deriv v T.entrance = deriv u T.entrance := by
  simpa only [hv₀, one_mul] using tailNaturalLine_normalized_spans hgap hline hu hu₀ hv

/-- A nonzero natural solution cannot have entrance value zero once the
normalized natural solution provided by parameter continuity is available. -/
theorem tailNaturalLine_entrance_ne_zero {T : Statements.DeepTailData}
    (hgap : T.entrance < T.endpoint) (hline : Statements.TailNaturalLineAndKernel T)
    {u : ℝ → ℝ} (hu : Statements.TailNaturalEquation T u) (hu₀ : u T.entrance = 1)
    {v : ℝ → ℝ} (hv : Statements.TailNaturalEquation T v)
    (hvne : ∃ x ∈ Ioo T.entrance T.endpoint, v x ≠ 0) : v T.entrance ≠ 0 := by
  obtain ⟨x, hx, hne⟩ := hvne
  intro hz
  apply hne
  have h := (tailNaturalLine_normalized_spans hgap hline hu hu₀ hv).1 hx
  simpa only [hz, zero_mul] using h

end ContinuousFlexibility.Radial
