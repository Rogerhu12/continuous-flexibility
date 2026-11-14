module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

/-!
# Continuity at a boundary from actual scalar equations

A continuous injective scalar slice has its unique solution between any
two strict value brackets. Limits of those two fixed test values are
enough to determine the limit of the solutions. Neither continuity of
the selected solutions nor joint continuity of the scalar field is an
input to this statement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

private theorem mem_Ioo_of_injective_scalar_equation
    {F : ℝ → ℝ} {a b u y : ℝ} (hab : a < b)
    (hF : Continuous F) (hinj : Function.Injective F)
    (hu : F u = y) (ha : F a < y) (hb : y < F b) : u ∈ Ioo a b := by
  obtain ⟨v, hv, hvalue⟩ := intermediate_value_Icc hab.le hF.continuousOn ⟨ha.le, hb.le⟩
  have hleft : a < v := by
    rcases lt_or_eq_of_le hv.1 with h | h
    · exact h
    · exact False.elim (ha.ne (by rw [h]; exact hvalue))
  have hright : v < b := by
    rcases lt_or_eq_of_le hv.2 with h | h
    · exact h
    · exact False.elim (hb.ne' (by rw [← h]; exact hvalue))
  have heq : v = u := hinj (hvalue.trans hu.symm)
  apply Set.mem_Ioo.mpr
  simpa only [heq] using And.intro hleft hright

/-- Fixed-angle value limits and injectivity of the true interior slices
force the actual solution limit at the boundary. -/
theorem tendsto_of_injective_scalar_equation
    {P : Type*} {l : Filter P} {F : P → ℝ → ℝ} {u y : P → ℝ}
    {G : ℝ → ℝ} {θ : ℝ}
    (hF : ∀ᶠ p in l, Continuous (F p))
    (hinj : ∀ᶠ p in l, Function.Injective (F p))
    (heq : ∀ᶠ p in l, F p (u p) = y p)
    (hfixed : ∀ η : ℝ, Tendsto (fun p => F p η) l (𝓝 (G η)))
    (hy : Tendsto y l (𝓝 (G θ))) (hG : StrictMono G) :
    Tendsto u l (𝓝 θ) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hright : θ < θ + 1 := by linarith
    have hlo := Filter.Tendsto.eventually_lt (hfixed a) hy (hG ha)
    have hhi := Filter.Tendsto.eventually_lt hy (hfixed (θ + 1)) (hG hright)
    filter_upwards [hF, hinj, heq, hlo, hhi] with p hp hi he hl hh
    exact (mem_Ioo_of_injective_scalar_equation (ha.trans hright) hp hi he hl hh).1
  · intro b hb
    have hleft : θ - 1 < θ := by linarith
    have hlo := Filter.Tendsto.eventually_lt (hfixed (θ - 1)) hy (hG hleft)
    have hhi := Filter.Tendsto.eventually_lt hy (hfixed b) (hG hb)
    filter_upwards [hF, hinj, heq, hlo, hhi] with p hp hi he hl hh
    exact (mem_Ioo_of_injective_scalar_equation (hleft.trans hb) hp hi he hl hh).2

end ContinuousFlexibility.Analysis
