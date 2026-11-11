import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences

/-!
# Extending an actual Green representation from dense sources to all of L²

A bounded operator whose values agree with row-wise L² pairings on a dense
source class has the same representation for every L² source.  The proof
uses an almost-everywhere convergent subsequence of the output sequence
and continuity of each row pairing.  No uniform bound on the individual
rows and no pointwise evaluation on L² equivalence classes is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

/-- A dense-source Green representation extends to all L² sources whenever
each actual kernel row belongs to L². -/
theorem ae_eq_row_pairing_of_dense {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (row : X → Lp ℝ 2 μ)
    {S : Set (Lp ℝ 2 μ)} (hS : Dense S)
    (hrep : ∀ f ∈ S, (T f : X → ℝ) =ᵐ[μ] fun x => inner ℝ (row x) f)
    (f : Lp ℝ 2 μ) :
    (T f : X → ℝ) =ᵐ[μ] fun x => inner ℝ (row x) f := by
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp (hS f)
  have hTlim : Tendsto (fun n => T (s n)) atTop (𝓝 (T f)) :=
    (T.continuous.tendsto f).comp hlim
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hTlim).exists_seq_tendsto_ae
  have hrepAll : ∀ᵐ x ∂μ, ∀ n : ℕ, T (s n) x = inner ℝ (row x) (s n) :=
    ae_all_iff.mpr (fun n => hrep (s n) (hs n))
  filter_upwards [hae, hrepAll] with x hx hxr
  have hpair : Tendsto (fun n => inner ℝ (row x) (s (ns n))) atTop
      (𝓝 (inner ℝ (row x) f)) :=
    ((innerSL ℝ (row x)).continuous.tendsto f).comp (hlim.comp hns.tendsto_atTop)
  have hpair' : Tendsto (fun n => inner ℝ (row x) (s (ns n))) atTop (𝓝 (T f x)) := by
    convert hx using 1
    funext n
    exact (hxr (ns n)).symm
  exact tendsto_nhds_unique hpair' hpair

end ContinuousFlexibility.Analysis
