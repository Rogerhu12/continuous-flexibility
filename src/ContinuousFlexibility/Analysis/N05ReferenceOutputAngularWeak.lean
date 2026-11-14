module

public import ContinuousFlexibility.Analysis.N05ReferenceOutputAngularLimit
public import ContinuousFlexibility.Analysis.N05ReferenceAngularWeakClosure
public import ContinuousFlexibility.Analysis.N05ReferenceWeightedPhysical
public import ContinuousFlexibility.Analysis.N05ReferenceHighConvergence

/-!
# The reconstructed output jet has the actual weak derivative

The finite angular projections converge to the original high part in
physical L². The weighted jet limit converges in the same physical space,
so closure identifies its true full-period weak angular derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

theorem n05_referenceOutput_highWeakAngularJet {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M a : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hU : OutputRealization D γ M a U) (b : ℕ)
    (hs : Summable (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
      n05_referenceHighOutputSquare D γ M U n)) :
    ∃ d : PolarPoint → ℝ,
      n05_weakReferenceAngularJet D (n05_referenceHighPart U.1) d b ∧
      MemLp d 2 (referenceWeightedMeasure D γ (-M)) ∧
      outputNormSquare D γ M 0 (d, 0) =
        ∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          n05_referenceHighOutputSquare D γ M U n ∧
      Function.Periodic d (0, Real.pi) := by
  obtain ⟨d, hd, hb, hlim, hperiodic⟩ :=
    n05_referenceOutput_highAngularJet_limit hD hborder hγ hU b hs
  have hab := hD.choose_spec.1.2.1.le
  have hpart := hD.choose_spec.2.1
  have hjet (N : ℕ) :
      MemLp (n05_referenceHighAngularJet (Finset.range N) b U.1) 2
        (referenceWeightedMeasure D γ (-M)) := by
    have hn := n05_referenceHighAngularJet_output_norm hD hborder hγ hU (Finset.range N) b
    apply memLp_referenceWeightedMeasure hab hpart hn.1
    simpa only [sourceCellSquare_neg_fun] using hn.2.1
  obtain ⟨hjp, hdp, hjlim⟩ :=
    n05_referenceWeighted_tendsto_physical hD hγ hjet hd hlim
  have hu : MemLp U.1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ ⟨a, hU⟩
  have hup (r : ℝ) : Function.Periodic (fun θ => U.1 (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hU.2.2.1 (r, θ)
  have hue (r : ℝ) : Function.Even (fun θ => U.1 (r, θ)) := hU.2.2.2 r
  obtain ⟨hp, hh, hhighlim⟩ := n05_referenceHighProjection_tendsto hu hup hue
  have hweak := n05_weakReferenceAngularJet_of_L2_tendsto hab hp hjp hh hdp
    hhighlim hjlim (fun N => n05_referenceHighAngularJet_weak D (Finset.range N) b U.1)
  exact ⟨d, hweak, hd, hb, hperiodic⟩

end ContinuousFlexibility.Radial
