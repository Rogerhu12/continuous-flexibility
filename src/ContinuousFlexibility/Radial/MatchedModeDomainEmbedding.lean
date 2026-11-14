module

public import ContinuousFlexibility.Radial.MatchedModeMeasureEmbedding
public import ContinuousFlexibility.Radial.MatchedModeGraphRealization
public import ContinuousFlexibility.Radial.ReferenceSourceCosine
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# The frozen weighted domains supply the actual modal L² vectors

Positive attenuation embeds the output remainder into the genuine
Hilbert measure. The smooth left height can then be restored there.
A fixed source coefficient threshold gives every normalized source mode
in the same space, so cosine projection has no extra L² assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

theorem OutputRealization.memLp_hilbertAngular {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M aL : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hU : OutputRealization D γ M aL U) :
    MemLp U.1 2 ((radialHilbertMeasure D).prod referenceAngularMeasure) := by
  have hp : RadialPartition D := hD.choose_spec.2.1
  have hab := (Radial.matchingProfileGeometry hD).2.1.le
  obtain ⟨K, _, hK⟩ := Radial.matchedMode_measure_le_outputWeighted hD hγ M
  have hprod : (radialHilbertMeasure D).prod referenceAngularMeasure ≤
      ENNReal.ofReal K • referenceWeightedMeasure D γ (-M) := by
    rw [referenceWeightedMeasure_eq_prod hp]
    simpa only [Measure.prod_smul_left] using
      Measure.prod_mono (hK γ le_rfl) (le_refl referenceAngularMeasure)
  have hr : MemLp (outputRemainder D aL U) 2
      ((radialHilbertMeasure D).prod referenceAngularMeasure) :=
    (hU.memLp_weighted hab hp).of_measure_le_smul (by simp) hprod
  have hχ : MemLp D.chiLeft 2 (radialHilbertMeasure D) :=
    Radial.matching_memLp_of_continuousOn hD hB.2.2.2.2.1.continuous.measurable
      hB.2.2.2.2.1.continuous.continuousOn 2
  have hh : MemLp (fun x : PolarPoint => aL * D.chiLeft x.1) 2
      ((radialHilbertMeasure D).prod referenceAngularMeasure) :=
    (hχ.const_mul aL).comp_fst referenceAngularMeasure
  apply (memLp_congr_ae ?_).mp (hr.add hh)
  filter_upwards with x
  change (U.1 x - aL * D.chiLeft x.1) + aL * D.chiLeft x.1 = U.1 x
  ring

theorem OutputMember.memLp_hilbertAngular {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hU : OutputMember D γ M U) :
    MemLp U.1 2 ((radialHilbertMeasure D).prod referenceAngularMeasure) := by
  obtain ⟨aL, haL⟩ := hU
  exact haL.memLp_hilbertAngular hD hB hγ

theorem OutputMember.referenceMode_even_memLp_hilbert {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hU : OutputMember D γ M U) (n : ℕ) :
    MemLp (referenceMode U.1 (2 * (n + 1))) 2 (radialHilbertMeasure D) := by
  letI : IsFiniteMeasure (radialHilbertMeasure D) := Radial.radialHilbertMeasure_isFinite hD
  have hi := hU.memLp_hilbertAngular hD hB hγ
  obtain ⟨aL, haL⟩ := hU
  have hp (r : ℝ) : Function.Periodic (fun θ => U.1 (r, θ)) Real.pi := by
    intro θ
    have he := haL.2.2.1 (r, θ)
    change U.1 (r + 0, θ + Real.pi) = U.1 (r, θ) at he
    simpa only [add_zero] using he
  have hm := referenceCosineCoefficient_memLp hi hp haL.2.2.2 (n + 1)
  simpa only [referenceCosineCoefficient_succ_eq_referenceMode] using hm

/-- The source threshold is fixed before the attenuation, source, and mode. -/
theorem exists_sourceMode_memLp_hilbert {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ Mmin : ℝ, 0 < Mmin ∧ ∀ M, Mmin ≤ M → ∀ γ, 0 ≤ γ →
      ∀ F : RadialSource, SourceMember D γ M F → ∀ n : ℕ,
        MemLp (fun r => -referenceMode F.1 (2 * (n + 1)) r /
          Radial.matchingDensity D r) 2 (radialHilbertMeasure D) := by
  obtain ⟨Mmin, hMmin, hsource⟩ := Radial.exists_matchedMode_source_memLp hD
  refine ⟨Mmin, hMmin, ?_⟩
  intro M hM γ hγ F hF n
  exact hsource M hM γ hγ _ (hF.referenceMode_even_memLp
    (Radial.matchingProfileGeometry hD).2.1.le hD.choose_spec.2.1 n)

/-- Every positive even mode of a member of the actual weighted weak graph
has genuine Hilbert representatives satisfying the complete frozen graph.
Only the stated positive attenuation and source coefficient threshold
remain; no modal L² membership is assumed separately. -/
theorem exists_referenceGraph_modeFullGraph {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) :
    ∃ Mmin : ℝ, 0 < Mmin ∧
      ∀ γ : ℝ, 0 < γ → ∀ M₀ : ℝ, Mmin ≤ M₀ → ∀ M₁ : ℝ,
      ∀ U : RadialUnknown, ∀ F : RadialSource,
        ReferenceGraph D γ M₀ M₁ U F → ∀ n : ℕ,
          ∃ u f : RadialModeL2 D,
            ((u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
              referenceMode U.1 (2 * (n + 1))) ∧
            ((f : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
              (fun r => -referenceMode F.1 (2 * (n + 1)) r /
                Radial.matchingDensity D r)) ∧
            ModeFullGraph D (2 * (n + 1))
              (u, -(if 2 * (n + 1) = 2 then U.2 else 0))
              (f, if 2 * (n + 1) = 2 then F.2 else 0) := by
  obtain ⟨Mmin, hMmin, hsource⟩ := exists_sourceMode_memLp_hilbert hD
  refine ⟨Mmin, hMmin, ?_⟩
  intro γ hγ M₀ hM₀ M₁ U F hG n
  have hu := hG.1.referenceMode_even_memLp_hilbert hD hB hγ n
  have hf := hsource M₀ hM₀ γ hγ.le F hG.2.1 n
  refine ⟨hu.toLp (referenceMode U.1 (2 * (n + 1))),
    hf.toLp (fun r => -referenceMode F.1 (2 * (n + 1)) r /
      Radial.matchingDensity D r), hu.coeFn_toLp, hf.coeFn_toLp, ?_⟩
  exact hG.modeFullGraph_of_memLp hD hB (by omega) hu hf

end ContinuousFlexibility.Statements
