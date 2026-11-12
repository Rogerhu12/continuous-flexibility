import ContinuousFlexibility.Analysis.N05ReferenceAngularReconstruction
import ContinuousFlexibility.Analysis.N05ReferenceAngularJetEstimate
import ContinuousFlexibility.Analysis.N05ReferencePeriodicJetLimit
import ContinuousFlexibility.Analysis.N05ReferenceZeroRemainder

/-!
# Actual angular jet limits of a physical output

Any output with summable frequency-weighted squares has one genuine
periodic angular jet limit. This reconstruction applies to the original
inverse output and to its actual normal derivative with the same weights.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

theorem n05_referenceOutput_highAngularJet_limit {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M a : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hU : OutputRealization D γ M a U) (b : ℕ)
    (hs : Summable (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
      n05_referenceHighOutputSquare D γ M U n)) :
    ∃ d : PolarPoint → ℝ,
      MemLp d 2 (referenceWeightedMeasure D γ (-M)) ∧
      outputNormSquare D γ M 0 (d, 0) =
        ∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          n05_referenceHighOutputSquare D γ M U n ∧
      Tendsto (fun N => ∫ x, (n05_referenceHighAngularJet (Finset.range N) b U.1 x - d x) ^ 2
        ∂referenceWeightedMeasure D γ (-M)) atTop (𝓝 0) ∧
      Function.Periodic d (0, Real.pi) := by
  have hab := hD.choose_spec.1.2.1.le
  have hpart := hD.choose_spec.2.1
  have hp (n : ℕ) : MemLp (referenceBasisProjection {n + 2} U.1) 2
      (referenceWeightedMeasure D γ (-M)) := by
    have hI : ∀ k ∈ ({n + 2} : Finset ℕ), 2 ≤ k := by
      intro k hk
      simp only [Finset.mem_singleton] at hk
      omega
    have hP := n05_referenceHighProjection_outputRealization hab hpart hU hI
    have hw := OutputRealization.memLp_weighted hab hpart hP
    simpa only [n05_outputRemainder_zero] using hw
  have hsout : Summable (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
      sourceNormSquare D γ (-M) (referenceBasisProjection {n + 2} U.1, 0)) := by
    simpa only [n05_referenceHighOutputSquare,
      n05_zeroOutputNormSquare_eq_sourceNormSquare_neg] using hs
  obtain ⟨d₀, hd₀, he₀, hlim₀⟩ :=
    n05_referenceHighAngularJet_reconstruct hab hpart U.1 b hp hsout
  have hjet (N : ℕ) :
      MemLp (n05_referenceHighAngularJet (Finset.range N) b U.1) 2
        (referenceWeightedMeasure D γ (-M)) := by
    have hn := n05_referenceHighAngularJet_output_norm hD hborder hγ hU (Finset.range N) b
    apply memLp_referenceWeightedMeasure hab hpart hn.1
    simpa only [sourceCellSquare_neg_fun] using hn.2.1
  obtain ⟨d, hd, hrep, hperiodic⟩ := n05_periodic_representative_of_L2_tendsto
    hjet (fun N => n05_referenceHighAngularJet_periodic (Finset.range N) b U.1)
    (reference_memLp_tendsto_of_sub_sq hjet hd₀ hlim₀)
  have heq : d =ᵐ[referenceWeightedMeasure D γ (-M)] d₀ :=
    hrep.trans hd₀.coeFn_toLp
  have he : (∫ x, d x ^ 2 ∂referenceWeightedMeasure D γ (-M)) =
      ∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        sourceNormSquare D γ (-M) (referenceBasisProjection {n + 2} U.1, 0) := by
    refine (integral_congr_ae ?_).trans he₀
    filter_upwards [heq] with x hx
    rw [hx]
  have hlim : Tendsto (fun N => ∫ x,
      (n05_referenceHighAngularJet (Finset.range N) b U.1 x - d x) ^ 2
        ∂referenceWeightedMeasure D γ (-M)) atTop (𝓝 0) := by
    have hsame : (fun N => ∫ x,
        (n05_referenceHighAngularJet (Finset.range N) b U.1 x - d x) ^ 2
          ∂referenceWeightedMeasure D γ (-M)) =
        (fun N => ∫ x,
        (n05_referenceHighAngularJet (Finset.range N) b U.1 x - d₀ x) ^ 2
          ∂referenceWeightedMeasure D γ (-M)) := by
      funext N
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    rw [hsame]
    exact hlim₀
  have heOut : (∫ x, d x ^ 2 ∂referenceWeightedMeasure D γ (-M)) =
      ∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        n05_referenceHighOutputSquare D γ M U n := by
    simpa only [n05_referenceHighOutputSquare,
      n05_zeroOutputNormSquare_eq_sourceNormSquare_neg] using he
  obtain ⟨hl, hsum⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hd
  have hn : outputNormSquare D γ M 0 (d, 0) =
      ∫ x, d x ^ 2 ∂referenceWeightedMeasure D γ (-M) := by
    rw [n05_zeroOutputNormSquare_eq_sourceNormSquare_neg]
    simpa only [sourceNormSquare, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using
      (integral_sq_referenceWeightedMeasure_eq hab hpart hl hsum).symm
  exact ⟨d, hd, hn.trans heOut, hlim, hperiodic⟩

end ContinuousFlexibility.Radial
