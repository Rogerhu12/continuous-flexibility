module

public import ContinuousFlexibility.Analysis.N05ReferenceOutputAngularWeak
public import ContinuousFlexibility.Analysis.N05ReferenceFullAngularSobolev

/-!
# Reconstructing all positive angular jets of an actual output

The high spectral energy and the original low-mode energy control an
actual periodic weak jet. This statement applies equally to the physical
inverse and to its previously identified normal derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem n05_referenceOutput_positiveAngular_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M a : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hU : OutputRealization D γ M a U) {b : ℕ} (hb : 0 < b)
    (hs : Summable (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
      n05_referenceHighOutputSquare D γ M U n)) :
    ∃ d : PolarPoint → ℝ,
      n05_weakReferenceAngularJet D U.1 d b ∧
      MemLp d 2 (referenceWeightedMeasure D γ (-M)) ∧
      outputNormSquare D γ M 0 (d, 0) ≤
        2 * ((∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          n05_referenceHighOutputSquare D γ M U n) +
            (2 : ℝ) ^ (2 * b) * outputNormSquare D γ M a U) ∧
      Function.Periodic d (0, Real.pi) := by
  have hab := hD.choose_spec.1.2.1.le
  have hpart := hD.choose_spec.2.1
  obtain ⟨d, hwd, hd, hbd, hdperiodic⟩ :=
    n05_referenceOutput_highWeakAngularJet hD hborder hγ hU b hs
  obtain ⟨he, hbe⟩ := n05_referenceLowAngularJet_output_bound hab hpart hU hb
  obtain ⟨_, _, hphysical⟩ := n05_referenceWeighted_physical_square_bound hD hγ (-M)
  have hdp := (hphysical d hd).1
  have hep := (hphysical (n05_referenceLowAngularJet b U.1) he).1
  have hu : MemLp U.1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ ⟨a, hU⟩
  have hprod : MemLp U.1 2 ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hu
  have hlow : MemLp (referenceBasisProjection {0, 1} U.1) 2
      (radialPhysicalMeasure D) := by
    simpa only [radialPhysicalMeasure_eq_prod] using memLp_referenceBasisProjection_prod hprod {0, 1}
  have hwhole := n05_weakReferenceAngularJet_add hab (hu.sub hlow) hlow hdp hep hwd
    (n05_referenceLowAngularJet_weak D U.1 b)
  have hw : n05_weakReferenceAngularJet D U.1 (d + n05_referenceLowAngularJet b U.1) b := by
    simpa only [n05_referenceHighPart, sub_add_cancel] using hwhole
  refine ⟨d + n05_referenceLowAngularJet b U.1, hw, hd.add he, ?_,
    hdperiodic.add (n05_referenceLowAngularJet_periodic b U.1)⟩
  calc
    _ ≤ 2 * (outputNormSquare D γ M 0 (d, 0) +
        outputNormSquare D γ M 0 (n05_referenceLowAngularJet b U.1, 0)) :=
      n05_referenceZeroOutputNormSquare_add_le hab hpart hd he
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hbd.le hbe) (by norm_num)

end ContinuousFlexibility.Radial
