module

public import ContinuousFlexibility.Radial.ReferenceZeroModeUniqueness
public import ContinuousFlexibility.Radial.MatchedModeDomainEmbedding
public import ContinuousFlexibility.Radial.ReferenceTestIntegrability

/-!
# Triviality of the actual homogeneous reference graph

The weighted domains supply genuine modal Hilbert vectors. The already
constructed modal inverse kills each positive even homogeneous mode,
including the border scalar at frequency two. The zero channel is
excluded by its actual endpoint norm. Local cosine completeness then
gives equality of the physical field almost everywhere.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal

theorem exists_referenceGraph_homogeneous_unique {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hmode : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ G : RadialModePair D →L[ℝ] RadialModePair D,
        ModeInverseProperties D j G) :
    ∃ Mmin : ℝ, 0 < Mmin ∧
      ∀ γ : ℝ, 0 < γ → ∀ M₀ : ℝ, Mmin ≤ M₀ → ∀ M₁ : ℝ,
      ∀ U : RadialUnknown, ReferenceGraph D γ M₀ M₁ U 0 →
        RadialRepresentativeEq D U 0 := by
  obtain ⟨Mmin, hMmin, hgraphs⟩ := exists_referenceGraph_modeFullGraph hD hB
  refine ⟨Mmin, hMmin, ?_⟩
  intro γ hγ M₀ hM₀ M₁ U hU
  have hmodal (n : ℕ) :
      (referenceMode U.1 (2 * (n + 1)) =ᵐ[volume.restrict (radialCore D)]
        (fun _ => (0 : ℝ))) ∧
        (if 2 * (n + 1) = 2 then U.2 else 0) = 0 := by
    obtain ⟨u, f, hu, hf, hgraph⟩ := hgraphs γ hγ M₀ hM₀ M₁ U 0 hU n
    have hfzero : (f : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (fun _ => (0 : ℝ)) := by
      simpa only [Prod.fst_zero, Pi.zero_apply, referenceMode, radialAngularMean,
        zero_mul, intervalIntegral.integral_zero, mul_zero, neg_zero, zero_div] using hf
    have hf0 : f = 0 := by
      apply Lp.ext
      exact Filter.EventuallyEq.trans hfzero
        (Filter.EventuallyEq.symm (Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)))
    obtain ⟨G, hG⟩ := hmode (2 * (n + 1)) (by omega) ⟨n + 1, by omega⟩
    have hsource : (f, if 2 * (n + 1) = 2 then (0 : RadialSource).2 else 0) =
        (0 : RadialModePair D) := by
      apply Prod.ext
      · exact hf0
      · simp only [Prod.snd_zero, ite_self]
    have heq := hG.2
      (u, -(if 2 * (n + 1) = 2 then U.2 else 0))
      (f, if 2 * (n + 1) = 2 then (0 : RadialSource).2 else 0) hgraph
    rw [hsource, map_zero] at heq
    have hu0 : u = 0 := (congrArg Prod.fst heq).symm
    have hscalar : (if 2 * (n + 1) = 2 then U.2 else 0) = 0 := by
      have hs := congrArg Prod.snd heq
      change 0 = -(if 2 * (n + 1) = 2 then U.2 else 0) at hs
      exact neg_eq_zero.mp hs.symm
    refine ⟨?_, hscalar⟩
    apply (Radial.radialHilbertMeasure_ae_iff hD).mp
    rw [hu0] at hu
    exact Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hu)
      (Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D))
  refine ⟨?_, ?_⟩
  · simpa only [Nat.zero_add, zero_add, Nat.mul_one, ite_true, Prod.snd_zero] using
      (hmodal 0).2
  · have hcell := hU.1.radialCellIntegrable hD hB
    have hzero : RadialCellIntegrable D (fun _ => (0 : ℝ)) := by
      simpa only [zero_mul] using hcell.const_mul 0
    obtain ⟨aL, hout⟩ := hU.1
    apply hcell.cosineCoefficients_ae_injective hD.choose_spec.2.1 hzero
      hout.2.2.1 (fun _ => rfl) hout.2.2.2 (fun _ _ => rfl)
    intro n
    have hz : referenceCosineCoefficient (fun _ : PolarPoint => (0 : ℝ)) n =
        (fun _ => (0 : ℝ)) := by
      funext r
      simp only [referenceCosineCoefficient, referenceCosineCoeff, zero_mul, integral_zero]
    rw [hz]
    cases n with
    | zero =>
        have hcoef : referenceCosineCoefficient U.1 0 =
            (fun r => radialAngularMean (fun θ => U.1 (r, θ))) := by
          funext r
          exact referenceCosineCoeff_zero (fun θ => U.1 (r, θ))
        rw [hcoef]
        exact hU.zeroMode_eq_zero hD hB hγ
    | succ n =>
        simpa only [referenceCosineCoefficient_succ_eq_referenceMode] using (hmodal n).1

end ContinuousFlexibility.Statements
