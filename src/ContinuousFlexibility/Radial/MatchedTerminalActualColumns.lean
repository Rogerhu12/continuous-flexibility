module

public import ContinuousFlexibility.Radial.MatchedTerminalExternalColumns
public import ContinuousFlexibility.Radial.MatchedInnerActualSource

/-!
# The terminal correction uses the same actual finite-chain inverse

The original physical terminal source is placed in the existing
supported Hilbert space. Frozen uniqueness identifies its correction
with C.inverse for that same chain C. No Poisson or inverse identity
is added as an assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

theorem terminalRegional_innerPoisson_same_actual_inverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hw : ContDiff ℝ ∞ D.w) {n : ℕ} (G : InnerRadialChainGeometry D n)
    (R : TerminalRegionalData D)
    (hM : MatchingLocalRealizations D R.matching)
    (hleft : R.matching.innerLeft = G.left 0)
    (hright : R.matching.innerRight = G.right (Fin.last n))
    (central : Fin (n + 1)) (column : RadialModeL2 D)
    (hcolumn : column = matchingBorderVector D hD hB)
    (hcolfix : innerL2PieceProjection (radialHilbertMeasure D)
      (Ioo (G.left central) (G.right central)) column = column)
    (C : InnerRadialActualChain D G (decide (R.matching.frequency = 2))
      (R.matching.frequency : ℝ) central column)
    (hS : IsUnit C.fluxMatrix) (i : Fin 2) :
    ∃ Z : InnerRadialPhysicalSource D G (decide (R.matching.frequency = 2)),
      Z.val = WithLp.toLp 2
        (terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
          (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i)) ∧
      WithLp.toLp 2 (R.matching.innerPoisson i) =
        WithLp.toLp 2
          (terminalCapInnerLift hD R.matching.innerLeft R.matching.innerRight
            (R.matching.boundaryScale i) (R.cutoff_smooth i) (R.standIn_smooth i)) -
          (C.inverse hw hS Z).val := by
  let F := terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
    (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i)
  have hFs : F.2 = 0 := rfl
  have hfix : R.matching.sourceInner F = F := by
    rw [R.inner_source F]
    exact modeInnerSource_idempotent D R.matching.innerLeft R.matching.innerRight _
  have hmem : WithLp.toLp 2 F ∈ innerSupportedAdmissibleSource
      (radialHilbertMeasure D) (innerRadialChainRegion D G)
        (decide (R.matching.frequency = 2)) := by
    rw [← hfix]
    exact matchedInner_sourceInner_mem hD G R.matching hM hleft hright F (fun _ => hFs)
  let Z : InnerRadialPhysicalSource D G (decide (R.matching.frequency = 2)) :=
    ⟨WithLp.toLp 2 F, hmem⟩
  have hsub : Icc R.matching.innerLeft R.matching.innerRight ⊆ radialCore D := by
    intro r hr
    exact ⟨R.cut_order.1.trans_le hr.1, hr.2.trans_lt R.cut_order.2.2⟩
  have hC :
      R.matching.innerInverse F =
        ((C.inverse hw hS Z).val.fst, (C.inverse hw hS Z).val.snd) := by
    simpa only [Z, WithLp.toLp_fst, WithLp.toLp_snd] using
      matchedInnerActualInverse_eq_innerInverse hD hB hw G R.matching hleft hright hsub
        central column hcolumn hcolfix C hS hM Z
  have hC' : WithLp.toLp 2 (R.matching.innerInverse F) = (C.inverse hw hS Z).val :=
    congrArg (WithLp.toLp 2) hC
  refine ⟨Z, rfl, ?_⟩
  rw [terminalRegional_innerPoisson_eq hD hB R hM i, WithLp.toLp_sub]
  exact congrArg (fun z => WithLp.toLp 2
    (terminalCapInnerLift hD R.matching.innerLeft R.matching.innerRight
      (R.matching.boundaryScale i) (R.cutoff_smooth i) (R.standIn_smooth i)) - z) hC'

end ContinuousFlexibility.Radial
