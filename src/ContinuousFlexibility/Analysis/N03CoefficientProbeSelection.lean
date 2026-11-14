import ContinuousFlexibility.Analysis.N03CorrectedCoefficientJetBounds
import ContinuousFlexibility.Analysis.PositiveConformalCanonicalExtension

/-!
# Fixed genuine height probes for every negative component

The closed component lies strictly inside the annulus. A fixed smooth
radial cutoff is therefore one near that whole component and has compact
support inside the annulus. The four even periodic fields are realized
as actual height elements before choosing any state. Their finite
seminorms enter only the component and order constants.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem exists_negativeComponent_coefficientProbes
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S)
    (hinterval : ∀ m, D.a < C.left m ∧ C.left m < C.right m ∧ C.right m < D.b) :
    ∃ χ : ℕ → ℝ → ℝ, ∃ η : ℕ → Fin 4 → HeightPair S,
      (∀ m, ContDiff ℝ ∞ (χ m)) ∧
      (∀ m r, r ∈ Ioo (C.left m) (C.right m) → χ m r = 1) ∧
      ∀ m, heightPairField S (η m 0) = radialLinearProbe (χ m) ∧
        heightPairField S (η m 1) = radialCosineProbe (χ m) ∧
        heightPairField S (η m 2) =
          (fun p => radialLinearProbe (χ m) p * radialCosineProbe (χ m) p) ∧
        heightPairField S (η m 3) =
          (fun p => radialCosineProbe (χ m) p * radialCosineProbe (χ m) p) := by
  classical
  have heach (m : ℕ) : ∃ χ : ℝ → ℝ, ∃ η : Fin 4 → HeightPair S,
      ContDiff ℝ ∞ χ ∧
      (∀ r ∈ Ioo (C.left m) (C.right m), χ r = 1) ∧
      heightPairField S (η 0) = radialLinearProbe χ ∧
      heightPairField S (η 1) = radialCosineProbe χ ∧
      heightPairField S (η 2) = (fun p => radialLinearProbe χ p * radialCosineProbe χ p) ∧
      heightPairField S (η 3) = (fun p => radialCosineProbe χ p * radialCosineProbe χ p) := by
    obtain ⟨χ, hχ, hsupp, hone⟩ := exists_bufferedRadialCutoff
      (hinterval m).1 (hinterval m).2.1.le (hinterval m).2.2
    have hcompact : IsCompact (tsupport χ) :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ)
        (fun r hr => Ioo_subset_Icc_self (hsupp hr))
    obtain ⟨ηr, ηc, ηrc, ηcc, hηr, hηc, hηrc, hηcc⟩ :=
      exists_heightPair_coefficientProbes hT hS hχ hcompact hsupp (subset_tsupport χ)
    refine ⟨χ, ![ηr, ηc, ηrc, ηcc], hχ, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      exact (hone r (Ioo_subset_Icc_self hr)).eq_of_nhds
    · simpa using hηr.2
    · simpa using hηc.2
    · simpa using hηrc.2
    · simpa using hηcc.2
  choose χ η hχ hone hηr hηc hηrc hηcc using heach
  exact ⟨χ, η, hχ, hone, fun m => ⟨hηr m, hηc m, hηrc m, hηcc m⟩⟩

/-- All probe inputs are now constructed from the original physical
spaces and the fixed component endpoints. The common neighborhood and
loss precede every component and every mixed derivative order. -/
theorem n03_correctedCoefficient_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε) (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) :
    ∃ outLoss low : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ m a b : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      N03CorrectedCoefficientBoundAtOrder D S C L base ε low δ outLoss m a b B := by
  obtain ⟨χ, η, hχ, hone, hη⟩ := exists_negativeComponent_coefficientProbes
    hT hS C hN01.2.2.2.1.1
  exact n03_correctedCoefficient_fixed_loss_of_probes
    (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (K := K)
    (base := base) (loss := loss) (ε := ε) hS hT hN01 hN02 hN03 hA hB χ hχ hone η hη

end ContinuousFlexibility.Analysis
