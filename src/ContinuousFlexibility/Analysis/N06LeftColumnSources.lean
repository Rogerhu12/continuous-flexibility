import ContinuousFlexibility.Analysis.N06LeftColumnDifferenceBound
import ContinuousFlexibility.Analysis.N06LeftColumnSymmetry
import ContinuousFlexibility.Analysis.N06CurrentCompactSources
import ContinuousFlexibility.Analysis.N06CanonicalWeakTransport

/-!
# The actual left-column sources

Both the current left column and its physical difference from the
reference left column belong to the original source model at each fixed
admissible state. The last identity displays separately the physical
coefficient difference and the current coordinate change of the fixed
reference column. No uniform bound for that coordinate change is asserted.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}

theorem n06_leftColumnDifference_eq_current_sub_reference
    (hS : IsPhysicalSpaces D T S) (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε) (z : AnnularState S × ℝ) :
    n06LeftColumnDifference D S L z = fun p =>
      n06CurrentLeftColumn S L z p -
        n06CurrentLeftColumn S L (C.referenceState, 0) p := by
  funext p
  exact congrArg (fun a : ℝ => n06CurrentLeftColumn S L z p - a)
    (n06_currentLeftColumn_reference hS h01 h03 p).symm

theorem n06_leftColumnDifference_regular
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    ContDiff ℝ ∞ (n06LeftColumnDifference D S L z) ∧
      Function.Periodic (n06LeftColumnDifference D S L z) (0, Real.pi) ∧
      ∀ p : PolarPoint, n06LeftColumnDifference D S L z (p.1, -p.2) =
        n06LeftColumnDifference D S L z p := by
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  rw [n06_leftColumnDifference_eq_current_sub_reference hS h01 h03 z]
  refine ⟨(n06_currentLeftColumn_contDiff hT hS h01 h03 hz hs).sub
    (n06_currentLeftColumn_contDiff hT hS h01 h03 href hsector),
    (n06_currentLeftColumn_periodic hS h03 hz hs).sub
      (n06_currentLeftColumn_periodic hS h03 href hsector), ?_⟩
  intro p
  exact congrArg₂ (fun a b : ℝ => a - b)
    (n06_currentLeftColumn_even hT hS h01 h03 hz hs p)
    (n06_currentLeftColumn_even hT hS h01 h03 href hsector p)

theorem n06_leftColumnDifferences_commonSupport
    (hS : IsPhysicalSpaces D T S) (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ radialCore D ∧
      ∀ z : AnnularState S × ℝ, ∀ r, r ∉ J → ∀ θ,
        n06LeftColumnDifference D S L z (r, θ) = 0 := by
  obtain ⟨J, hJ, hJD, _hpos, hzero⟩ := hS.2.2.1.2.2
  exact ⟨J, hJ, hJD, fun z r hr θ =>
    n06_leftColumnDifference_zero_off_cutoff hS h01 h03 hJ.isClosed hzero z
      (p := (r, θ)) hr⟩

/-- This is fixed-state source membership for the actual current column;
there is no fixed-support normalization hypothesis. -/
theorem n06Volume_exists_current_leftColumnSource
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hV : IsVolumeModel T S K V)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (γ t : ℝ) (b : ℕ) :
    ∃ F : V.level γ t b,
      ∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K z m (n06CurrentLeftColumn S L z) := by
  obtain ⟨J, hJ, hJD, _hpos, hzero⟩ :=
    n06_currentLeftColumns_commonSupport (L := L) hS
  exact n06Volume_exists_current_compact_source h01.1.1 h01.2.2.2.1
    hT hV h04 hcoordinates hz hs
    γ t b (n06_currentLeftColumn_contDiff hT hS h01 h03 hz hs)
    (n06_currentLeftColumn_periodic hS h03 hz hs)
    (n06_currentLeftColumn_even hT hS h01 h03 hz hs)
    ⟨J, hJ, hJD, hzero z⟩

/-- The true physical difference also gives a source in the current
coordinates at each admissible state. Uniform smallness in reference
coordinates is supplied separately by the fixed-support source bound. -/
theorem n06Volume_exists_current_leftDifferenceSource
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hV : IsVolumeModel T S K V)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (γ t : ℝ) (b : ℕ) :
    ∃ F : V.level γ t b,
      ∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K z m (n06LeftColumnDifference D S L z) := by
  obtain ⟨J, hJ, hJD, hzero⟩ := n06_leftColumnDifferences_commonSupport hS h01 h03
  have hf := n06_leftColumnDifference_regular hT hS h01 h03 hz hs
  exact n06Volume_exists_current_compact_source h01.1.1 h01.2.2.2.1
    hT hV h04 hcoordinates hz hs
    γ t b hf.1 hf.2.1 hf.2.2 ⟨J, hJ, hJD, hzero z⟩

/-- The unestimated term is exactly the current coordinate transform of
the fixed reference left source. This identity does not identify the
current atlas with the reference atlas. -/
theorem n06_currentLeftSourceDifference_decomposition
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) :
    canonicalSource S K z m (n06CurrentLeftColumn S L z) p -
        canonicalSource S K (C.referenceState, 0) m
          (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)) p =
      canonicalSource S K z m (n06LeftColumnDifference D S L z) p +
        (canonicalSource S K z m
            (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)) p -
          canonicalSource S K (C.referenceState, 0) m
            (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)) p) := by
  have hd : canonicalSource S K z m (n06LeftColumnDifference D S L z) p =
      canonicalSource S K z m (n06CurrentLeftColumn S L z) p -
        canonicalSource S K z m
          (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)) p := by
    change canonicalSource S K z m
        (fun q => n06CurrentLeftColumn S L z q -
          n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) q) p =
      canonicalSource S K z m (n06CurrentLeftColumn S L z) p -
        canonicalSource S K z m
          (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)) p
    simpa only [one_mul] using
      n06_canonicalSource_sub_smul (S := S) (K := K) (z := z) (m := m)
        (n06CurrentLeftColumn S L z)
        (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)) 1 p
  rw [hd]
  ring

end ContinuousFlexibility.Statements
