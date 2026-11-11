import ContinuousFlexibility.Analysis.N07bScalarBridgeConstruction
import ContinuousFlexibility.Analysis.N07bPrimitiveGeometrySource
import ContinuousFlexibility.Analysis.N07bPrimitiveGeometryReference
import ContinuousFlexibility.Analysis.N07bNeighborhood

/-!
# One common neighborhood for the actual scalar/Banach bridge

Both finite geometric estimates choose their constants before the state
and source. Intersecting their neighborhoods preserves every chosen chart,
space, graph and inverse. The source norm has the requested original
grading, while the identification uses the actual reference source built
from the physical solution.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency true

theorem n07b_reference_mem_stateNeighborhood
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
  change stateGrading S base (C.referenceState - C.referenceState) < ε ∧ |(0 : ℝ)| < ε
  simpa only [sub_self, map_zero, abs_zero] using And.intro hε hε

theorem n07b_exists_scalarBanachBridge_on_smaller
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b base : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
    {G : ScalarInverseData S}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hborder : RadialTrueBorder D)
    (hK : N04PartA D S C K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hsref : stateSector S C.referenceState) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ScalarBanachBridgeProperties D S C K V b B P G base' ε' := by
  have href := n07b_reference_mem_stateNeighborhood S C base h06.1
  obtain ⟨bs, εs, Cs, hbs, hεs, hεsle, _, hCs, hsource⟩ :=
    n07b_sourceLift_of_geometric_contract hD hT hS h05.2.1 hK h06.1 hgeom b
  obtain ⟨br, εr, Ar, hbr, hεr, hεrle, _, hAr, hcoeff⟩ :=
    n07b_referenceAngular_bound_of_geometric_contract hD hT hK h06.1 href hsref hgeom b
  let base' : ℕ := max bs br
  let ε' : ℝ := min εs εr
  have hbase' : base ≤ base' := hbs.trans (le_max_left _ _)
  have hε' : 0 < ε' := lt_min hεs hεr
  have hε'le : ε' ≤ ε := (min_le_left _ _).trans hεsle
  have hUs : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C bs εs :=
    n06_stateNeighborhood_mono (le_max_left _ _) (min_le_left _ _)
  have hUr : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C br εr :=
    n06_stateNeighborhood_mono (le_max_right _ _) (min_le_right _ _)
  have hU : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε :=
    n06_stateNeighborhood_mono hbase' hε'le
  have hreferenceSource : ∀ f : S.Source, ∃ F : V.level (3 / 4 : ℝ) 0 b,
      ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
          ((S.height (3 / 4 : ℝ)).decode f.val) := by
    intro f
    obtain ⟨F, _, hF⟩ := hsource (C.referenceState, 0)
      (n07b_reference_mem_stateNeighborhood S C bs hεs) hsref f
    exact ⟨F, hF⟩
  refine ⟨base', ε', hbase', hε', hε'le, b + 1, Nat.le_succ b, Cs, hCs, ?_⟩
  intro z hz hs f
  obtain ⟨F, hFnorm, hF⟩ := hsource z (hUs hz) hs f
  refine ⟨F, ?_, hF, ?_⟩
  · have hQ : 1 ≤ 1 + stateGrading S (b + 1) (z.1 - C.referenceState) + |z.2| := by
      calc
        (1 : ℝ) ≤ 1 + stateGrading S (b + 1) (z.1 - C.referenceState) :=
          le_add_of_nonneg_right (apply_nonneg _ _)
        _ ≤ _ := le_add_of_nonneg_right (abs_nonneg z.2)
    have hCsQ : Cs ≤ Cs *
        (1 + stateGrading S (b + 1) (z.1 - C.referenceState) + |z.2|) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hQ hCs.le
    exact hFnorm.trans (mul_le_mul_of_nonneg_right hCsQ (apply_nonneg _ _))
  · apply n07b_scalarInverse_banach_identification hD hT hS hborder hK h05 h06 hG
      hgeom href hsref hreferenceSource (hU hz) hs hAr ?_ f F hF
    intro m x hx j i
    have h := hcoeff z (hUr hz) hs m x hx j.val (Nat.le_of_lt_succ j.isLt) i
    simpa only [n07bReferenceBulkCoefficient, n07b_canonicalPrimitiveDirection_one,
      n07b_canonicalPrimitiveDirection_two] using h

end ContinuousFlexibility.Analysis
