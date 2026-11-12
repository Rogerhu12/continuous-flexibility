import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Analysis.N04bActualAtlasCuts
import ContinuousFlexibility.Analysis.N04bActualRootDensity
import ContinuousFlexibility.Analysis.N04bActualRootTransmission
import ContinuousFlexibility.Analysis.N04bGeometricCompletion

/-!
# N04b: canonical coordinates of the actual corrected field

The actual corrected characteristic flow constructs the travel chart.
Its two moving physical halves use the regularized root charts, genuine
closed inverse extensions, and the actual density height. One enumeration
indexes this atlas and its reference optical cut metadata.

The input consists only of the cumulative N01--N03 construction and raw
coefficient regularity and type. Every chart, closed inverse, partition,
operator identity, cut transmission identity and positive divided
difference is a conclusion.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 992--1303.
Task: docs/tasks/N04b-CanonicalConstruction.md.
-/

namespace ContinuousFlexibility.Blueprint

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem N04bCanonicalConstruction
    (A : RadialReference) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (base loss : ℕ) (ε : ℝ)
    (hT : IsMaterialData A.val T) (hS : IsPhysicalSpaces A.val T S)
    (h03 : NonlinearPropertiesThrough03 A.val T S C R L base loss ε)
    (hfield : N04bFieldRegularity A.val S C L base ε) :
    ∃ K : CanonicalData S,
      N04PartA A.val S C K base ε ∧ N04PartB S C L K base ε := by
  obtain ⟨e, hA, hcut⟩ := n04b_exists_actual_typed_atlas hT hS h03 hfield
  let K := n04bActualTypedAtlas hT hS h03 hfield e
  apply n04b_complete_geometric_atlas (K := K) hA hfield hcut
  · intro z hz hs u hu m θ
    have hg := n04bActualTypedAtlas_cut_germs hT hS h03 hfield e hz hs m θ
    have ht := n04b_actualRoot_cut_transmission h03 hS hT hfield hz hs m K
      (fun side => e.symm (.inl (m, side))) θ hg.1 hg.2 u hu
    simpa only [K, n04bActualTypedAtlas, n04bTypedAtlasData_cutPair,
      n04bTypedAtlasData_cutRadius] using ht
  · intro z hz hs k hnegative x hx
    cases hi : e k with
    | inl i =>
      rcases i with ⟨m, side⟩
      have hxHalf : x ∈ n04bActualNegativeDomain S C L z m side := by
        simpa only [K, n04bActualTypedAtlas, n04bTypedAtlasData_physicalPieceOpen,
          hi, n04bTypedPhysicalDomain, n04bActualNegativeDomain] using hx
      have hxFull := n04b_actualNegativeDomain_subset_component C L z m side hxHalf
      have hg := n04bActualTypedAtlas_negative_component_germs
        hT hS h03 hfield e hz hs k m side hi hxFull
      exact n04b_actualRootDensity_germ h03 hS hT hfield hz hs m side
        hxFull (n04bTravelHalfDomain_oriented_pos hxHalf) hg.1 hg.2.self_of_nhds
    | inr i =>
      simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_positive,
        hi, n04TypedPiecePositive, Bool.true_eq_false] at hnegative

/--
info: 'ContinuousFlexibility.Blueprint.N04bCanonicalConstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Blueprint.N04bCanonicalConstruction

end ContinuousFlexibility.Blueprint
