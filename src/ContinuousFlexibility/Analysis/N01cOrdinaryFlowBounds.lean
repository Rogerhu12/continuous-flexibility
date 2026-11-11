import ContinuousFlexibility.Analysis.N01cOrdinaryFlowAngularBounds
import ContinuousFlexibility.Analysis.N01cOrdinaryFlowRadialBounds
import ContinuousFlexibility.Analysis.N01cFlowPositivePrefix
import ContinuousFlexibility.Analysis.N01cOrdinaryFlowReferenceBounds
import ContinuousFlexibility.Analysis.N01cCommonCosineGeometry
import ContinuousFlexibility.Analysis.N01cPhysicalFlowRegularity

/-!
# The actual ordinary-flow family on one common neighborhood

The angular and positive-radial estimates choose their bases before every
parameter order. Their intersection retains those choices. The genuine
first parameter derivative then controls the reference-subtracted zero
jet along the reference segment.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

theorem n01_exists_ordinaryFlowFamilyTameBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      OrdinaryFlowFamilyTameBounds T S C base' loss ε' := by
  obtain ⟨ba, εa, hba, hεa, hεaε, ha⟩ :=
    n01_exists_ordinaryFlowAngularPositivePrefixBounds hS hT hA hε hB hG hE hSpeed
  obtain ⟨br, εr, hbr, hεr, hεrε, hr⟩ :=
    n01_exists_ordinaryFlowRadialPositivePrefixBounds hS hT hA hε hB hG hE hSpeed
  obtain ⟨bg, εg, hbg, hεg, hεgε, hpos, hcos, M, hM, hgeometry⟩ :=
    n01_exists_common_cosineLowGeometry hS hT hA hε hB hG hSpeed
  let base' : ℕ := max bg (max ba br)
  let ε' : ℝ := min εg (min εa εr)
  have hgba : bg ≤ base' := le_max_left _ _
  have haba : ba ≤ base' := (le_max_left ba br).trans (le_max_right _ _)
  have hrba : br ≤ base' := (le_max_right ba br).trans (le_max_right _ _)
  have hb : base ≤ base' := hbg.trans hgba
  have hε' : 0 < ε' := lt_min hεg (lt_min hεa hεr)
  have hε'g : ε' ≤ εg := min_le_left _ _
  have hε'a : ε' ≤ εa := (min_le_right _ _).trans (min_le_left _ _)
  have hε'r : ε' ≤ εr := (min_le_right _ _).trans (min_le_right _ _)
  have hε'ε : ε' ≤ ε := hε'g.trans hεgε
  have hε'2 : ε' ≤ 1 / 2 := hε'a.trans (hεaε.trans (min_le_right _ _))
  have hB' : N01PartB D S C base' ε' := n01PartB_mono hB hb hε'ε
  have hsample : ∀ m, T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1
  refine ⟨base', ε', hb, hε', hε'ε, ?_⟩
  apply ordinaryFlowFamilyTameBounds_of_positive_prefix hT hA.1.1 hε' hε'2 hE
  · intro z hz m
    exact contDiffOn_minusFlow_of_cosineSpeed hS hT hA hB' hz m
      (hcos z (stateNeighborhood_subset hgba hε'g hz) m)
  · exact combine_mixed_positive_prefix_bounds
      (X := AnnularState S × ℝ) (U := stateNeighborhood S C base' ε')
      (fun m q => q.1 ∈ Ioo (C.left m) (C.right m))
      (fun m a b q z => mixedDerivative a b (fun q => C.minusFlow z m q.1 q.2) q)
      (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
      base' loss (C.referenceState, 0)
      (fun m a q => min (q.1 - C.left m) (C.right m - q.1) ^ a)
      (fun _ _ => pow_zero _)
      (fun m => T.H (T.sample (C.cell m)))
      (fun m => T.E0 (T.sample (C.cell m)))
      (fun m => (hT.2.1 _ (hsample (C.cell m))).2.1.le)
      (fun m => hE _ (hsample (C.cell m)))
      (ha base' haba ε' hε' hε'a)
      (hr base' hrba ε' hε' hε'r)

end ContinuousFlexibility.Blueprint
