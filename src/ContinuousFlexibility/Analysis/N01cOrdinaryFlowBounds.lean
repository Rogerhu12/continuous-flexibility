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

private theorem n01c_flowBounds_of_threeNeighborhoods
    {base : ℕ} {ε : ℝ}
    {Angular Radial Positive Smooth Extra Result : ℕ → ℝ → Prop}
    (ha : ∃ ba : ℕ, ∃ ea : ℝ, base ≤ ba ∧ 0 < ea ∧ ea ≤ min ε (1 / 2) ∧
      ∀ b : ℕ, ba ≤ b → ∀ e : ℝ, 0 < e → e ≤ ea → Angular b e)
    (hr : ∃ br : ℕ, ∃ er : ℝ, base ≤ br ∧ 0 < er ∧ er ≤ min ε (1 / 2) ∧
      ∀ b : ℕ, br ≤ b → ∀ e : ℝ, 0 < e → e ≤ er → Radial b e)
    (hg : ∃ bg : ℕ, ∃ eg : ℝ, base ≤ bg ∧ 0 < eg ∧ eg ≤ ε ∧
      Positive bg eg ∧ Smooth bg eg ∧ Extra bg eg)
    (hresult : ∀ (bg : ℕ) (eg : ℝ) (b : ℕ) (e : ℝ),
      bg ≤ b → e ≤ eg → base ≤ b → 0 < e → e ≤ ε → e ≤ 1 / 2 →
      Smooth bg eg → Angular b e → Radial b e → Result b e) :
    ∃ b : ℕ, ∃ e : ℝ, base ≤ b ∧ 0 < e ∧ e ≤ ε ∧ Result b e := by
  obtain ⟨ba, ea, _, hea, heae, hangular⟩ := ha
  obtain ⟨br, er, _, her, _, hradial⟩ := hr
  obtain ⟨bg, eg, hbg, heg, hege, _, hsmooth, _⟩ := hg
  let b : ℕ := max bg (max ba br)
  let e : ℝ := min eg (min ea er)
  have hgb : bg ≤ b := le_max_left _ _
  have hab : ba ≤ b := (le_max_left ba br).trans (le_max_right _ _)
  have hrb : br ≤ b := (le_max_right ba br).trans (le_max_right _ _)
  have hb : base ≤ b := hbg.trans hgb
  have he : 0 < e := lt_min heg (lt_min hea her)
  have heg' : e ≤ eg := min_le_left _ _
  have hea' : e ≤ ea := (min_le_right _ _).trans (min_le_left _ _)
  have her' : e ≤ er := (min_le_right _ _).trans (min_le_right _ _)
  have heε : e ≤ ε := heg'.trans hege
  have he2 : e ≤ 1 / 2 := hea'.trans (heae.trans (min_le_right _ _))
  exact ⟨b, e, hb, he, heε, hresult bg eg b e hgb heg' hb he heε he2 hsmooth
    (hangular b hab e he hea') (hradial b hrb e he her')⟩

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
  exact n01c_flowBounds_of_threeNeighborhoods
    (n01_exists_ordinaryFlowAngularPositivePrefixBounds hS hT hA hε hB hG hE hSpeed)
    (n01_exists_ordinaryFlowRadialPositivePrefixBounds hS hT hA hε hB hG hE hSpeed)
    (n01_exists_common_cosineLowGeometry hS hT hA hε hB hG hSpeed)
    (fun bg εg base' ε' hgba hε'g hb hε' hε'ε hε'2 hcos ha hr => by
      have hB' : N01PartB D S C base' ε' := n01PartB_mono hB hb hε'ε
      have hsample : ∀ m, T.sample m ∈ Ioo D.a D.b :=
        materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1
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
          (fun m => hE _ (hsample (C.cell m))) ha hr)

end ContinuousFlexibility.Blueprint
