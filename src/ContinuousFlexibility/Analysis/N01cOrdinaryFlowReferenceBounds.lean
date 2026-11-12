import ContinuousFlexibility.Analysis.N01cStateInterpolation
import ContinuousFlexibility.Analysis.N01cFlowReferenceDifference
import ContinuousFlexibility.Analysis.N01cBoundsRestriction

/-! Specialize the weighted reference-segment argument to the actual
ordinary flows, on the one state neighborhood chosen before all orders. -/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true in
theorem ordinaryFlowFamilyTameBounds_of_positive_prefix
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hsmooth : ∀ z ∈ stateNeighborhood S C base ε, ∀ m,
      ContDiffOn ℝ ∞ (fun q : PolarPoint => C.minusFlow z m q.1 q.2)
        (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hpositive : ∀ K : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m a b q, a + b ≤ s → q.1 ∈ Ioo (C.left m) (C.right m) →
      ∃ J : SmoothDirections (stateNeighborhood S C base ε)
        (fun z => mixedDerivative a b (fun q => C.minusFlow z m q.1 q.2) q),
        ∀ j : ℕ, j ≤ K → 0 < j → ∀ z ∈ stateNeighborhood S C base ε,
        ∀ v : Fin j → (AnnularState S × ℝ),
          min (q.1 - C.left m) (C.right m - q.1) ^ a * |J.D j z v| ≤
            B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
              T.E0 (T.sample (C.cell m)) ^ B *
                oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
                  base (s + loss + d) (z - (C.referenceState, 0)) v) :
    OrdinaryFlowFamilyTameBounds T S C base loss ε := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  have hsample : ∀ m, T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hRef.choose_spec.2.1
  exact mixedDifference_weighted_prefix_bounds
    (X := AnnularState S × ℝ) (U := stateNeighborhood S C base ε)
    (fun m => Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (fun _ => isOpen_Ioo.prod isOpen_univ)
    (fun m z q => C.minusFlow z m q.1 q.2)
    (fun m z hz => hsmooth z hz m)
    (fun m q => q.1 ∈ Ioo (C.left m) (C.right m))
    (fun _ _ hq => ⟨hq, mem_univ _⟩)
    (pairGrading (stateGrading S) realGrading) base loss (C.referenceState, 0)
    (reference_mem_stateNeighborhood S C base hε)
    (fun z hz t ht => stateNeighborhood_reference_segment S C hz ht)
    (fun z hz => (jointStateGrading_displacement_lt_one hε2 hz).le)
    (fun m a q => min (q.1 - C.left m) (C.right m - q.1) ^ a)
    (fun _ a _ hq => pow_pos (lt_min (sub_pos.mpr hq.1) (sub_pos.mpr hq.2)) a)
    (fun m => T.H (T.sample (C.cell m)))
    (fun m => T.E0 (T.sample (C.cell m)))
    (fun m => (hT.2.1 _ (hsample (C.cell m))).2.1.le)
    (fun m => hE _ (hsample (C.cell m))) hpositive

end ContinuousFlexibility.Statements
