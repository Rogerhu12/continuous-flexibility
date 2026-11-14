module

public import ContinuousFlexibility.Analysis.N01cActualFlowAngularInduction

/-!
# Positive angular prefixes of the canonical ordinary-flow tower

One genuine tower is selected before the state-order prefix. Finite
uniformization changes only the additive high loss and scalar constant.
It leaves the common domain and every actual derivative unchanged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

theorem n01_ordinaryFlowAngularPositivePrefixBounds_of_orders
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
      r ∈ Icc (C.left i) (C.right i) →
        0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (J : ∀ m, ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m))
    (horders : ∀ N : ℕ, 0 < N →
      OrdinaryFlowAngularOrderBound hS hT hA hB hpos loss N) :
    ∀ K : ℕ, ∃ dK : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m b p, b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
      ∃ Q : SmoothDirections (stateNeighborhood S C base ε)
        (fun z => mixedDerivative 0 b (fun q => C.minusFlow z m q.1 q.2) p),
      ∀ j : ℕ, j ≤ K → 0 < j →
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin j → (AnnularState S × ℝ),
        |Q.D j z v| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
              base (s + loss + dK) (z - (C.referenceState, 0)) v := by
  let p := pairGrading (stateGrading S) realGrading
  let P := fun (k s high : ℕ) (B : ℝ) =>
    ∀ b : ℕ, b ≤ s → ∀ m,
    ∀ Jm : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m),
    ∀ r : ℝ, ∀ hr : r ∈ Icc (C.left m) (C.right m), ∀ θ : ℝ,
    ∀ x ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
      |(ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos m Jm hr b θ).D k x v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight p base high (x - (C.referenceState, 0)) v
  intro K
  have hprefix := n01c_strict_positive_prefix P (K + 1) loss
    (fun k s a b A B hab hApos hAB hraw j hj m Jm r hr θ x hx v =>
      (hraw j hj m Jm r hr θ x hx v).trans
        (n01c_materialOneHigh_mono p (jointStateGrading_monotone S) base hab
          hApos.le hAB
          (hT.2.1 _ (materialSample_mem_radialCore
            hT hA.1.1.choose_spec.2.1 (C.cell m))).2.1.le
          (hE _ (materialSample_mem_radialCore
            hT hA.1.1.choose_spec.2.1 (C.cell m)))
          (3 / 4 : ℝ) (x - (C.referenceState, 0)) v))
    (fun k _ hk => horders k hk)
  refine n01c_transport_offset_bounds _ _ hprefix ?_
  intro dK s B hBpos hbound m b q hb hq
  have hqc : q.1 ∈ Icc (C.left m) (C.right m) := ⟨hq.1.le, hq.2.le⟩
  refine ⟨ordinaryFlowMixedZeroSmoothDirections hS hT hA hB hpos m (J m) b q hqc, ?_⟩
  intro j hj hjpos z hz v
  change |(ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos
    m (J m) hqc b q.2).D j z v| ≤ _
  have h := hbound j (Nat.lt_succ_of_le hj) hjpos
    b hb m (J m) q.1 hqc q.2 z hz v
  have hsample := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
  exact h.trans (n01c_materialOneHigh_mono p (jointStateGrading_monotone S)
    base (by omega) hBpos.le le_rfl (hT.2.1 _ hsample).2.1.le (hE _ hsample)
    (3 / 4 : ℝ) (z - (C.referenceState, 0)) v)

end ContinuousFlexibility.Blueprint
