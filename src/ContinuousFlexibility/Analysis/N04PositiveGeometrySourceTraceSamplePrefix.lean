import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceBoundaryTraces

/-!
# Sampled positive radial source traces

The fixed radial unit-vector evaluation and either coordinate projection
have norm at most one. The original source prefix therefore supplies all
positive endpoint traces with the same low order, shift and sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04PositiveGeometry_sourceProjectedTrace_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side),
      ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ L : PolarPoint →L[ℝ] ℝ, ‖L‖ ≤ 1 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y => radialBoundaryJet (fun p => L
          (n04PositiveSourceMap (X.src i side) (W.A X.e₀)
            (liftSectorParameter W.S W.C y.1) p)) (n04PositiveEndpoint i side) j y.2),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      N04BoundaryWordBounds Q K s 1 z θ
        (fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
          pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R)
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ))
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) shift := by
  let data := n04PositiveGeometry_sourceJet_sample_prefix W X hb hε hεW hεone hflow
  refine ⟨data.choose, data.choose_spec.1, fun K => ?_⟩
  let prefixData := data.choose_spec.2 K
  refine ⟨prefixData.choose, fun s => ?_⟩
  let orderData := prefixData.choose_spec s
  refine ⟨orderData.choose, orderData.choose_spec.1, ?_⟩
  intro i side m hm hctx j hj hj4 L hL Q z hz hzlow θ R hR hzR
  let J := n04PositiveGeometry_sourceJet_joint W X hb hε hεW hεone hflow
    i side m hm hctx j hj hj4
  exact (orderData.choose_spec.2 i side m hm hctx j hj hj4 J z hz hzlow θ R hR hzR).radialProjection
    (n04PositiveGeometry_source_root_smooth (X := X) hb hεW i side) L hL hz Q

end ContinuousFlexibility.Analysis
