import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Actual sector flow towers with the retained parameter-order loss

The affine restriction uses the same flow, state neighborhood and
one-high-factor weight. The loss is selected once for the requested
parameter order and remains independent of the spatial order and every
component, point, state and increment.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01SectorOrderStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01SectorOrderParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := Prod.instSMul
local instance n01SectorOrderRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- The new ordinary-flow clause supplies one additional loss for each
parameter order. Restriction to the genuine sector preserves that order
of quantifiers and the exact original weight. -/
theorem N01Properties.sectorFlow_parameterOrder_tower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (k : ℕ) :
    ∃ parameterLoss : ℕ, ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ m b θ r, b ≤ s → r ∈ Ioo (C.left m) (C.right m) →
        ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
          (fun z => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C z)),
        ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → (StateDirections S × ℝ),
          |J.D k z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
              base (s + loss + parameterLoss) z v := by
  have hflows : OrdinaryFlowFamilyTameBounds T S C base loss ε :=
    hN.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨parameterLoss, horder⟩ := hflows k
  refine ⟨parameterLoss, ?_⟩
  intro s
  obtain ⟨B, hB, hdata⟩ := horder s
  refine ⟨B, hB, ?_⟩
  intro m b θ r hb hr
  obtain ⟨J, hJ⟩ := hdata m 0 b (r, θ) (by simpa only [zero_add] using hb) hr
  have hmap : MapsTo (fun z : StateDirections S × ℝ =>
      (C.referenceState, 0) + sectorParameterInclusion S z)
      (sectorNeighborhood S base ε ε) (stateNeighborhood S C base ε) := by
    intro z hz
    exact Eq.mp
      (congrArg (fun u : AnnularState S × ℝ => u ∈ stateNeighborhood S C base ε)
        (liftSectorParameter_eq_affine S C z))
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
  let K : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C z)) :=
    (J.compAffine (sectorParameterInclusion S) (C.referenceState, 0)
      (sectorNeighborhood_isOpen S base ε ε) hmap).congrOn
      (fun z _ => congrArg (ordinaryFlowFamily S C m 0 b (r, θ))
        (liftSectorParameter_eq_affine S C z).symm)
  refine ⟨K, ?_⟩
  intro z hz v
  have hraw := hJ (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (fun i => sectorParameterInclusion S (v i))
  have heq : K.D k z v = J.D k (liftSectorParameter S C z)
      (fun i => sectorParameterInclusion S (v i)) :=
    congrArg (fun y => J.D k y (fun i => sectorParameterInclusion S (v i)))
      (liftSectorParameter_eq_affine S C z).symm
  have hbound : |J.D k (liftSectorParameter S C z)
      (fun i => sectorParameterInclusion S (v i))| ≤
      B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B *
        oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
          base (s + loss + parameterLoss) z v := by
    simpa only [pow_zero, one_mul, oneHighVariationWeight_sector_lift] using hraw
  exact (congrArg abs heq).trans_le hbound

end ContinuousFlexibility.Statements
