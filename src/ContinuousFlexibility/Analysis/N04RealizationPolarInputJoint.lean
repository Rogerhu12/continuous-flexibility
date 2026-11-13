import ContinuousFlexibility.Analysis.N01cCoefficientPolarPowerInputs
import ContinuousFlexibility.Analysis.N01cActualCosineSpeedTower
import ContinuousFlexibility.Analysis.N04RealizationMixedJointDirections
import ContinuousFlexibility.Analysis.SmoothDirectionsOneHighLimit

/-!
# Joint towers of the actual polar height inputs

The existing genuine mixed towers and their full material height gain
give uniform seminorm bounds on the annulus. Joining the two physical
coordinates therefore preserves the caller's original state neighborhood.
This supplies the actual inputs to the finite root coefficient formulas;
no root flow or reference family is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}

/-- The existing polar input tower is uniformly controlled in the physical
point. Material absorption is used here only for joint continuity. -/
theorem n04Realization_polarInput_uniformSeminormBounds
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hD : 0 < D.a) (hε : ε ≤ 1) (i : Fin 5) (a b : ℕ) :
    UniformScalarJetSeminormBounds
      (fun q : annularOpen D =>
        (coefficientPolarInput_regular hS hT hD C base ε i).parameter
          a b q q.property) := by
  apply uniformScalarJetSeminormBounds_of_oneHigh
    (pairGrading (stateGrading S) realGrading)
    (n01c_continuous_jointStateGrading S) (jointStateGrading_monotone S)
    0 (fun _ => a + b + 4)
  intro k
  obtain ⟨C₀, A, hC₀, _, hbound⟩ :=
    stateU_qPolarMixedJets_oneHigh_bound hT hS hD (a + b)
  obtain ⟨B, hB, habsorb⟩ :=
    materialHeight_E0_weight_bounded hT (by norm_num : (0 : ℝ) < 3 / 4) A
  refine ⟨C₀ * B, mul_nonneg hC₀ hB.le, ?_⟩
  intro q z hz v
  let RF := coefficientPolarInput_regular hS hT hD C base ε i
  let J : SmoothDirections (stateNeighborhood S C base ε)
      (fun x => x.2 * mixedDerivative a b (stateUPolarInput S i x.1) q.val) :=
    (RF.parameter a b q q.property).congr (fun x _ =>
      mixedDerivative_const_mul x.2 (stateUPolarInput S i x.1) a b q.val)
  have hj := hbound i a b le_rfl q q.property
    (stateNeighborhood S C base ε) J k 0 (0 : AnnularState S) z hz
    (hz.2.le.trans hε) v
  have hzero : stateGrading S (a + b + 4) (0 : AnnularState S) = 0 :=
    (stateGrading S (a + b + 4)).map_zero'
  have hdisp : z - ((0 : AnnularState S), (0 : ℝ)) = z := sub_zero z
  simp only [hzero, add_zero, mul_one, hdisp] at hj
  have hw : 0 ≤ oneHighVariationWeight
      (pairGrading (stateGrading S) realGrading) 0 (a + b + 4) z v :=
    oneHighVariationWeight_nonneg _ _ _ _ _
  calc
    _ ≤ C₀ * T.E0 q.val.1 ^ A * T.H q.val.1 ^ (3 / 4 : ℝ) *
        oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
          0 (a + b + 4) z v := hj
    _ = C₀ * (T.H q.val.1 ^ (3 / 4 : ℝ) * T.E0 q.val.1 ^ A) *
        oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
          0 (a + b + 4) z v := by ring
    _ ≤ C₀ * B * oneHighVariationWeight
        (pairGrading (stateGrading S) realGrading) 0 (a + b + 4) z v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (habsorb q.val.1 q.property.1) hC₀) hw

/-- Genuine joint state and physical-position jets of each actual polar
height input, on the same original state neighborhood. -/
def n04Realization_polarInputJointDirections
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hD : 0 < D.a) (hε : ε ≤ 1) (i : Fin 5) :
    SmoothDirections (stateNeighborhood S C base ε ×ˢ annularOpen D)
      (fun z : (AnnularState S × ℝ) × PolarPoint =>
        z.1.2 * stateUPolarInput S i z.1.1 z.2) :=
  n04Realization_mixedJointDirections
    (coefficientPolarInput_regular hS hT hD C base ε i)
    (isOpen_stateNeighborhood S C base ε)
    (convex_stateNeighborhood S C base ε)
    isOpen_Ioo (convex_Ioo D.a D.b)
    (n04Realization_polarInput_uniformSeminormBounds hT hS hD hε i)

end ContinuousFlexibility.Analysis
