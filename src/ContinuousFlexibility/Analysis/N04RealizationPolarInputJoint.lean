import ContinuousFlexibility.Analysis.N01cCoefficientPolarPowerInputs
import ContinuousFlexibility.Analysis.N01cActualCosineSpeedTower
import ContinuousFlexibility.Analysis.N04RealizationMixedJointDirections
import ContinuousFlexibility.Analysis.SmoothDirectionsOneHighLimit
import ContinuousFlexibility.Analysis.StateNeighborhood

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

private theorem polarInput_uniformBounds_of_raw
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
    (p : ℕ → Seminorm ℝ Y)
    (hp : ∀ n, Continuous (pairGrading p realGrading n))
    (hmono : Monotone (pairGrading p realGrading))
    (F : Fin 5 → Y → PolarPoint → ℝ) (Ω : Set PolarPoint)
    (H E : PolarPoint → ℝ) (U : Set (Y × ℝ)) (i : Fin 5) (a b : ℕ)
    (RF : MixedJetRegularity U Ω (fun z q => z.2 * F i z.1 q))
    (hscalar : ∀ z ∈ U, |z.2| ≤ 1)
    (habsorb : ∀ A : ℝ, ∃ B : ℝ, 0 < B ∧
      ∀ q ∈ Ω, H q * E q ^ A ≤ B)
    (hraw : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ i' : Fin 5, ∀ a' b' : ℕ, a' + b' ≤ a + b →
      ∀ q ∈ Ω, ∀ V : Set (Y × ℝ),
      ∀ J : SmoothDirections V
        (fun z => z.2 * mixedDerivative a' b' (F i' z.1) q),
      ∀ k base : ℕ, ∀ x0 : Y, ∀ z ∈ V, |z.2| ≤ 1 →
      ∀ v : Fin k → Y × ℝ,
        |J.D k z v| ≤ C * E q ^ A * H q * (1 + p (a + b + 4) x0) *
          oneHighVariationWeight (pairGrading p realGrading)
            base (a + b + 4) (z - (x0, 0)) v) :
    UniformScalarJetSeminormBounds
      (fun q : Ω => RF.parameter a b q q.property) := by
  apply uniformScalarJetSeminormBounds_of_oneHigh
    (pairGrading p realGrading) hp hmono 0 (fun _ => a + b + 4)
  intro k
  obtain ⟨C₀, A, hC₀, _, hbound⟩ := hraw
  obtain ⟨B, hB, hweight⟩ := habsorb A
  refine ⟨C₀ * B, mul_nonneg hC₀ hB.le, ?_⟩
  intro q z hz v
  let J : SmoothDirections U
      (fun x => x.2 * mixedDerivative a b (F i x.1) q.val) :=
    (RF.parameter a b q q.property).congr (fun x _ =>
      mixedDerivative_const_mul x.2 (F i x.1) a b q.val)
  have hj := hbound i a b le_rfl q q.property U J k 0 (0 : Y) z hz
    (hscalar z hz) v
  have hzero : p (a + b + 4) (0 : Y) = 0 := (p (a + b + 4)).map_zero'
  have hdisp : z - ((0 : Y), (0 : ℝ)) = z := sub_zero z
  simp only [hzero, add_zero, mul_one, hdisp] at hj
  have hw : 0 ≤ oneHighVariationWeight
      (pairGrading p realGrading) 0 (a + b + 4) z v :=
    oneHighVariationWeight_nonneg _ _ _ _ _
  calc
    _ ≤ C₀ * E q.val ^ A * H q.val *
        oneHighVariationWeight (pairGrading p realGrading) 0 (a + b + 4) z v := hj
    _ = C₀ * (H q.val * E q.val ^ A) *
        oneHighVariationWeight (pairGrading p realGrading) 0 (a + b + 4) z v := by ring
    _ ≤ C₀ * B *
        oneHighVariationWeight (pairGrading p realGrading) 0 (a + b + 4) z v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hweight q q.property) hC₀) hw

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
  exact polarInput_uniformBounds_of_raw
    (stateGrading S) (n01c_continuous_jointStateGrading S) (jointStateGrading_monotone S)
    (stateUPolarInput S) (annularOpen D)
    (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1)
    (stateNeighborhood S C base ε) i a b
    (coefficientPolarInput_regular hS hT hD C base ε i)
    (fun z hz => hz.2.le.trans hε)
    (fun A => by
      have h := materialHeight_E0_weight_bounded hT
        (by norm_num : (0 : ℝ) < 3 / 4) A
      exact ⟨h.choose, h.choose_spec.1, fun q hq => h.choose_spec.2 q.1 hq.1⟩)
    (stateU_qPolarMixedJets_oneHigh_bound hT hS hD (a + b))

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
