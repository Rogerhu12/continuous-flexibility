import ContinuousFlexibility.Analysis.N04PositiveGeometryLabelSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledForwardLabelPrefix

/-!
# A common sampled prefix for the forward label and its slope

The low base is fixed before the parameter prefix. Reindexing each
angular horizon aligns both the high seminorm and the denominator of
the normalized power. Only positive words of the angular lift are used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

local instance n04RootForwardLabelSampleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PositiveGeometry_rootForwardLabel_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε) (hεW : ε ≤ W.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ Jα : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y : (StateDirections W.S × ℝ) × ℝ =>
          (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side)) y.2),
      ∀ Jb : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y : (StateDirections W.S × ℝ) × ℝ =>
          deriv ((n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side))) y.2),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      let P := fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
        pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R
      let M := A * W.U.E0 (W.U.sample (X.cell i)) ^ A
      let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
      let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
      N04BoundaryPositiveWordBounds Jα K s 1 z θ P M H t shift ∧
        N04BoundaryWordBounds Jb K s 1 z θ P M H t shift := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  apply n04PositiveGeometry_labelPair_sample_prefix
    (pairGrading (sectorGrading W.S) realGrading) (sectorPairGrading_monotone W.S)
    (sectorNeighborhood W.S base ε ε)
    (fun side m y => (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m side) y.2)
    (fun i side m => (X.src i side).val = some m)
    (fun m => W.T.H (W.T.sample m) ^ (3 / 4 : ℝ))
    (fun i => W.U.E0 (W.U.sample (X.cell i)))
    (fun i => W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ))
    (fun i => (W.floor _).trans (le_enlargedMaterialData_E0 W.T _))
    (fun i => Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _) base
    (fun side m θ => n04PositiveGeometry_rootForwardDefect_angularDirections
      W.hT W.hS hN side m 0 θ)
    (n04PositiveGeometry_rootForwardDefect_fixedBase_prefix_of_flow W.hT W.hS hN hflow)
    (n04PositiveGeometry_rootForwardDerivative_fixedBase_prefix_of_flow W.hT W.hS hN hflow)
  intro A hA
  obtain ⟨B, hB, hsample⟩ := n04PositiveGeometry_positiveSource_circle_parameter_weight
    W X (3 / 4 : ℝ) (A := 0) (C := A) (by norm_num) (zero_le_one.trans hA)
  refine ⟨B, hB, ?_⟩
  intro i side m hm k
  simpa only [Real.rpow_zero, mul_one] using hsample i side m hm k

end ContinuousFlexibility.Analysis
