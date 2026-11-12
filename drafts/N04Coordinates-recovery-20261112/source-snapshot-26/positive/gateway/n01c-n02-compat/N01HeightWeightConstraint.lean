import ContinuousFlexibility.Analysis.N01HeightResponseBound
import ContinuousFlexibility.Analysis.N01TravelLowerBound

/-!
# The actual radial-cell constraint detected by height directions

The positive small-divisor margin at frequency one bounds the actual
optical travel from below. Combining that lower bound with the mixed
height response gives a quantitative constraint at an actual containing
cell, ready to be applied to a compact radial test direction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01HeightWeightConstraintStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- All analytic information here is from the actual N01 flow and the
actual radial margin. The remaining test-direction norm is explicit. -/
theorem N01Properties.radialHeightDirection_weight_constraint
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ parameterLoss : ℕ, ∃ B R : ℝ, 0 < B ∧ 0 < R ∧ ∀ m, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      ∀ η : HeightPair S, ∀ h : ℝ → ℝ,
        (∀ r, HasDerivAt h (D.w r) r) →
        (∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
          heightPairField S η =ᶠ[𝓝 (r, θ)] Radial.radialHeightField h) →
        1 ≤ radialE (D.cellIndex j) ^ R *
          (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            (2 * heightPairGrading S base η + heightPairGrading S (loss + parameterLoss) η)) := by
  obtain ⟨parameterLoss, B, hB, hresponse⟩ :=
    hN.opticalTravel_le_radialHeightDirection_weight hS hT
  obtain ⟨R, hR, htravel⟩ := hN.actualCell_travel_lower_bound
  refine ⟨parameterLoss, B, R, hB, hR, fun m => ?_⟩
  obtain ⟨_, j, hj, hlower⟩ := htravel m
  refine ⟨j, hj, fun η h hhw hgerm => ?_⟩
  have hE : 0 ≤ radialE (D.cellIndex j) ^ R :=
    (Real.rpow_pos_of_pos (Real.exp_pos _) _).le
  exact hlower.trans
    (mul_le_mul_of_nonneg_left (hresponse η m h hhw hgerm) hE)

end ContinuousFlexibility.Statements
