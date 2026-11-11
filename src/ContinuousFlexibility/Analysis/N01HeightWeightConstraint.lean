import ContinuousFlexibility.Analysis.N01HeightResponseBound
import ContinuousFlexibility.Analysis.N01ReturnMargins

/-!
# The actual radial-cell constraint detected by height directions

The positive small-divisor margin at frequency one bounds the actual
optical travel from below. Combining that lower bound with the mixed
height response gives a quantitative constraint at an actual containing
cell, ready to be applied to a compact radial test direction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.travel_nonneg
    (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    0 ≤ C.travel m := by
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have htravel : C.travel m = ∫ r in C.left m..C.right m, opticalSpeed D.w r :=
    hcontrol.2.2.2.2.2.2.2.1 m
  rw [htravel]
  exact intervalIntegral.integral_nonneg (hcontrol.1 m).2.1.le
    (fun _ _ => Real.sqrt_nonneg _)

/-- The radial margin gives a positive lower bound on travel at a
genuine containing reference cell. -/
theorem N01Properties.actualCell_travel_lower_bound
    (hN : N01Properties D T S C base loss ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ m,
      0 < C.travel m ∧ ∃ j : ℕ,
        Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
        1 ≤ radialE (D.cellIndex j) ^ R * C.travel m := by
  obtain ⟨R, hR, hmargins⟩ := n01Properties_returnMargins hN
  refine ⟨R, hR, fun m => ?_⟩
  obtain ⟨j, hcell, c, hc, hinv, hsmall⟩ := (hmargins m).2
  have hs : c ≤ |Real.sin (C.travel m)| := by
    simpa only [Nat.cast_one, one_mul, div_one] using hsmall 1 (by decide)
  have hcT : c ≤ C.travel m :=
    hs.trans ((Real.abs_sin_le_abs (C.travel m)).trans_eq
      (abs_of_nonneg (hN.travel_nonneg m)))
  have hE : 0 < radialE (D.cellIndex j) ^ R :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hcE : 1 ≤ radialE (D.cellIndex j) ^ R * c := by
    apply (div_le_iff₀ hc).mp
    simpa only [one_div] using hinv
  exact ⟨hc.trans_le hcT, j, hcell,
    hcE.trans (mul_le_mul_of_nonneg_left hcT hE.le)⟩

/-- All analytic information here is from the actual N01 flow and the
actual radial margin. The remaining test-direction norm is explicit. -/
theorem N01Properties.radialHeightDirection_weight_constraint
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B R : ℝ, 0 < B ∧ 0 < R ∧ ∀ m, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      ∀ η : HeightPair S, ∀ h : ℝ → ℝ,
        (∀ r, HasDerivAt h (D.w r) r) →
        (∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
          heightPairField S η =ᶠ[𝓝 (r, θ)] Radial.radialHeightField h) →
        1 ≤ radialE (D.cellIndex j) ^ R *
          (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            (2 * heightPairGrading S base η + heightPairGrading S loss η)) := by
  obtain ⟨B, hB, hresponse⟩ :=
    hN.opticalTravel_le_radialHeightDirection_weight hS hT
  obtain ⟨R, hR, htravel⟩ := hN.actualCell_travel_lower_bound
  refine ⟨B, R, hB, hR, fun m => ?_⟩
  obtain ⟨_, j, hj, hlower⟩ := htravel m
  refine ⟨j, hj, fun η h hhw hgerm => ?_⟩
  have hE : 0 ≤ radialE (D.cellIndex j) ^ R :=
    (Real.rpow_pos_of_pos (Real.exp_pos _) _).le
  exact hlower.trans
    (mul_le_mul_of_nonneg_left (hresponse η m h hhw hgerm) hE)

end ContinuousFlexibility.Statements
