import ContinuousFlexibility.Analysis.NegativeCanonicalFaithfulness
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The actual negative height is a fourth root of the determinant ratio

The forward coordinate determinant and the faithful stored coefficients
identify the height on each actual open negative half. This is a value
identity for the already chosen chart and height; it assumes no height
derivative estimate. Both endpoints use the same Boolean statement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

/-- Scalar determinant algebra, keeping the positive fourth root. -/
theorem positive_height_eq_fourthRoot_of_determinant
    {h ξ a b c : ℝ} (hh : 0 < h) (hξ : 0 < ξ)
    (hdet : a * c - b ^ 2 = -ξ / h ^ 4) :
    0 < b ^ 2 - a * c ∧ h = (ξ / (b ^ 2 - a * c)) ^ (1 / 4 : ℝ) := by
  have hdisc : b ^ 2 - a * c = ξ / h ^ 4 := by
    rw [neg_div] at hdet
    linarith only [hdet]
  refine ⟨by rw [hdisc]; exact div_pos hξ (pow_pos hh 4), ?_⟩
  have hratio : ξ / (b ^ 2 - a * c) = h ^ 4 := by
    rw [hdisc]
    field_simp [hh.ne', hξ.ne']
  rw [hratio, ← Real.rpow_natCast h 4, ← Real.rpow_mul hh.le]
  norm_num

/-- At every point in a genuine paired negative domain, the actual height
is determined by the actual chart and corrected coefficient field. -/
theorem negativeCutPair_height_eq_fourthRoot
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    ∀ p ∈ physicalPieceOpen S K z i,
      0 < (L.coefficients z).b p ^ 2 -
        (L.coefficients z).a p * (L.coefficients z).c p ∧
      K.height z i p = ((K.chart z i p).1 /
        ((L.coefficients z).b p ^ 2 -
          (L.coefficients z).a p * (L.coefficients z).c p)) ^ (1 / 4 : ℝ) := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  dsimp only
  intro p hp
  obtain ⟨_, _, _, _, _, _, hleftL, hleftR, _, _⟩ := hB.1.1 m
  have hleft : K.left i = 0 := by
    cases side with
    | false => exact hleftL
    | true => exact hleftR
  have hξ : 0 < (K.chart z i p).1 := by
    have hmem := (hA.charts z hz hs i).1 hp
    simpa only [hleft] using hmem.1.1
  have hh : 0 < K.height z i p :=
    ((hA.boundary z hz hs i).2.2.2.2.1 p (subset_closure hp)).2.2.2
  have hcoeff := negativeCutPair_coefficients_eq_closed
    hS hT hN01 hN03 hA hB hz hs m side p hp
  have hdet : (L.coefficients z).a p * (L.coefficients z).c p -
      (L.coefficients z).b p ^ 2 = -(K.chart z i p).1 / K.height z i p ^ 4 := by
    rw [hcoeff.1, hcoeff.2.1, hcoeff.2.2]
    exact negativeCanonicalClosedCoefficients_determinant hA hz hs i (subset_closure hp)
  exact positive_height_eq_fourthRoot_of_determinant hh hξ hdet

end ContinuousFlexibility.Analysis
