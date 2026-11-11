import ContinuousFlexibility.Radial.MatchedInnerLocalizedWeights
import ContinuousFlexibility.Radial.InnerMorseInnerWeightCosts

/-!
# Removing the fixed loss on the same finite physical chain

The reciprocal of the original coefficient loss is bounded by its
largest actual cell value. Composing that multiplier restores the
unlocalized weight on the same operator. The scalar coordinate remains
one throughout, so no replacement inverse is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements

/-- The reciprocal coefficient loss has a finite bound determined by
the transition index, including its extension by one off the chain. -/
theorem matchedInner_loss_inverse_bound {D : ReferenceData} (N K : ℕ)
    (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (x : ℝ) :
    |(innerMorseInnerLoss N K G ℓ x)⁻¹| ≤
      exp (ℓ * (radialQ (N + K) - radialQ N)) := by
  have hR : 1 ≤ exp (ℓ * (radialQ (N + K) - radialQ N)) :=
    one_le_exp_iff.mpr (mul_nonneg hℓ
      (sub_nonneg.mpr (radialQ_monotone (Nat.le_add_right N K))))
  change |(innerPiecewiseWeight (innerChainWeightPiece G)
    (fun p _ => innerCoefficientLoss N ℓ (innerMorseInnerPieceIndex N K p)) x)⁻¹| ≤ _
  apply innerPiecewiseWeight_inv_bound _ (innerChainWeightPieces_disjoint G) _ hR
  intro p y hy
  rw [innerCoefficientLoss_eq_exp, ← exp_neg, neg_neg, abs_of_pos (exp_pos _)]
  exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (sub_le_sub_right (radialQ_monotone (innerMorseInnerPieceIndex_bounds N K p).2) _) hℓ)

section SupportedLoss

variable {α : Type*} [MeasurableSpace α] [Nonempty α]
  (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (bordered : Bool)
  (loss W V : α → ℝ) (hloss : Measurable loss) (hW : Measurable W) (hV : Measurable V)
  (hpos : ∀ x, 0 < loss x) (hlossBound : ∀ x, |loss x| ≤ 1)
  (BW BV R : ℝ) (hWBound : ∀ x, |W x| ≤ BW) (hVBound : ∀ x, |V x| ≤ BV)
  (hR : 1 ≤ R) (hinv : ∀ x, |(loss x)⁻¹| ≤ R)

local notation "MW" => innerSupportedWeightMultiplier μ s hs bordered W hW BW hWBound
local notation "MV" => innerSupportedWeightMultiplier μ s hs bordered V hV BV hVBound
local notation "ML" => innerSupportedWeightMultiplier μ s hs bordered
  (fun x => loss x * W x) (hloss.mul hW) BW
  (innerWeight_mul_bound_one loss W hlossBound BW hWBound)
local notation "MI" => innerSupportedWeightMultiplier μ s hs bordered
  (fun x => (loss x)⁻¹) hloss.inv R hinv

/-- Undoing the loss is exact multiplication on the original supported
space, independently of the auxiliary multiplier bounds. -/
theorem matchedInner_remove_loss_identity :
    MI ∘L ML = MW := by
  have hBW : 0 ≤ BW := by
    obtain ⟨x⟩ := ‹Nonempty α›
    exact (abs_nonneg (W x)).trans (hWBound x)
  have hR₀ : 0 ≤ R := zero_le_one.trans hR
  rw [← innerSupportedWeightMultiplier_product μ s hs bordered
    (fun x => (loss x)⁻¹) (fun x => loss x * W x) hloss.inv (hloss.mul hW)
    R BW hR₀ hBW hinv (innerWeight_mul_bound_one loss W hlossBound BW hWBound)]
  apply innerSupportedWeightMultiplier_congr
  intro x
  rw [← mul_assoc, inv_mul_cancel₀ (hpos x).ne', one_mul]

/-- The same operator has its coarse bound after the reciprocal loss
is restored; this is a composition estimate on the original space. -/
theorem matchedInner_remove_loss_norm_le (T : ↥(innerSupportedAdmissibleSource μ s bordered) →L[ℝ]
    ↥(innerSupportedAdmissibleSource μ s bordered)) :
    ‖MW ∘L T ∘L MV‖ ≤ R * ‖ML ∘L T ∘L MV‖ := by
  have hfactor : MW ∘L T ∘L MV = MI ∘L (ML ∘L T ∘L MV) := by
    calc
      _ = (MI ∘L ML) ∘L T ∘L MV := by
        rw [matchedInner_remove_loss_identity μ s hs bordered loss W hloss hW
          hpos hlossBound BW R hWBound hR hinv]
      _ = _ := by simp only [ContinuousLinearMap.comp_assoc]
  rw [hfactor]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_innerSupportedWeightMultiplier_le μ s hs bordered
        (fun x => (loss x)⁻¹) hloss.inv R hR hinv) (norm_nonneg _))

end SupportedLoss

/-- Restoring the fixed loss costs only the transition-cell power.
The Poisson correction is absorbed in a constant chosen before the mode. -/
theorem matchedInner_coarse_fixed37_cost {N n : ℕ} {KD c : ℝ}
    (hc : 0 ≤ c) :
    exp (37 * (radialQ n - radialQ N)) *
        (KD * radialE N ^ (37 : ℝ) + c) ≤
      (KD + c) * radialE n ^ (37 : ℝ) := by
  have hcancel :
      exp (37 * (radialQ n - radialQ N)) * radialE N ^ (37 : ℝ) =
        radialE n ^ (37 : ℝ) := by
    simp only [radialE, ← exp_mul, ← exp_add]
    congr 1
    ring
  have hR : exp (37 * (radialQ n - radialQ N)) ≤ radialE n ^ (37 : ℝ) := by
    rw [radialE, ← exp_mul]
    apply exp_le_exp.mpr
    nlinarith only [radialQ_nonneg N]
  calc
    _ = KD * radialE n ^ (37 : ℝ) +
        c * exp (37 * (radialQ n - radialQ N)) := by
      rw [mul_add]
      rw [show exp (37 * (radialQ n - radialQ N)) *
          (KD * radialE N ^ (37 : ℝ)) =
        KD * (exp (37 * (radialQ n - radialQ N)) * radialE N ^ (37 : ℝ)) by ring,
        hcancel]
      ring
    _ ≤ KD * radialE n ^ (37 : ℝ) + c * radialE n ^ (37 : ℝ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hR hc)
    _ = _ := by ring

end ContinuousFlexibility.Radial
