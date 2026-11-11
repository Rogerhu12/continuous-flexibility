import ContinuousFlexibility.Radial.InnerRadialActualAssembly
import ContinuousFlexibility.Radial.InnerLiouvillePhysicalRepresentatives
import ContinuousFlexibility.Radial.InnerBorderWeights

/-!
# Exact action of a constant weight on actual model columns

The physical field of each original model column is supported on its
own piece. A multiplier equal to one there preserves that full column,
including its scalar coordinate. This identifies the central column
inside either sign of the actual Morse chain weight.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

theorem innerBorderFieldMap_eq_of_weight_one_on_support
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (W : α → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ x, |W x| ≤ CW)
    (F : InnerBorderL2 μ) (s : Set α)
    (hF : ∀ᵐ x ∂μ, x ∉ s → F.fst x = 0)
    (hOne : EqOn W (fun _ => 1) s) :
    innerBorderFieldMap μ (innerWeightMultiplier μ W hW CW hWC) F = F := by
  have hfield : innerWeightMultiplier μ W hW CW hWC F.fst = F.fst := by
    apply Lp.ext
    filter_upwards [innerWeightMultiplier_ae μ W hW CW hWC F.fst, hF] with x hmul hs
    rw [hmul]
    by_cases hx : x ∈ s
    · rw [hOne hx, one_mul]
    · rw [hs hx, mul_zero]
  rw [innerBorderFieldMap_apply, hfield]
  exact WithLp.toLp_ofLp 2 F

namespace InnerRadialModelChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central piece : Fin (n + 1)} {column : RadialModeL2 D}
  (M : InnerRadialModelChart D G bordered j central column piece)

theorem matchedColumn_support_ae (i : Fin 2) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo (G.left piece) (G.right piece) →
      (M.column i).fst r = 0 := by
  let F : RadialModeL2 D := innerLiouvilleFieldLift D M.buffer_hypotheses.1.le
    M.height_pos M.radius_smooth M.scale_smooth M.chart_pos M.in_core M.weight_identity
    M.U M.U_nonneg M.log_deriv_bound (M.localized.column i).field
  let c : ℝ := sqrt M.height * M.scale (bufferCut M.buffer i)
  have he : (M.column i).fst = c • F := by
    simp only [InnerRadialModelChart.column, innerModelPhysicalPoissonColumn,
      WithLp.toLp_fst, innerLiouvilleUnitPoissonPair_apply]
  have hs := innerLiouvilleFieldLift_support_ae D M.buffer_hypotheses.1.le M.height_pos
    M.radius_smooth M.scale_smooth M.chart_pos M.in_core M.weight_identity
    M.U M.U_nonneg M.log_deriv_bound (M.localized.column i).field
  rw [M.left_eq, M.right_eq]
  filter_upwards [Lp.coeFn_smul c F, hs] with r hsm hzero
  intro hr
  rw [he, hsm, Pi.smul_apply, smul_eq_mul, hzero hr, mul_zero]

theorem matchedColumn_weight_one
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (hOne : EqOn W (fun _ => 1) (Ioo (G.left piece) (G.right piece)))
    (i : Fin 2) :
    innerBorderFieldMap (radialHilbertMeasure D)
      (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) (M.column i) =
        M.column i :=
  innerBorderFieldMap_eq_of_weight_one_on_support (radialHilbertMeasure D)
    W hW CW hWC (M.column i) (Ioo (G.left piece) (G.right piece))
    (M.matchedColumn_support_ae i) hOne

end InnerRadialModelChart

end ContinuousFlexibility.Radial
