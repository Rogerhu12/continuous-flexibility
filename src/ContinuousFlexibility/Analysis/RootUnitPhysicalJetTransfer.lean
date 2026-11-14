module

public import ContinuousFlexibility.Analysis.RootPhysicalJetTransfer

/-!
# Physical transfer after the root normalization has been removed

Only the actual inward orientation remains. Its inverse linear map has
norm one, so the existing ordinary-jet transfer costs the universal
factor two, and the Jacobian lower bound has no scale divisor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem norm_rootProfileInverseLinear_unit {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ‖rootProfileInverseLinear σ‖ = 1 := by
  have hσinv : |σ⁻¹| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have happ (v : PolarPoint) : rootProfileInverseLinear σ v = (σ⁻¹ * v.1, v.2) := by
    simp only [rootProfileInverseLinear, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul]
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
    rw [happ]
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_mul, hσinv, one_mul, le_refl]
  · have h := (rootProfileInverseLinear σ).le_opNorm ((0, 1) : PolarPoint)
    rw [happ] at h
    simpa [Prod.norm_def, max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)] using h

theorem rootAffineJetEnvelope_unit {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (B : ℕ → ℝ) : rootAffineJetEnvelope σ B = fun n => 2 * B n := by
  funext n
  simp only [rootAffineJetEnvelope, norm_rootProfileInverseLinear_unit hσ, one_pow]
  norm_num

/-- This consumes the actual unit-coordinate ordinary jet identities.
All state orders and the original chart and height remain unchanged. -/
theorem rootPhysicalFields_of_unit_jet_model
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {B : ℕ → ℝ} {z : E}
    (r σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hB : ∀ n, 0 ≤ B n)
    {F M : PolarPoint → PolarPoint} {H h : PolarPoint → ℝ} {q : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F (rootProfileShift r σ q))
    (hH : ContDiffAt ℝ ∞ H (rootProfileShift r σ q))
    (hHpos : 0 < H (rootProfileShift r σ q))
    (hmodel : RootPhysicalFieldJetBound p loss B z M h q)
    (hFjet : ∀ n : ℕ,
      iteratedFDeriv ℝ n (fun y => F (rootProfileShift r σ y)) q =
        iteratedFDeriv ℝ n M q)
    (hHjet : ∀ a : ℝ, ∀ n : ℕ,
      iteratedFDeriv ℝ n (fun y => H (rootProfileShift r σ y) ^ a) q =
        iteratedFDeriv ℝ n (fun y => h y ^ a) q)
    {J₀ : ℝ} (hJ : J₀ ≤ planeJacobian M q) :
    RootPhysicalFieldJetBound p loss (fun n => 2 * B n) z
      F H (rootProfileShift r σ q) ∧
      J₀ ≤ |planeJacobian F (rootProfileShift r σ q)| := by
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hb := rootPhysicalFields_of_scaled_jet_model r σ hσne hB
    hF hH hHpos hmodel hFjet hHjet hJ
  simpa only [rootAffineJetEnvelope_unit hσ B, hσabs, div_one] using hb

end ContinuousFlexibility.Analysis
