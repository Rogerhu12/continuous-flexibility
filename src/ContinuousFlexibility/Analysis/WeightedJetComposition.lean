import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# A scale-invariant composition estimate for finite jets

The small powers in a Taylor remainder cancel the large powers in a
singular coordinate map. Rescaling the intermediate space reduces this
statement to mathlib's ordinary composition estimate. The coordinate map
only needs to be smooth on an open set containing the evaluation point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Weighted outer and inner jets give a composition bound independent of
the positive scale `ρ`. -/
theorem norm_iteratedFDeriv_comp_le_weighted
    {f : E → F} {g : F → G} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiff ℝ ∞ g)
    {x : E} (hx : x ∈ U) {ρ C D : ℝ} (hρ : 0 < ρ) (n : ℕ)
    (houter : ∀ i : ℕ, i ≤ n →
      ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C * ρ ^ (n - i))
    (hinner : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i f x‖ ≤ ρ * (D / ρ) ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (n ! : ℝ) * C * D ^ n := by
  let f₁ : E → F := fun y => ρ⁻¹ • f y
  let g₁ : F → G := fun y => g (ρ • y)
  have hf₁ : ContDiffOn ℝ ∞ f₁ U := hf.const_smul _
  have hg₁ : ContDiff ℝ ∞ g₁ := hg.comp (contDiff_id.const_smul ρ)
  have hfAt : ContDiffAt ℝ ∞ f x := (hf x hx).contDiffAt (hU.mem_nhds hx)
  have hcancel : ρ • f₁ x = f x := by
    dsimp only [f₁]
    rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  have houter₁ : ∀ i : ℕ, i ≤ n →
      ‖iteratedFDerivWithin ℝ i g₁ univ (f₁ x)‖ ≤ C * ρ ^ n := by
    intro i hi
    rw [iteratedFDerivWithin_univ]
    have hiG : ContDiff ℝ i g := hg.of_le (by simp)
    have hscale := congrFun (iteratedFDeriv_comp_const_smul ρ hiG) (f₁ x)
    rw [hscale, hcancel, norm_smul, Real.norm_of_nonneg (pow_nonneg hρ.le i)]
    calc
      ρ ^ i * ‖iteratedFDeriv ℝ i g (f x)‖ ≤ ρ ^ i * (C * ρ ^ (n - i)) :=
        mul_le_mul_of_nonneg_left (houter i hi) (pow_nonneg hρ.le i)
      _ = C * (ρ ^ i * ρ ^ (n - i)) := by ring
      _ = C * ρ ^ n := by rw [← pow_add, show i + (n - i) = n by omega]
  have hinner₁ : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i f₁ U x‖ ≤ (D / ρ) ^ i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hU hx]
    have hscale : iteratedFDeriv ℝ i f₁ x = ρ⁻¹ • iteratedFDeriv ℝ i f x :=
      iteratedFDeriv_const_smul_apply' (hfAt.of_le (by simp))
    rw [hscale, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
    calc
      ρ⁻¹ * ‖iteratedFDeriv ℝ i f x‖ ≤ ρ⁻¹ * (ρ * (D / ρ) ^ i) :=
        mul_le_mul_of_nonneg_left (hinner i hi hin) (inv_nonneg.mpr hρ.le)
      _ = (D / ρ) ^ i := by rw [← mul_assoc, inv_mul_cancel₀ hρ.ne', one_mul]
  have hcomp := norm_iteratedFDerivWithin_comp_le
    hg₁.contDiffOn hf₁ (n := n) (by simp) uniqueDiffOn_univ hU.uniqueDiffOn
    (fun _ _ => mem_univ _) hx houter₁ hinner₁
  have heq : g₁ ∘ f₁ = g ∘ f := by
    funext y
    dsimp only [Function.comp_apply, g₁, f₁]
    rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  rw [heq, iteratedFDerivWithin_of_isOpen n hU hx] at hcomp
  have hconstant : (n ! : ℝ) * (C * ρ ^ n) * (D / ρ) ^ n =
      (n ! : ℝ) * C * D ^ n := by
    rw [div_pow]
    field_simp [hρ.ne']
    <;> ring
  exact hcomp.trans_eq hconstant

end ContinuousFlexibility.Analysis
