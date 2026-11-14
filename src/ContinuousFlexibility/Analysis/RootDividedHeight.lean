module

public import ContinuousFlexibility.Analysis.RootChartExtension
public import ContinuousFlexibility.Analysis.RootCoefficientFactorization

/-!
# The root height after the genuine radial factor is divided out

The physical discriminant is δ x times the true smooth divided
discriminant, whereas the canonical radial coordinate is x times the
smooth root power. Cancelling this same x gives a formula smooth at the
root. The factor δ is retained explicitly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootDividedHeight (δ : ℝ) (V : PolarPoint → ℝ)
    (G : ℝ × ℝ × ℝ → ℝ) (p : PolarPoint) : ℝ :=
  (extendedRootRadialFactor G p / (δ * V p)) ^ (1 / 4 : ℝ)

theorem rootDividedHeight_eq_powers
    {δ : ℝ} {V : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ} {p : PolarPoint}
    (hδ : 0 < δ) (hV : 0 < V p) (hχ : 0 < extendedRootOddCoefficient G p) :
    rootDividedHeight δ V G p =
      (((3 / 2 : ℝ) * extendedRootOddCoefficient G p) ^ (1 / 6 : ℝ)) *
        (δ * V p) ^ (-(1 / 4 : ℝ)) := by
  have ha : 0 < (3 / 2 : ℝ) * extendedRootOddCoefficient G p := mul_pos (by norm_num) hχ
  have hb : 0 < δ * V p := mul_pos hδ hV
  rw [rootDividedHeight, extendedRootRadialFactor,
    Real.div_rpow (Real.rpow_nonneg ha.le _) hb.le,
    ← Real.rpow_mul ha.le,
    show (2 / 3 : ℝ) * (1 / 4 : ℝ) = 1 / 6 by norm_num,
    div_eq_mul_inv, Real.rpow_neg hb.le]

theorem contDiffAt_rootDividedHeight
    {δ : ℝ} {V : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ} {p : PolarPoint}
    (hδ : 0 < δ) (hV : ContDiffAt ℝ ∞ V p)
    (hχ : ContDiffAt ℝ ∞ (extendedRootOddCoefficient G) p)
    (hVp : 0 < V p) (hχp : 0 < extendedRootOddCoefficient G p) :
    ContDiffAt ℝ ∞ (rootDividedHeight δ V G) p ∧ 0 < rootDividedHeight δ V G p := by
  have ha : 0 < (3 / 2 : ℝ) * extendedRootOddCoefficient G p := mul_pos (by norm_num) hχp
  have hb : 0 < δ * V p := mul_pos hδ hVp
  have hF : ContDiffAt ℝ ∞ (extendedRootRadialFactor G) p :=
    (contDiffAt_const.mul hχ).rpow_const_of_ne ha.ne'
  have hFp : 0 < extendedRootRadialFactor G p := Real.rpow_pos_of_pos ha _
  have hquot : ContDiffAt ℝ ∞ (fun q => extendedRootRadialFactor G q / (δ * V q)) p :=
    hF.fun_div (contDiffAt_const.mul hV) hb.ne'
  exact ⟨hquot.rpow_const_of_ne (div_pos hFp hb).ne',
    Real.rpow_pos_of_pos (div_pos hFp hb) _⟩

/-- The actual determinant ratio loses exactly its common radial x;
there is no inverse power of x left in this formula. -/
theorem rootDividedHeight_eq_of_radial_factor
    {δ x v : ℝ} {V : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ} {θ : ℝ}
    (hδ : 0 < δ) (hx : 0 < x) (hV : 0 < V (x, θ))
    (hv : v = (δ * x) * V (x, θ)) :
    ((extendedRootEvenOddChart G (x, θ)).1 / v) ^ (1 / 4 : ℝ) =
      rootDividedHeight δ V G (x, θ) := by
  rw [hv]
  congr 1
  change x * extendedRootRadialFactor G (x, θ) / ((δ * x) * V (x, θ)) =
    extendedRootRadialFactor G (x, θ) / (δ * V (x, θ))
  field_simp [hδ.ne', hx.ne', hV.ne']
  <;> ring

end ContinuousFlexibility.Analysis
