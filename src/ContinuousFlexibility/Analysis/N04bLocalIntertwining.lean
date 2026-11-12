import ContinuousFlexibility.Analysis.N04bOperatorGerms
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Localizing an actual canonical operator identity

The canonical identity is assumed only for globally smooth test functions.
An arbitrary smooth physical test is converted into its actual local
canonical height. A compactly supported smooth representative preserves the
whole germ, and operator locality transfers both divergence evaluations.

Neither stored coefficient field is required to be differentiable. The
result concerns interior points of open chart domains.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- An actual intertwining identity on all global smooth canonical tests
determines the physical operator on every global smooth physical test.
The local canonical test is the genuine inverse-height pullback. -/
theorem n04b_physicalOperator_of_intertwining
    {U Ω : Set PolarPoint} {A B : SymmetricCoefficients}
    {F G : PolarPoint → PolarPoint} {h u : PolarPoint → ℝ}
    {x : PolarPoint} {V : ℝ}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hx : x ∈ U)
    (hFU : MapsTo F U Ω) (hGU : MapsTo G Ω U)
    (hGF : ∀ y ∈ U, G (F y) = y)
    (hF : ContinuousAt F x) (hG : ContDiffOn ℝ ∞ G Ω)
    (hh : ContDiffOn ℝ ∞ h U) (hpos : ∀ y ∈ U, 0 < h y)
    (hu : ContDiff ℝ ∞ u) (hJ : planeJacobian F x ≠ 0)
    (hact : ∀ W : PolarPoint → ℝ, ContDiff ℝ ∞ W →
      h x * divergenceOperator A (fun y => h y * W (F y)) x /
          |planeJacobian F x| =
        divergenceOperator B W (F x) + V * W (F x)) :
    divergenceOperator A u x =
      |planeJacobian F x| / h x *
        (divergenceOperator B (fun p => u (G p) / h (G p)) (F x) +
          V * (u x / h x)) := by
  let v : PolarPoint → ℝ := fun p => u (G p) / h (G p)
  have hv : ContDiffOn ℝ ∞ v Ω := by
    exact (hu.comp_contDiffOn hG).div (hh.comp hG hGU)
      (fun p hp => ne_of_gt (hpos (G p) (hGU hp)))
  obtain ⟨W, hW, _, hWv⟩ :=
    n04b_exists_contDiff_germ_extension hΩ (hFU hx) hv
  have hWvF : (fun y => W (F y)) =ᶠ[𝓝 x] (fun y => v (F y)) :=
    hWv.comp_tendsto hF
  have hpull : (fun y => h y * W (F y)) =ᶠ[𝓝 x] u := by
    filter_upwards [hWvF, hU.mem_nhds hx] with y hy hyU
    rw [hy]
    dsimp only [v]
    rw [hGF y hyU]
    field_simp [ne_of_gt (hpos y hyU)] <;> ring
  have hphysical :
      divergenceOperator A (fun y => h y * W (F y)) x =
        divergenceOperator A u x :=
    n04b_divergenceOperator_congr_germ hpull
  have hcanonical : divergenceOperator B W (F x) =
      divergenceOperator B v (F x) :=
    n04b_divergenceOperator_congr_germ hWv
  have hvalue : W (F x) = u x / h x := by
    simpa only [v, hGF x hx] using hWv.self_of_nhds
  have he := hact W hW
  rw [hphysical, hcanonical, hvalue] at he
  have he' := (div_eq_iff (abs_ne_zero.mpr hJ)).mp he
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (ne_of_gt (hpos x hx))).mpr
  simpa only [v, mul_comm] using he'

end ContinuousFlexibility.Analysis
