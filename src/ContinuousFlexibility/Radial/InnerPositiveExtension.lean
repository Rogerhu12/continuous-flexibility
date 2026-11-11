import ContinuousFlexibility.Radial.OscillatorCompactCore
import ContinuousFlexibility.Statements.Radial
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth positive coefficients for a retained radial interval

The reference weight is globally smooth and flat outside its annulus,
so its reciprocal is not globally smooth. A cutoff supported inside
the annulus extends the weight positively without changing its germ
at any point of a retained closed inner interval. A similar positive
radius removes the irrelevant singularity at zero. These extensions
allow the ordinary finite-interval ODE existence theorem to be applied
to the actual radial flux system.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem innerReference_weight_nonneg {D : ReferenceData} (hD : RadialProfileGeometry D) :
    ∀ r, 0 ≤ D.w r := by
  intro r
  by_cases hr : r ∈ radialCore D
  · exact (hD.2.2.2.2.1 r hr).le
  · have hout : r ≤ D.a ∨ D.b ≤ r := by
      by_cases hleft : r ≤ D.a
      · exact Or.inl hleft
      · exact Or.inr (le_of_not_gt (fun h => hr ⟨lt_of_not_ge hleft, h⟩))
    rw [hD.2.2.1.2 r hout]

/-- A single smooth cutoff is one on a neighbourhood of the retained
closed interval and has support strictly inside the ambient interval. -/
theorem exists_innerIntervalCutoff {A l h B : ℝ}
    (hAl : A < l) (hlh : l ≤ h) (hhB : h < B) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      Function.support χ ⊆ Ioo A B ∧
      ∀ x ∈ Icc l h, χ =ᶠ[𝓝 x] (fun _ => 1) := by
  let δ : ℝ := min (l - A) (B - h) / 3
  let m : ℝ := (l + h) / 2
  let d : ℝ := (h - l) / 2
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr hAl) (sub_pos.mpr hhB)) (by norm_num)
  have hd : 0 ≤ d := div_nonneg (sub_nonneg.mpr hlh) (by norm_num)
  have hδL : 3 * δ ≤ l - A := by
    dsimp only [δ]
    linarith only [min_le_left (l - A) (B - h)]
  have hδR : 3 * δ ≤ B - h := by
    dsimp only [δ]
    linarith only [min_le_right (l - A) (B - h)]
  let χ : ContDiffBump m := ⟨d + δ, d + 2 * δ, by linarith, by linarith⟩
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, fun _ => ⟨χ.nonneg, χ.le_one⟩, ?_, ?_⟩
  · rw [χ.support_eq, Real.ball_eq_Ioo]
    intro x hx
    change m - (d + 2 * δ) < x ∧ x < m + (d + 2 * δ) at hx
    dsimp only [m, d] at hx
    exact ⟨by linarith only [hx.1, hδL, hδ], by linarith only [hx.2, hδR, hδ]⟩
  · intro x hx
    have hball : x ∈ Metric.ball m χ.rIn := by
      rw [Real.ball_eq_Ioo]
      change m - (d + δ) < x ∧ x < m + (d + δ)
      dsimp only [m, d]
      exact ⟨by linarith only [hx.1, hδ], by linarith only [hx.2, hδ]⟩
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hball] with y hy
    simpa only [Pi.one_apply] using hy

def innerPositiveWeightExtension (w χ : ℝ → ℝ) (x : ℝ) : ℝ := w x + 1 - χ x

theorem innerPositiveWeightExtension_pos {A B : ℝ} {w χ : ℝ → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hpos : ∀ x ∈ Ioo A B, 0 < w x)
    (hχ : ∀ x, χ x ≤ 1) (hsupport : Function.support χ ⊆ Ioo A B) (x : ℝ) :
    0 < innerPositiveWeightExtension w χ x := by
  by_cases hlt : χ x < 1
  · dsimp only [innerPositiveWeightExtension]
    linarith only [hw x, hlt]
  · have heq : χ x = 1 := le_antisymm (hχ x) (le_of_not_gt hlt)
    have hmem : x ∈ Function.support χ := by rw [Function.mem_support, heq]; exact one_ne_zero
    have h := hpos x (hsupport hmem)
    dsimp only [innerPositiveWeightExtension]
    linarith only [heq, h]

theorem innerPositiveWeightExtension_contDiff {w χ : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (innerPositiveWeightExtension w χ) :=
  (hw.add contDiff_const).sub hχ

theorem innerPositiveWeightExtension_germ {w χ : ℝ → ℝ} {x : ℝ}
    (hχ : χ =ᶠ[𝓝 x] (fun _ => 1)) :
    innerPositiveWeightExtension w χ =ᶠ[𝓝 x] w := by
  filter_upwards [hχ] with y hy
  simp only [innerPositiveWeightExtension, hy, add_sub_cancel_right]

/-- The actual flat reference weight has a globally positive smooth
extension that agrees with it near every retained point. -/
theorem exists_innerPositiveWeight {A l h B : ℝ}
    (hAl : A < l) (hlh : l ≤ h) (hhB : h < B)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hwnonneg : ∀ x, 0 ≤ w x)
    (hwpos : ∀ x ∈ Ioo A B, 0 < w x) :
    ∃ wPos : ℝ → ℝ, ContDiff ℝ ∞ wPos ∧ (∀ x, 0 < wPos x) ∧
      ∀ x ∈ Icc l h, wPos =ᶠ[𝓝 x] w := by
  obtain ⟨χ, hχ, _, hχbounds, hs, hg⟩ := exists_innerIntervalCutoff hAl hlh hhB
  exact ⟨innerPositiveWeightExtension w χ, innerPositiveWeightExtension_contDiff hw hχ,
    innerPositiveWeightExtension_pos hwnonneg hwpos (fun x => (hχbounds x).2) hs,
    fun x hx => innerPositiveWeightExtension_germ (hg x hx)⟩

/-- A positive smooth substitute for the radius, identical to the radius
above `2c`. The transition is outside the retained physical interval. -/
def innerPositiveRadius (c x : ℝ) : ℝ :=
  c + (x - c) * smoothTransition ((x - c) / c)

theorem innerPositiveRadius_contDiff (c : ℝ) : ContDiff ℝ ∞ (innerPositiveRadius c) := by
  have harg : ContDiff ℝ ∞ (fun x : ℝ => (x - c) / c) := by
    simp only [div_eq_mul_inv]
    exact (contDiff_id.sub contDiff_const).mul contDiff_const
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (smoothTransition.contDiff.comp harg))

theorem innerPositiveRadius_pos {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 < innerPositiveRadius c x := by
  by_cases hx : x ≤ c
  · have hz := smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hc.le)
    simpa only [innerPositiveRadius, hz, mul_zero, add_zero] using hc
  · have hmul := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hx))
      (smoothTransition.nonneg ((x - c) / c))
    dsimp only [innerPositiveRadius]
    linarith only [hc, hmul]

theorem innerPositiveRadius_eq {c x : ℝ} (hc : 0 < c) (hx : 2 * c ≤ x) :
    innerPositiveRadius c x = x := by
  have harg : 1 ≤ (x - c) / c := (le_div_iff₀ hc).mpr (by linarith only [hx])
  rw [innerPositiveRadius, smoothTransition.one_of_one_le harg, mul_one]
  ring

theorem innerPositiveRadius_germ {c x : ℝ} (hc : 0 < c) (hx : 2 * c < x) :
    innerPositiveRadius c =ᶠ[𝓝 x] (fun y => y) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact innerPositiveRadius_eq hc hy.le

/-- Both coefficients of `u' = p v`, `v' = q u` are genuinely smooth
on the whole line, while their retained germs are exactly `1/w` and
`j² w'/r`. Consequently the finite ODE does not change the radial operator. -/
theorem exists_innerRadialFluxCoefficients {A l h B : ℝ}
    (hA : 0 < A) (hAl : A < l) (hlh : l ≤ h) (hhB : h < B)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hwnonneg : ∀ x, 0 ≤ w x)
    (hwpos : ∀ x ∈ Ioo A B, 0 < w x) (j : ℝ) :
    ∃ p q : ℝ → ℝ, ContDiff ℝ ∞ p ∧ ContDiff ℝ ∞ q ∧
      ∀ x ∈ Icc l h,
        p =ᶠ[𝓝 x] (fun y => (w y)⁻¹) ∧
        q =ᶠ[𝓝 x] (fun y => j ^ 2 * deriv w y / y) := by
  obtain ⟨wPos, hwPos, hpos, hg⟩ := exists_innerPositiveWeight hAl hlh hhB hw hwnonneg hwpos
  let c : ℝ := A / 3
  have hc : 0 < c := div_pos hA (by norm_num)
  have hp : ContDiff ℝ ∞ (fun x => (wPos x)⁻¹) := hwPos.inv (fun x => (hpos x).ne')
  have hq : ContDiff ℝ ∞ (fun x => j ^ 2 * deriv wPos x / innerPositiveRadius c x) :=
    (contDiff_const.mul (contDiff_infty_iff_deriv.mp hwPos).2).div
      (innerPositiveRadius_contDiff c) (fun x => (innerPositiveRadius_pos hc x).ne')
  refine ⟨_, _, hp, hq, ?_⟩
  intro x hx
  have hgx := hg x hx
  have hR := innerPositiveRadius_germ hc (x := x)
    (by dsimp only [c]; linarith only [hA, hAl, hx.1])
  constructor
  · filter_upwards [hgx] with y hy
    rw [hy]
  · filter_upwards [hgx.deriv, hR] with y hy hRy
    rw [hy, hRy]

end ContinuousFlexibility.Radial
