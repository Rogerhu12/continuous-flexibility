module

public import ContinuousFlexibility.Radial.CentralRadius
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The central radius as an actual radial coordinate

The constructed radius covers `(0,∞)`. Its inverse is smooth there,
so the pulled-back positive profile defines a genuine smooth function of
the radius. The endpoint limits below are qualitative limits, not the
finite-order asymptotic expansions required for later cutting estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem strictMono_gaussianLaplaceMoment {β : ℝ} (hβ : 0 < β) :
    StrictMono (gaussianLaplaceMoment β) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [deriv_gaussianLaplaceMoment hβ x]
  exact mul_pos (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    (gaussianLaplaceMoment_pos (by linarith : 0 < β + 1) x)

theorem strictMono_centralRadiusPsi : StrictMono centralRadiusPsi :=
  strictMono_of_deriv_pos deriv_centralRadiusPsi_pos

/-- A simple upper bound already settles the left endpoint limit. -/
theorem centralRadius_le_exp_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    centralRadius x ≤ exp (centralRadiusA * x) * gaussianLaplaceMoment centralRadiusAlpha 0 := by
  have hα : 0 < centralRadiusAlpha := by linarith [centralRadiusAlpha_gt_half]
  have he : exp (-x ^ 2 / 2) ≤ 1 := by
    apply exp_le_one_iff.mpr
    nlinarith [sq_nonneg x]
  have hp : centralRadiusPsi x ≤ gaussianLaplaceMoment centralRadiusAlpha 0 := by
    change exp (-x ^ 2 / 2) * gaussianLaplaceMoment centralRadiusAlpha x ≤ _
    calc
      _ ≤ gaussianLaplaceMoment centralRadiusAlpha x := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right he
          (gaussianLaplaceMoment_pos hα x).le
      _ ≤ _ := (strictMono_gaussianLaplaceMoment hα).monotone hx
  exact mul_le_mul_of_nonneg_left hp (exp_pos _).le

theorem tendsto_centralRadius_atBot : Tendsto centralRadius atBot (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => exp (centralRadiusA * x)) atBot (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot centralRadiusA_pos)
  apply squeeze_zero' (Eventually.of_forall (fun x => (centralRadius_pos x).le))
    ((eventually_le_atBot (0 : ℝ)).mono (fun _ hx => centralRadius_le_exp_of_nonpos hx))
  simpa only [zero_mul] using he.mul_const (gaussianLaplaceMoment centralRadiusAlpha 0)

theorem tendsto_centralRadius_atTop : Tendsto centralRadius atTop atTop := by
  have he : Tendsto (fun x : ℝ => exp (centralRadiusA * x)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop centralRadiusA_pos)
  apply tendsto_atTop_mono' atTop _ (he.atTop_mul_const (centralRadiusPsi_pos 0))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact mul_le_mul_of_nonneg_left (strictMono_centralRadiusPsi.monotone hx) (exp_pos _).le

theorem range_centralRadius : Set.range centralRadius = Ioi 0 := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    exact centralRadius_pos x
  · intro hr
    obtain ⟨x, hx⟩ := (tendsto_centralRadius_atBot.eventually (Iio_mem_nhds hr)).exists
    obtain ⟨y, hy⟩ :=
      (tendsto_centralRadius_atTop.eventually (eventually_ge_atTop r)).exists
    exact mem_range_of_exists_le_of_exists_ge contDiff_centralRadius.continuous
      ⟨x, hx.le⟩ ⟨y, hy⟩

/-- The inverse is only used on positive radii, the proved image of `R`. -/
def centralModelCoordinate : ℝ → ℝ := Function.invFun centralRadius

theorem centralModelCoordinate_radius (x : ℝ) :
    centralModelCoordinate (centralRadius x) = x :=
  Function.leftInverse_invFun strictMono_centralRadius.injective x

theorem centralRadius_modelCoordinate {r : ℝ} (hr : 0 < r) :
    centralRadius (centralModelCoordinate r) = r := by
  apply Function.invFun_eq
  rw [← Set.mem_range, range_centralRadius]
  exact hr

theorem hasStrictDerivAt_centralModelCoordinate (x : ℝ) :
    HasStrictDerivAt centralModelCoordinate (deriv centralRadius x)⁻¹ (centralRadius x) :=
  (contDiff_centralRadius.hasStrictDerivAt (x := x) (by simp)).to_local_left_inverse
    (deriv_centralRadius_pos x).ne' (Eventually.of_forall centralModelCoordinate_radius)

/-- Actual inverse-function regularity, not merely an algebraic inverse. -/
theorem contDiffAt_centralModelCoordinate (x : ℝ) :
    ContDiffAt ℝ ∞ centralModelCoordinate (centralRadius x) := by
  have h0 := (deriv_centralRadius_pos x).ne'
  let h := (contDiff_centralRadius.hasStrictDerivAt (x := x) (by simp)).hasStrictFDerivAt_equiv h0
  let e := h.toOpenPartialHomeomorph centralRadius
  have he : e.symm (centralRadius x) = x := h.localInverse_apply_image
  have hd : HasDerivAt e (deriv centralRadius x) (e.symm (centralRadius x)) := by
    rw [he]
    exact (contDiff_centralRadius.differentiable (by simp) x).hasDerivAt
  have hc : ContDiffAt ℝ ∞ (e : ℝ → ℝ) (e.symm (centralRadius x)) := by
    rw [he]
    exact contDiff_centralRadius.contDiffAt
  have hi := e.contDiffAt_symm_deriv h0 h.image_mem_toOpenPartialHomeomorph_target hd hc
  have heq : centralModelCoordinate =ᶠ[𝓝 (centralRadius x)] (e.symm : ℝ → ℝ) :=
    h.localInverse_unique (Eventually.of_forall centralModelCoordinate_radius)
  exact hi.congr_of_eventuallyEq heq

def centralPulledProfile (c x : ℝ) : ℝ :=
  c * centralDensityRoot x ^ 2 * deriv centralRadius x

/-- The profile is now a function of the genuine radius. -/
def centralRadialProfile (c r : ℝ) : ℝ :=
  centralPulledProfile c (centralModelCoordinate r)

theorem centralRadialProfile_pullback (c x : ℝ) :
    centralRadialProfile c (centralRadius x) =
      c * centralDensityRoot x ^ 2 * deriv centralRadius x := by
  simp only [centralRadialProfile, centralModelCoordinate_radius, centralPulledProfile]

theorem contDiff_centralPulledProfile (c : ℝ) : ContDiff ℝ ∞ (centralPulledProfile c) :=
  (contDiff_const.mul (contDiff_centralDensityRoot.pow 2)).mul
    (contDiff_infty_iff_deriv.mp contDiff_centralRadius).2

theorem contDiffAt_centralRadialProfile (c x : ℝ) :
    ContDiffAt ℝ ∞ (centralRadialProfile c) (centralRadius x) :=
  (contDiff_centralPulledProfile c).contDiffAt.comp _ (contDiffAt_centralModelCoordinate x)

theorem centralRadialProfile_pos {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    0 < centralRadialProfile c r := by
  rw [← centralRadius_modelCoordinate hr, centralRadialProfile_pullback]
  exact mul_pos (mul_pos hc (sq_pos_of_pos (centralDensityRoot_pos _)))
    (deriv_centralRadius_pos _)

theorem contDiffOn_centralRadialProfile (c : ℝ) :
    ContDiffOn ℝ ∞ (centralRadialProfile c) (Ioi 0) := by
  intro r hr
  have h := contDiffAt_centralRadialProfile c (centralModelCoordinate r)
  rw [centralRadius_modelCoordinate hr] at h
  exact h.contDiffWithinAt

end ContinuousFlexibility.Radial
