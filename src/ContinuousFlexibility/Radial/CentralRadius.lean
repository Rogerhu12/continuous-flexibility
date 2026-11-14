module

public import ContinuousFlexibility.Radial.GaussianLaplace
public import ContinuousFlexibility.Radial.CentralTravelAngle
public import ContinuousFlexibility.Radial.Liouville
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The actual positive increasing central radius

The radius is the convergent Laplace--Gaussian integral in Section 4,
`eq:rad-eq-sc6`. Its differential equation and positivity follow from the
proved integral derivatives and integration-by-parts recurrence.
The full end expansions and the oscillator's closed spectral realization
remain separate results; neither is assumed to construct this radius.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The positive oscillator solution from the paper's actual half-line integral. -/
def gaussianLaplacePsi (β x : ℝ) : ℝ :=
  exp (-x ^ 2 / 2) * gaussianLaplaceMoment β x

theorem gaussianLaplacePsi_pos {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    0 < gaussianLaplacePsi β x :=
  mul_pos (exp_pos _) (gaussianLaplaceMoment_pos hβ x)

theorem contDiff_gaussianLaplacePsi {β : ℝ} (hβ : 0 < β) :
    ContDiff ℝ ∞ (gaussianLaplacePsi β) :=
  (((contDiff_id.pow 2).neg.div_const 2).exp).mul (contDiff_gaussianLaplaceMoment hβ)

theorem hasDerivAt_gaussianLaplacePsi {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    HasDerivAt (gaussianLaplacePsi β)
      (exp (-x ^ 2 / 2) * (sqrt 2 * gaussianLaplaceMoment (β + 1) x -
        x * gaussianLaplaceMoment β x)) x := by
  unfold gaussianLaplacePsi
  convert ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).mul
    (hasDerivAt_gaussianLaplaceMoment hβ x) using 1
  · funext y
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, id_eq]
  · simp only [Pi.pow_apply, Pi.neg_apply, id_eq]
    ring

theorem deriv_gaussianLaplacePsi {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    deriv (gaussianLaplacePsi β) x =
      exp (-x ^ 2 / 2) * (sqrt 2 * gaussianLaplaceMoment (β + 1) x -
        x * gaussianLaplaceMoment β x) :=
  (hasDerivAt_gaussianLaplacePsi hβ x).deriv

/-- Actual second derivative: the moment recurrence gives the oscillator ODE. -/
theorem hasDerivAt_deriv_gaussianLaplacePsi {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    HasDerivAt (deriv (gaussianLaplacePsi β))
      ((x ^ 2 + (2 * β - 1)) * gaussianLaplacePsi β x) x := by
  have heq : deriv (gaussianLaplacePsi β) = fun y =>
      exp (-y ^ 2 / 2) * (sqrt 2 * gaussianLaplaceMoment (β + 1) y -
        y * gaussianLaplaceMoment β y) := funext (deriv_gaussianLaplacePsi hβ)
  rw [heq]
  convert ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).mul
    (((hasDerivAt_gaussianLaplaceMoment (by linarith : 0 < β + 1) x).const_mul (sqrt 2)).sub
      ((hasDerivAt_id x).mul (hasDerivAt_gaussianLaplaceMoment hβ x))) using 1
  · funext y
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, id_eq]
  · simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, id_eq]
    rw [gaussianLaplaceMoment_recurrence hβ x]
    unfold gaussianLaplacePsi
    ring_nf
    norm_num [sq_sqrt]
    rw [show sqrt (2 : ℝ) ^ 3 = 2 * sqrt 2 by
      rw [pow_succ, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]]
    ring

theorem gaussianLaplacePsi_ode {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    deriv (deriv (gaussianLaplacePsi β)) x =
      (x ^ 2 + (2 * β - 1)) * gaussianLaplacePsi β x :=
  (hasDerivAt_deriv_gaussianLaplacePsi hβ x).deriv

theorem deriv_gaussianLaplacePsi_pos_of_nonpos
    {β x : ℝ} (hβ : 0 < β) (hx : x ≤ 0) :
    0 < deriv (gaussianLaplacePsi β) x := by
  rw [deriv_gaussianLaplacePsi hβ x]
  apply mul_pos (exp_pos _)
  have hpos := mul_pos (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    (gaussianLaplaceMoment_pos (by linarith : 0 < β + 1) x)
  have hneg := mul_nonpos_of_nonpos_of_nonneg hx (gaussianLaplaceMoment_pos hβ x).le
  linarith

/-- For `2β-1>0`, convexity propagates the positive derivative from zero
to the right. On the left, positivity follows directly from the integral. -/
theorem deriv_gaussianLaplacePsi_pos {β : ℝ} (hβ : 1 / 2 < β) (x : ℝ) :
    0 < deriv (gaussianLaplacePsi β) x := by
  have hb : 0 < β := by linarith
  by_cases hx : x ≤ 0
  · exact deriv_gaussianLaplacePsi_pos_of_nonpos hb hx
  · have hm : StrictMono (deriv (gaussianLaplacePsi β)) := by
      apply strictMono_of_deriv_pos
      intro y
      rw [gaussianLaplacePsi_ode hb y]
      exact mul_pos (by nlinarith [sq_nonneg y]) (gaussianLaplacePsi_pos hb y)
    exact lt_trans (deriv_gaussianLaplacePsi_pos_of_nonpos hb (le_refl 0))
      (hm (lt_of_not_ge hx))

def centralRadiusA : ℝ := sqrt (4 * centralOscillatorA - 2)

def centralRadiusC : ℝ := 3 * centralOscillatorA - 2

def centralRadiusAlpha : ℝ := (centralRadiusC + 1) / 2

theorem centralOscillatorA_gt_two_thirds : (2 / 3 : ℝ) < centralOscillatorA := by
  unfold centralOscillatorA
  have hs : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  rw [lt_div_iff₀ hs]
  nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem centralRadiusA_pos : 0 < centralRadiusA := by
  unfold centralRadiusA
  apply sqrt_pos.mpr
  linarith [centralOscillatorA_gt_two_thirds]

theorem centralRadiusA_sq : centralRadiusA ^ 2 = 4 * centralOscillatorA - 2 := by
  unfold centralRadiusA
  exact sq_sqrt (by linarith [centralOscillatorA_gt_two_thirds])

theorem centralRadiusC_pos : 0 < centralRadiusC := by
  unfold centralRadiusC
  linarith [centralOscillatorA_gt_two_thirds]

theorem centralRadiusAlpha_gt_half : (1 / 2 : ℝ) < centralRadiusAlpha := by
  unfold centralRadiusAlpha
  linarith [centralRadiusC_pos]

/-- The actual `ψ₁` in the manuscript. -/
def centralRadiusPsi : ℝ → ℝ := gaussianLaplacePsi centralRadiusAlpha

/-- The full-line radius, not an arbitrary solution of the radius equation. -/
def centralRadius (x : ℝ) : ℝ := exp (centralRadiusA * x) * centralRadiusPsi x

def centralDensityRoot (x : ℝ) : ℝ := exp (-centralRadiusA * x)

theorem centralRadiusPsi_pos (x : ℝ) : 0 < centralRadiusPsi x :=
  gaussianLaplacePsi_pos (by linarith [centralRadiusAlpha_gt_half]) x

theorem deriv_centralRadiusPsi_pos (x : ℝ) : 0 < deriv centralRadiusPsi x :=
  deriv_gaussianLaplacePsi_pos centralRadiusAlpha_gt_half x

theorem contDiff_centralRadiusPsi : ContDiff ℝ ∞ centralRadiusPsi :=
  contDiff_gaussianLaplacePsi (by linarith [centralRadiusAlpha_gt_half])

theorem centralRadiusPsi_ode (x : ℝ) :
    deriv (deriv centralRadiusPsi) x = (x ^ 2 + centralRadiusC) * centralRadiusPsi x := by
  have hc : 2 * centralRadiusAlpha - 1 = centralRadiusC := by
    unfold centralRadiusAlpha
    ring
  change deriv (deriv (gaussianLaplacePsi centralRadiusAlpha)) x = _
  rw [gaussianLaplacePsi_ode (by linarith [centralRadiusAlpha_gt_half]) x, hc]
  rfl

theorem contDiff_centralRadius : ContDiff ℝ ∞ centralRadius :=
  (contDiff_const.mul contDiff_id).exp.mul contDiff_centralRadiusPsi

theorem centralRadius_pos (x : ℝ) : 0 < centralRadius x :=
  mul_pos (exp_pos _) (centralRadiusPsi_pos x)

theorem hasDerivAt_centralRadius (x : ℝ) :
    HasDerivAt centralRadius
      (exp (centralRadiusA * x) *
        (centralRadiusA * centralRadiusPsi x + deriv centralRadiusPsi x)) x := by
  convert (((hasDerivAt_id x).const_mul centralRadiusA).exp).mul
    ((contDiff_centralRadiusPsi.differentiable (by simp)) x).hasDerivAt using 1
  · funext y
    simp only [centralRadius, Pi.mul_apply, id_eq]
  · simp only [id_eq]
    ring

theorem deriv_centralRadius (x : ℝ) :
    deriv centralRadius x = exp (centralRadiusA * x) *
      (centralRadiusA * centralRadiusPsi x + deriv centralRadiusPsi x) :=
  (hasDerivAt_centralRadius x).deriv

/-- Strict increase has a quantitative margin, exactly as needed for a
genuine radius coordinate in the Liouville construction. -/
theorem deriv_centralRadius_gt (x : ℝ) :
    centralRadiusA * centralRadius x < deriv centralRadius x := by
  rw [deriv_centralRadius]
  unfold centralRadius
  have hp := mul_pos (exp_pos (centralRadiusA * x)) (deriv_centralRadiusPsi_pos x)
  nlinarith

theorem deriv_centralRadius_pos (x : ℝ) : 0 < deriv centralRadius x :=
  lt_trans (mul_pos centralRadiusA_pos (centralRadius_pos x)) (deriv_centralRadius_gt x)

theorem strictMono_centralRadius : StrictMono centralRadius :=
  strictMono_of_deriv_pos deriv_centralRadius_pos

/-- The actual integral-defined radius satisfies the central radius ODE. -/
theorem centralRadius_ode (x : ℝ) :
    deriv (deriv centralRadius) x - 2 * centralRadiusA * deriv centralRadius x +
      (centralOscillatorA - x ^ 2) * centralRadius x = 0 := by
  have hd : deriv centralRadius = fun y => exp (centralRadiusA * y) *
      (centralRadiusA * centralRadiusPsi y + deriv centralRadiusPsi y) :=
    funext deriv_centralRadius
  have hψ := (contDiff_centralRadiusPsi.differentiable (by simp) x).hasDerivAt
  have hψsmooth : ContDiff ℝ 2 centralRadiusPsi := contDiff_centralRadiusPsi.of_le (by simp)
  have hψ' := (hψsmooth.differentiable_deriv_two x).hasDerivAt
  have hD := (((hasDerivAt_id x).const_mul centralRadiusA).exp).mul
    ((hψ.const_mul centralRadiusA).add hψ')
  have heq := hD.deriv
  change deriv (fun y => exp (centralRadiusA * y) *
    (centralRadiusA * centralRadiusPsi y + deriv centralRadiusPsi y)) x = _ at heq
  simp only [Pi.add_apply, id_eq] at heq
  rw [hd, heq, centralRadiusPsi_ode]
  unfold centralRadius centralRadiusC
  simp only [mul_one]
  ring_nf
  rw [centralRadiusA_sq]
  ring

theorem contDiff_centralDensityRoot : ContDiff ℝ ∞ centralDensityRoot :=
  (contDiff_const.mul contDiff_id).exp

theorem centralDensityRoot_pos (x : ℝ) : 0 < centralDensityRoot x := exp_pos _

theorem hasDerivAt_centralDensityRoot (x : ℝ) :
    HasDerivAt centralDensityRoot (-centralRadiusA * centralDensityRoot x) x := by
  convert ((hasDerivAt_id x).const_mul (-centralRadiusA)).exp using 1
  · funext y
    simp only [centralDensityRoot, id_eq]
  · simp only [centralDensityRoot, id_eq]
    ring

theorem deriv_centralDensityRoot (x : ℝ) :
    deriv centralDensityRoot x = -centralRadiusA * centralDensityRoot x :=
  (hasDerivAt_centralDensityRoot x).deriv

theorem deriv_deriv_centralDensityRoot (x : ℝ) :
    deriv (deriv centralDensityRoot) x = centralRadiusA ^ 2 * centralDensityRoot x := by
  have hd : deriv centralDensityRoot = fun y => -centralRadiusA * centralDensityRoot y :=
    funext deriv_centralDensityRoot
  rw [hd]
  convert ((hasDerivAt_centralDensityRoot x).const_mul (-centralRadiusA)).deriv using 1
  ring

/-- The potential used in Liouville's identity is the paper's actual
quadratic coefficient, for the integral-defined increasing radius. -/
theorem centralRadius_liouvilleRho (x : ℝ) :
    liouvilleRho centralRadius centralDensityRoot x = centralOscillatorA - x ^ 2 := by
  have hR := (centralRadius_pos x).ne'
  have hs := (centralDensityRoot_pos x).ne'
  have ho := centralRadius_ode x
  unfold liouvilleRho
  rw [deriv_centralDensityRoot]
  field_simp [hs, hR]
  nlinarith

theorem centralDensityRoot_liouvilleV0 (x : ℝ) :
    liouvilleV0 centralDensityRoot x = centralRadiusA ^ 2 := by
  unfold liouvilleV0
  rw [deriv_deriv_centralDensityRoot]
  exact mul_div_cancel_right₀ _ (centralDensityRoot_pos x).ne'

/-- The actual constructed coordinate and density realize the central
oscillator expression for every real frequency. -/
theorem central_liouvilleSchrodinger (j : ℝ) (ψ : ℝ → ℝ) (x : ℝ) :
    liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ x =
      -deriv (deriv ψ) x +
        (j ^ 2 * x ^ 2 + centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA) * ψ x := by
  unfold liouvilleSchrodinger
  rw [centralRadius_liouvilleRho, centralDensityRoot_liouvilleV0]
  ring

end ContinuousFlexibility.Radial
