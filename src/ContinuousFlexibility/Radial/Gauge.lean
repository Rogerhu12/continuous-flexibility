import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The logarithmic radial gauge

Section 5, equation `rad-eq-rm13` of the supplied manuscript uses
`u(r) = r^(j²) V(log r)`. This file proves actual derivative identities on
the positive half-line, with a real exponent `a` (later specialized to `j²`).
The identities do not assert existence of a radial reference or an inverse.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Filter
open scoped Topology

/-- The power gauge in the original radial variable. -/
def gaugeLift (a : ℝ) (V : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ a * V (Real.log r)

/-- Its first derivative, with a separately supplied logarithmic derivative. -/
def gaugeFirst (a : ℝ) (V V₁ : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ (a - 1) * (a * V (Real.log r) + V₁ (Real.log r))

/-- The radial Jacobi expression; the angular eigenvalue is `a = j²`. -/
def radialJacobi (a : ℝ) (w u : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (fun t => w t * deriv u t) r - a * deriv w r / r * u r

/-- Chain and product rules for the logarithmic power gauge. -/
theorem hasDerivAt_gaugeLift {a r v₁ : ℝ} {V : ℝ → ℝ}
    (hr : 0 < r) (hV : HasDerivAt V v₁ (Real.log r)) :
    HasDerivAt (gaugeLift a V)
      (r ^ (a - 1) * (a * V (Real.log r) + v₁)) r := by
  have hp := Real.hasDerivAt_rpow_const (p := a) (Or.inl (ne_of_gt hr))
  have hv := hV.comp r (Real.hasDerivAt_log (ne_of_gt hr))
  unfold gaugeLift
  convert hp.mul hv using 1
  · rfl
  · simp only [Real.rpow_sub hr a 1, Real.rpow_one, Function.comp_apply]
    field_simp [ne_of_gt hr]

/-- The derivative formula with mathlib's actual derivative of `V`. -/
theorem deriv_gaugeLift {a r : ℝ} {V : ℝ → ℝ}
    (hr : 0 < r) (hV : DifferentiableAt ℝ V (Real.log r)) :
    deriv (gaugeLift a V) r = gaugeFirst a V (deriv V) r :=
  (hasDerivAt_gaugeLift hr hV.hasDerivAt).deriv

/-- Differentiating the first derivative gives the exact second-order gauge. -/
theorem hasDerivAt_gaugeFirst {a r v₁ v₂ : ℝ} {V V₁ : ℝ → ℝ}
    (hr : 0 < r) (hV : HasDerivAt V v₁ (Real.log r))
    (hV₁ : HasDerivAt V₁ v₂ (Real.log r)) :
    HasDerivAt (gaugeFirst a V V₁)
      (r ^ (a - 2) *
        (a * (a - 1) * V (Real.log r) +
          (a - 1) * V₁ (Real.log r) + a * v₁ + v₂)) r := by
  have hp := Real.hasDerivAt_rpow_const (p := a - 1) (Or.inl (ne_of_gt hr))
  have hl := Real.hasDerivAt_log (ne_of_gt hr)
  have hv := ((hV.comp r hl).const_mul a).add (hV₁.comp r hl)
  unfold gaugeFirst
  convert hp.mul hv using 1
  · rfl
  · rw [show a - 1 - 1 = a - 2 by ring]
    simp only [Real.rpow_sub hr a 1, Real.rpow_sub hr a 2, Real.rpow_one,
      Real.rpow_two, Function.comp_apply, Pi.add_apply]
    field_simp [ne_of_gt hr]
    ring

/-- The actual second derivative when `V` is differentiable everywhere and
its first derivative is differentiable at the logarithmic point. -/
theorem deriv_deriv_gaugeLift {a r : ℝ} {V : ℝ → ℝ}
    (hr : 0 < r) (hV : Differentiable ℝ V)
    (hV₁ : DifferentiableAt ℝ (deriv V) (Real.log r)) :
    deriv (deriv (gaugeLift a V)) r =
      r ^ (a - 2) * (a * (a - 1) * V (Real.log r) +
        (2 * a - 1) * deriv V (Real.log r) + deriv (deriv V) (Real.log r)) := by
  have hd := hasDerivAt_gaugeFirst (a := a) hr
    (hV (Real.log r)).hasDerivAt hV₁.hasDerivAt
  have heq : deriv (gaugeLift a V) =ᶠ[𝓝 r] gaugeFirst a V (deriv V) := by
    filter_upwards [eventually_gt_nhds hr] with t ht
    exact deriv_gaugeLift ht (hV (Real.log t))
  have hactual := hd.congr_of_eventuallyEq heq
  convert hactual.deriv using 1
  ring

/-- The exact radial gauge identity, without division by the profile `w`.
All derivatives in this statement are actual derivatives of the functions. -/
theorem radialJacobi_gauge {a r : ℝ} {w V : ℝ → ℝ}
    (hr : 0 < r) (hw : DifferentiableAt ℝ w r)
    (hV : Differentiable ℝ V)
    (hV₁ : DifferentiableAt ℝ (deriv V) (Real.log r)) :
    radialJacobi a w (gaugeLift a V) r =
      r ^ (a - 2) *
        (w r * deriv (deriv V) (Real.log r) +
          (r * deriv w r + (2 * a - 1) * w r) * deriv V (Real.log r) +
          a * (a - 1) * w r * V (Real.log r)) := by
  have hd := hasDerivAt_gaugeFirst (a := a) hr
    (hV (Real.log r)).hasDerivAt hV₁.hasDerivAt
  have hf := hw.hasDerivAt.mul hd
  have heq : (fun t => w t * deriv (gaugeLift a V) t) =ᶠ[𝓝 r]
      (fun t => w t * gaugeFirst a V (deriv V) t) := by
    filter_upwards [eventually_gt_nhds hr] with t ht
    rw [deriv_gaugeLift ht (hV (Real.log t))]
  have hactual := hf.congr_of_eventuallyEq heq
  unfold radialJacobi
  rw [hactual.deriv]
  unfold gaugeFirst gaugeLift
  simp only [Real.rpow_sub hr a 1, Real.rpow_sub hr a 2, Real.rpow_one,
    Real.rpow_two]
  field_simp [ne_of_gt hr]
  ring

/-- The usual divided gauge formula on a nonvanishing radial profile. -/
theorem radialJacobi_gauge_divided {a r : ℝ} {w V : ℝ → ℝ}
    (hr : 0 < r) (hw : DifferentiableAt ℝ w r)
    (hw₀ : w r ≠ 0) (hV : Differentiable ℝ V)
    (hV₁ : DifferentiableAt ℝ (deriv V) (Real.log r)) :
    radialJacobi a w (gaugeLift a V) r =
      w r * r ^ (a - 2) *
        (deriv (deriv V) (Real.log r) +
          (r * deriv w r / w r + 2 * a - 1) * deriv V (Real.log r) +
          a * (a - 1) * V (Real.log r)) := by
  rw [radialJacobi_gauge hr hw hV hV₁]
  field_simp [hw₀]
  ring

/-- The integrating factor `p_j = w r^(2 j² - 1)` in the coordinate `y = log r`. -/
def logGaugeWeight (a : ℝ) (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  w (Real.exp y) * Real.exp ((2 * a - 1) * y)

theorem logGaugeWeight_eq (a : ℝ) (w : ℝ → ℝ) (y : ℝ) :
    logGaugeWeight a w y = w (Real.exp y) * (Real.exp y) ^ (2 * a - 1) := by
  unfold logGaugeWeight
  rw [← Real.exp_mul, mul_comm y (2 * a - 1)]

/-- The divergence-form expression in the logarithmic coordinate. -/
def logGaugeEquation (a : ℝ) (w V : ℝ → ℝ) (y : ℝ) : ℝ :=
  deriv (fun t => logGaugeWeight a w t * deriv V t) y +
    a * (a - 1) * logGaugeWeight a w y * V y

/-- Direct differentiation of the logarithmic integrating factor. -/
theorem logGaugeEquation_eq {a y : ℝ} {w V : ℝ → ℝ}
    (hw : DifferentiableAt ℝ w (Real.exp y))
    (hV₁ : DifferentiableAt ℝ (deriv V) y) :
    logGaugeEquation a w V y =
      Real.exp ((2 * a - 1) * y) *
        (w (Real.exp y) * deriv (deriv V) y +
          (Real.exp y * deriv w (Real.exp y) + (2 * a - 1) * w (Real.exp y)) *
            deriv V y + a * (a - 1) * w (Real.exp y) * V y) := by
  have hwexp := hw.hasDerivAt.comp y (Real.hasDerivAt_exp y)
  have hexp := ((hasDerivAt_id y).const_mul (2 * a - 1)).exp
  have hf := (hwexp.mul hexp).mul hV₁.hasDerivAt
  change HasDerivAt
    (fun t => w (Real.exp t) * Real.exp ((2 * a - 1) * t) * deriv V t) _ y at hf
  unfold logGaugeEquation logGaugeWeight
  rw [hf.deriv]
  simp only [Function.comp_apply, Pi.mul_apply, id_eq, mul_one]
  ring

/-- The exact factor for nonhomogeneous sources under the logarithmic gauge.
This records more information than equivalence of the homogeneous equations. -/
theorem logGaugeEquation_source_identity {a y : ℝ} {w V : ℝ → ℝ}
    (hw : DifferentiableAt ℝ w (Real.exp y)) (hV : Differentiable ℝ V)
    (hV₁ : DifferentiableAt ℝ (deriv V) y) :
    logGaugeEquation a w V y = Real.exp ((a + 1) * y) *
      radialJacobi a w (gaugeLift a V) (Real.exp y) := by
  have hVlog : DifferentiableAt ℝ (deriv V) (Real.log (Real.exp y)) := by
    simpa only [Real.log_exp] using hV₁
  rw [logGaugeEquation_eq hw hV₁,
    radialJacobi_gauge (Real.exp_pos y) hw hV hVlog]
  simp only [Real.log_exp]
  rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp,
    ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The exact equivalence behind Section 5, equation `rad-eq-rm13`.
Specializing `a` to `j²` gives `Λ = j² (j² - 1)`. -/
theorem radialJacobi_gauge_eq_zero_iff {a y : ℝ} {w V : ℝ → ℝ}
    (hw : DifferentiableAt ℝ w (Real.exp y)) (hV : Differentiable ℝ V)
    (hV₁ : DifferentiableAt ℝ (deriv V) y) :
    radialJacobi a w (gaugeLift a V) (Real.exp y) = 0 ↔
      logGaugeEquation a w V y = 0 := by
  have hVlog : DifferentiableAt ℝ (deriv V) (Real.log (Real.exp y)) := by
    simpa only [Real.log_exp] using hV₁
  rw [radialJacobi_gauge (Real.exp_pos y) hw hV hVlog,
    logGaugeEquation_eq hw hV₁]
  simp only [Real.log_exp]
  rw [mul_eq_zero, mul_eq_zero]
  simp only [ne_of_gt (Real.rpow_pos_of_pos (Real.exp_pos y) (a - 2)),
    ne_of_gt (Real.exp_pos ((2 * a - 1) * y)), false_or]

end

end ContinuousFlexibility.Radial
