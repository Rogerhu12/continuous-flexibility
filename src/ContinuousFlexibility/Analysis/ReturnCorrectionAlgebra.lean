import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebra and calculus of the return correction

This is the scalar construction in steps 1--3 of the return-correction
proposition, `paper/flexible-surface-readable/07-fixed-geometry.tex`,
lines 905--978. The interpolation acts on the initial point of the old
flow. Its coefficients are reconstructed from the two characteristic
slopes, with the leading radial coefficient left unchanged.

The lemmas keep the analytic hypotheses explicit. They do not assert
existence of the ordinary flow, bounds on its inverse, or membership of
the resulting divergence error in the weighted source space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ContDiff

/-! ## Interpolation of the initial point -/

/-- The interpolation `J = id + χ (K - id)` used to correct a return. -/
def returnInterpolation (χ : ℝ) (K : ℝ → ℝ) (θ : ℝ) : ℝ :=
  θ + χ * (K θ - θ)

theorem returnInterpolation_apply (χ : ℝ) (K : ℝ → ℝ) (θ : ℝ) :
    returnInterpolation χ K θ = θ + χ * (K θ - θ) := rfl

theorem returnInterpolation_zero (K : ℝ → ℝ) (θ : ℝ) :
    returnInterpolation 0 K θ = θ := by
  rw [returnInterpolation_apply, zero_mul, add_zero]

theorem returnInterpolation_one (K : ℝ → ℝ) (θ : ℝ) :
    returnInterpolation 1 K θ = K θ := by
  rw [returnInterpolation_apply, one_mul]
  ring

theorem returnInterpolation_eq_convexCombination (χ : ℝ) (K : ℝ → ℝ) (θ : ℝ) :
    returnInterpolation χ K θ = (1 - χ) * θ + χ * K θ := by
  rw [returnInterpolation_apply]
  ring

/-- No smallness assumption is needed for monotonicity: the correction
is a convex combination of two strictly increasing maps. -/
theorem returnInterpolation_strictMono {χ : ℝ} {K : ℝ → ℝ}
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hK : StrictMono K) :
    StrictMono (returnInterpolation χ K) := by
  intro x y hxy
  rw [returnInterpolation_eq_convexCombination, returnInterpolation_eq_convexCombination]
  by_cases hχ : χ = 1
  · simpa only [hχ, sub_self, zero_mul, one_mul, zero_add] using hK hxy
  · have hpositive : 0 < (1 - χ) * (y - x) :=
      mul_pos (by linarith) (sub_pos.mpr hxy)
    have hnonnegative : 0 ≤ χ * (K y - K x) :=
      mul_nonneg hχ0 (sub_nonneg.mpr (hK hxy).le)
    nlinarith

theorem returnInterpolation_hasDerivAt {χ θ k' : ℝ} {K : ℝ → ℝ}
    (hK : HasDerivAt K k' θ) :
    HasDerivAt (returnInterpolation χ K) (1 + χ * (k' - 1)) θ := by
  exact (hasDerivAt_id θ).add ((hK.sub (hasDerivAt_id θ)).const_mul χ)

theorem returnInterpolation_deriv_pos {χ k' : ℝ}
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hk' : 0 < k') :
    0 < 1 + χ * (k' - 1) := by
  by_cases hχ : χ = 1
  · subst χ
    linarith
  · have hnonnegative : 0 ≤ χ * k' := mul_nonneg hχ0 hk'.le
    nlinarith

/-- Interpolation preserves the chosen lift period. -/
theorem returnInterpolation_periodic_lift {K : ℝ → ℝ} {P : ℝ}
    (hK : ∀ θ, K (θ + P) = K θ + P) (χ θ : ℝ) :
    returnInterpolation χ K (θ + P) = returnInterpolation χ K θ + P := by
  rw [returnInterpolation_apply, returnInterpolation_apply, hK]
  ring

/-! ## Conjugation and the two endpoint returns -/

/-- The conjugation formula for `K`, written with the actual inverse
maps rather than an unspecified group operation. -/
theorem returnCorrection_conjugation
    (f fInv hL hR hRInv e : ℝ → ℝ) (T θ : ℝ)
    (hreturn : hR (f θ) + e (hR (f θ)) = hL θ - T) :
    fInv (hRInv (hL θ - T)) =
      fInv (hRInv (hR (f θ) + e (hR (f θ)))) := by
  rw [hreturn]

/-- The reparametrized flow is the identity at the left endpoint and
the required corrected return at the right endpoint. -/
theorem returnCorrection_flow_endpoints
    (Φ : ℝ → ℝ → ℝ) (χ f fInv hL hRInv : ℝ → ℝ) (l r T : ℝ)
    (hleft : ∀ θ, Φ l θ = θ) (hright : ∀ θ, Φ r θ = f θ)
    (hχleft : χ l = 0) (hχright : χ r = 1)
    (hf : Function.RightInverse fInv f) (θ : ℝ) :
    Φ l (returnInterpolation (χ l) (fun t => fInv (hRInv (hL t - T))) θ) = θ ∧
    Φ r (returnInterpolation (χ r) (fun t => fInv (hRInv (hL t - T))) θ) =
      hRInv (hL θ - T) := by
  constructor
  · rw [hχleft, returnInterpolation_zero, hleft]
  · rw [hχright, returnInterpolation_one, hright, hf]

/-- Odd boundary charts convert the reflected minus return into the
plus return. This is a statement about both actual returns. -/
theorem returnCorrection_reflected_return
    (f hL hR : ℝ → ℝ) (T : ℝ)
    (hLodd : ∀ θ, hL (-θ) = -hL θ)
    (hRodd : ∀ θ, hR (-θ) = -hR θ)
    (hminus : ∀ θ, hR (f θ) = hL θ - T) (θ : ℝ) :
    hR (-f (-θ)) = hL θ + T := by
  rw [hRodd, hminus, hLodd]
  ring

/-- Endpoint return formulas for the constructed target map. -/
theorem returnCorrection_target_returns
    (hL hR hRInv : ℝ → ℝ) (T : ℝ)
    (hLodd : ∀ θ, hL (-θ) = -hL θ)
    (hRodd : ∀ θ, hR (-θ) = -hR θ)
    (hInv : Function.RightInverse hRInv hR) (θ : ℝ) :
    hR (hRInv (hL θ - T)) = hL θ - T ∧
    hR (-hRInv (hL (-θ) - T)) = hL θ + T := by
  exact ⟨hInv _, returnCorrection_reflected_return
    (fun t => hRInv (hL t - T)) hL hR T hLodd hRodd (fun t => hInv _) θ⟩

/-! ## The corrected velocity -/

/-- The chain rule for `Φ(r, J_r θ₀)`, before rewriting the initial
point by the inverse of the corrected flow. -/
theorem returnCorrection_flow_hasDerivAt
    (Φ : ℝ × ℝ → ℝ) (χ K : ℝ → ℝ) (r θ χ' c p : ℝ)
    (hχ : HasDerivAt χ χ' r)
    (hΦ : HasFDerivAt Φ
      (c • ContinuousLinearMap.fst ℝ ℝ ℝ + p • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (r, returnInterpolation (χ r) K θ)) :
    HasDerivAt (fun t => Φ (t, returnInterpolation (χ t) K θ))
      (c + p * χ' * (K θ - θ)) r := by
  have hJ : HasDerivAt (fun t => returnInterpolation (χ t) K θ)
      (χ' * (K θ - θ)) r := by
    simpa only [returnInterpolation_apply, zero_add] using
      (hasDerivAt_const r θ).add (hχ.mul_const (K θ - θ))
  have hpath := (hasDerivAt_id r).prodMk hJ
  convert hΦ.comp_hasDerivAt r hpath using 1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.fst_apply, ContinuousLinearMap.snd_apply, smul_eq_mul, mul_one]
  ring

/-- Evaluate the velocity correction along the corrected curve. The
two inverse identities are precisely those used in the manuscript. -/
theorem returnCorrection_velocity_on_flow
    (Φ ΦInv J JInv Δ p : ℝ → ℝ) (χ' θ : ℝ)
    (hΦ : Function.LeftInverse ΦInv Φ) (hJ : Function.LeftInverse JInv J) :
    p (ΦInv (Φ (J θ))) * χ' * Δ (JInv (ΦInv (Φ (J θ)))) =
      p (J θ) * χ' * Δ θ := by
  rw [hΦ, hJ]

/-! ## Freezing the coefficient of the residual -/

/-- Fundamental theorem of calculus along a line segment, with the
displacement factored out. This formula also holds when the
displacement is zero. -/
theorem returnCorrection_difference_integral
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (x d : ℝ) :
    F (x + d) - F x =
      d * ∫ t in (0 : ℝ)..1, deriv F (x + t * d) := by
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s => F (x + s * d))
      (d * deriv F (x + t * d)) t := by
    intro t
    convert (hdF (x + t * d)).hasDerivAt.comp t
      ((hasDerivAt_const t x).add ((hasDerivAt_id t).mul_const d)) using 1 <;> ring
  have hcontinuous : Continuous (fun t : ℝ => d * deriv F (x + t * d)) :=
    continuous_const.mul (hF.continuous_deriv (by norm_num)).comp
      (continuous_const.add (continuous_id.mul continuous_const))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) (hcontinuous.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hFTC
  simpa only [one_mul, zero_mul, add_zero] using hFTC.symm

/-- The displacement of the conjugated correction has a leading
residual factor. Freezing the other arguments makes that factor
linear in an independent residual variable. -/
theorem returnCorrection_displacement_integral
    (g gInv e : ℝ → ℝ) (hInv : Function.LeftInverse gInv g)
    (hgInv : ContDiff ℝ 1 gInv) (θ : ℝ) :
    gInv (g θ + e (g θ)) - θ =
      e (g θ) * ∫ t in (0 : ℝ)..1, deriv gInv (g θ + t * e (g θ)) := by
  calc gInv (g θ + e (g θ)) - θ
      = gInv (g θ + e (g θ)) - gInv (g θ) := by rw [hInv]
    _ = _ := returnCorrection_difference_integral hgInv (g θ) (e (g θ))

/-! ## Reconstruction of the symmetric operator -/

/-- Discriminant of the coefficients reconstructed from drift and
positive speed. -/
theorem returnCorrection_discriminant (a d v : ℝ) :
    (a * d) ^ 2 - a * (a * (d ^ 2 - v ^ 2)) = (a * v) ^ 2 := by
  ring

/-- The sign hypotheses are essential: they select the actual two
square-root characteristic slopes, not just the roots of a polynomial. -/
theorem returnCorrection_characteristic_slopes {a v : ℝ} (d : ℝ)
    (ha : 0 < a) (hv : 0 ≤ v) :
    (a * d) / a - Real.sqrt ((a * d) ^ 2 - a * (a * (d ^ 2 - v ^ 2))) / a = d - v ∧
    (a * d) / a + Real.sqrt ((a * d) ^ 2 - a * (a * (d ^ 2 - v ^ 2))) / a = d + v := by
  rw [returnCorrection_discriminant, Real.sqrt_sq (mul_nonneg ha.le hv)]
  simp only [mul_div_cancel_left₀ _ ha.ne']
  exact ⟨rfl, rfl⟩

theorem returnCorrection_drift_speed (minus plus : ℝ) :
    (plus + minus) / 2 - (plus - minus) / 2 = minus ∧
    (plus + minus) / 2 + (plus - minus) / 2 = plus := by
  constructor <;> ring

/-- Reflection gives odd drift and even speed. -/
theorem returnCorrection_reflected_parity (minus : ℝ → ℝ) (θ : ℝ) :
    (-minus (-(-θ)) + minus (-θ)) / 2 =
      -((-minus (-θ) + minus θ) / 2) ∧
    (-minus (-(-θ)) - minus (-θ)) / 2 =
      (-minus (-θ) - minus θ) / 2 := by
  simp only [neg_neg]
  constructor <;> ring

/-- Parity of the reconstructed coefficients. -/
theorem returnCorrection_coefficients_parity
    (a d v : ℝ → ℝ)
    (ha : ∀ θ, a (-θ) = a θ)
    (hd : ∀ θ, d (-θ) = -d θ)
    (hv : ∀ θ, v (-θ) = v θ) (θ : ℝ) :
    a (-θ) * d (-θ) = -(a θ * d θ) ∧
    a (-θ) * (d (-θ) ^ 2 - v (-θ) ^ 2) = a θ * (d θ ^ 2 - v θ ^ 2) := by
  rw [ha, hd, hv]
  constructor <;> ring

section CoefficientError

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- The two independent coefficient errors, after freezing the state
and its actual residual. The result is a real linear map in the new
residual argument. -/
def returnCoefficientError (a d v : ℝ) (D V : E →ₗ[ℝ] ℝ) (e : E) :
    E →ₗ[ℝ] ℝ × ℝ :=
  ((-a) • D).prod
    (((-a * (2 * d + D e)) • D) + ((a * (2 * v + V e)) • V))

theorem returnCoefficientError_apply (a d v : ℝ) (D V : E →ₗ[ℝ] ℝ) (e r : E) :
    returnCoefficientError a d v D V e r =
      (-a * D r, -a * (2 * d + D e) * D r + a * (2 * v + V e) * V r) := by
  simp only [returnCoefficientError, LinearMap.prod_apply, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul]

/-- Substituting the actual residual produces the exact difference
between the old and corrected coefficients. -/
theorem returnCoefficientError_at_residual
    (a d v : ℝ) (D V : E →ₗ[ℝ] ℝ) (e : E) :
    returnCoefficientError a d v D V e e =
      (a * d - a * (d + D e),
        a * (d ^ 2 - v ^ 2) - a * ((d + D e) ^ 2 - (v + V e) ^ 2)) := by
  rw [returnCoefficientError_apply]
  congr 1 <;> ring

end CoefficientError

end ContinuousFlexibility.Analysis
