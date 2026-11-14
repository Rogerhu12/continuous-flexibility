module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Order.Hom.Set
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

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

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

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
      mul_pos (sub_pos.mpr (lt_of_le_of_ne hχ1 hχ)) (sub_pos.mpr hxy)
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
    have hχlt : χ < 1 := lt_of_le_of_ne hχ1 hχ
    nlinarith

/-- Interpolation preserves the chosen lift period. -/
theorem returnInterpolation_periodic_lift {K : ℝ → ℝ} {P : ℝ}
    (hK : ∀ θ, K (θ + P) = K θ + P) (χ θ : ℝ) :
    returnInterpolation χ K (θ + P) = returnInterpolation χ K θ + P := by
  rw [returnInterpolation_apply, returnInterpolation_apply, hK]
  ring

/-- Surjectivity of the interpolation follows from a direct
intermediate-value argument. For a target `y` and `K z = y`, the two
points `min y z` and `max y z` bracket `y` under the interpolation. -/
theorem returnInterpolation_surjective {χ : ℝ} {K : ℝ → ℝ}
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hKcont : Continuous K)
    (hKmono : Monotone K) (hKsurj : Function.Surjective K) :
    Function.Surjective (returnInterpolation χ K) := by
  have hJcont : Continuous (returnInterpolation χ K) :=
    continuous_id.add (continuous_const.mul (hKcont.sub continuous_id))
  intro y
  obtain ⟨z, hz⟩ := hKsurj y
  apply mem_range_of_exists_le_of_exists_ge hJcont
  · refine ⟨min y z, ?_⟩
    rw [returnInterpolation_eq_convexCombination]
    have h₁ := mul_le_mul_of_nonneg_left (min_le_left y z) (sub_nonneg.mpr hχ1)
    have h₂ := mul_le_mul_of_nonneg_left (hKmono (min_le_right y z)) hχ0
    rw [hz] at h₂
    nlinarith
  · refine ⟨max y z, ?_⟩
    rw [returnInterpolation_eq_convexCombination]
    have h₁ := mul_le_mul_of_nonneg_left (le_max_left y z) (sub_nonneg.mpr hχ1)
    have h₂ := mul_le_mul_of_nonneg_left (hKmono (le_max_right y z)) hχ0
    rw [hz] at h₂
    nlinarith

/-- The interpolation is an actual homeomorphism of the real line. -/
def returnInterpolationHomeomorph {χ : ℝ} {K : ℝ → ℝ}
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hKcont : Continuous K)
    (hKmono : StrictMono K) (hKsurj : Function.Surjective K) : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (returnInterpolation χ K)
    (returnInterpolation_strictMono hχ0 hχ1 hKmono)
    (returnInterpolation_surjective hχ0 hχ1 hKcont hKmono.monotone hKsurj)).toHomeomorph

theorem returnInterpolationHomeomorph_apply {χ : ℝ} {K : ℝ → ℝ}
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hKcont : Continuous K)
    (hKmono : StrictMono K) (hKsurj : Function.Surjective K) (θ : ℝ) :
    returnInterpolationHomeomorph hχ0 hχ1 hKcont hKmono hKsurj θ =
      returnInterpolation χ K θ := by
  simp only [returnInterpolationHomeomorph, OrderIso.coe_toHomeomorph,
    StrictMono.coe_orderIsoOfSurjective]

/-- The inverse has the expected reciprocal derivative. -/
theorem returnInterpolationHomeomorph_symm_hasDerivAt {χ : ℝ} {K : ℝ → ℝ}
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hKcont : Continuous K)
    (hKmono : StrictMono K) (hKsurj : Function.Surjective K) (y k' : ℝ)
    (hK : HasDerivAt K k'
      ((returnInterpolationHomeomorph hχ0 hχ1 hKcont hKmono hKsurj).symm y))
    (hk' : 0 < k') :
    HasDerivAt (returnInterpolationHomeomorph hχ0 hχ1 hKcont hKmono hKsurj).symm
      (1 + χ * (k' - 1))⁻¹ y := by
  apply HasDerivAt.of_local_left_inverse
    (returnInterpolationHomeomorph hχ0 hχ1 hKcont hKmono hKsurj).symm.continuous.continuousAt
    (returnInterpolation_hasDerivAt hK) (returnInterpolation_deriv_pos hχ0 hχ1 hk').ne'
  exact Filter.Eventually.of_forall fun t => by
    simpa only [returnInterpolationHomeomorph_apply] using
      (returnInterpolationHomeomorph hχ0 hχ1 hKcont hKmono hKsurj).apply_symm_apply t

/-- Smoothness of `K` and positivity of its derivative give a smooth
inverse of the interpolated map at every interpolation parameter. -/
theorem returnInterpolationHomeomorph_symm_contDiff {χ : ℝ} {K : ℝ → ℝ}
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hK : ContDiff ℝ ∞ K)
    (hKmono : StrictMono K) (hKsurj : Function.Surjective K)
    (hKpositive : ∀ θ, 0 < deriv K θ) :
    ContDiff ℝ ∞
      ((returnInterpolationHomeomorph hχ0 hχ1 hK.continuous hKmono hKsurj).symm : ℝ → ℝ) := by
  let J : ℝ ≃ₜ ℝ := returnInterpolationHomeomorph hχ0 hχ1 hK.continuous hKmono hKsurj
  have hJ : (J : ℝ → ℝ) = returnInterpolation χ K := by
    funext θ
    exact returnInterpolationHomeomorph_apply hχ0 hχ1 hK.continuous hKmono hKsurj θ
  apply J.contDiff_symm_deriv
    (f' := fun θ => 1 + χ * (deriv K θ - 1))
  · intro θ
    exact (returnInterpolation_deriv_pos hχ0 hχ1 (hKpositive θ)).ne'
  · intro θ
    rw [hJ]
    exact returnInterpolation_hasDerivAt ((hK.differentiable (by simp) θ).hasDerivAt)
  · rw [hJ]
    exact contDiff_id.add (contDiff_const.mul (hK.sub contDiff_id))

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
    have h := ((hasDerivAt_const r θ).add (hχ.mul_const (K θ - θ))).congr_deriv
      (zero_add (χ' * (K θ - θ)))
    exact h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by
        simp only [returnInterpolation_apply, Pi.add_apply])
  have hpath := (hasDerivAt_id r).prodMk hJ
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one, mul_assoc] using
      hΦ.comp_hasDerivAt r hpath

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
    simpa only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_mul, mul_one, mul_comm] using
      (hdF (x + t * d)).hasDerivAt.comp t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).mul_const d))
  have hcontinuous : Continuous (fun t : ℝ => d * deriv F (x + t * d)) :=
    continuous_const.mul ((hF.continuous_deriv_one).comp
      (continuous_const.add (continuous_id.mul continuous_const)))
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
  constructor <;> simp only [mul_div_cancel_left₀ _ ha.ne']

theorem returnCorrection_drift_speed (minus plus : ℝ) :
    (plus + minus) / 2 - (plus - minus) / 2 = minus ∧
    (plus + minus) / 2 + (plus - minus) / 2 = plus := by
  constructor <;> ring

/-- A correction smaller than half of the old speed in each
characteristic family preserves the positive speed gap. -/
theorem returnCorrection_speed_positive {v minusIncrement plusIncrement : ℝ}
    (hv : 0 < v) (hminus : |minusIncrement| ≤ v / 2)
    (hplus : |plusIncrement| ≤ v / 2) :
    v / 2 ≤ v + (plusIncrement - minusIncrement) / 2 ∧
    0 < v + (plusIncrement - minusIncrement) / 2 := by
  have h₁ := (abs_le.mp hminus).2
  have h₂ := (abs_le.mp hplus).1
  constructor <;> linarith

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
  simp only [returnCoefficientError, LinearMap.coe_prod, Function.prod_apply,
    LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]

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
