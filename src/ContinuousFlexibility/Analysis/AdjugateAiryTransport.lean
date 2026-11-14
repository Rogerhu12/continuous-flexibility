import ContinuousFlexibility.Analysis.AdjugatePrincipalField
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.LinearCombination

/-!
# Actual characteristic first integrals of a forward Airy chart

For a positive-Jacobian forward chart, the two actual functions
η ± (2/3) ξ^(3/2) satisfy the physical characteristic equations of its
adjugate effective field. The square root of the physical discriminant
is derived from the determinant identity. No transport equation or flow
endpoint formula is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def airyTravelPrimitive (ξ : ℝ) : ℝ := (2 / 3 : ℝ) * ξ ^ (3 / 2 : ℝ)

def airyFirstIntegral (F : PolarPoint → PolarPoint) (σ : ℝ) (p : PolarPoint) : ℝ :=
  (F p).2 + σ * airyTravelPrimitive (F p).1

theorem hasDerivAt_airyTravelPrimitive {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt airyTravelPrimitive (Real.sqrt ξ) ξ := by
  have hd := ((hasDerivAt_id ξ).rpow_const
    (p := (3 / 2 : ℝ)) (Or.inl hξ.ne')).const_mul (2 / 3 : ℝ)
  simp only [id_eq] at hd
  apply hd.congr_deriv
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  ring

/-- Both partials are computed from the actual Frechet chain rule. -/
theorem airyFirstIntegral_partials
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (hξ : 0 < (F p).1) (σ : ℝ) :
    radialPartial (airyFirstIntegral F σ) p =
        (fderiv ℝ F p (1, 0)).2 +
          σ * Real.sqrt (F p).1 * (fderiv ℝ F p (1, 0)).1 ∧
      angularPartial (airyFirstIntegral F σ) p =
        (fderiv ℝ F p (0, 1)).2 +
          σ * Real.sqrt (F p).1 * (fderiv ℝ F p (0, 1)).1 := by
  have hs := (hasDerivAt_airyTravelPrimitive hξ).comp_hasFDerivAt p hF.hasFDerivAt.fst
  have hd := hF.hasFDerivAt.snd.fun_add (hs.const_mul σ)
  have he : (fun q : PolarPoint => (F q).2 + σ * (airyTravelPrimitive ∘ fun y => (F y).1) q) =
      airyFirstIntegral F σ := by
    funext q
    rfl
  rw [he] at hd
  simp only [radialPartial, angularPartial, hd.fderiv,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  constructor <;> ring

private theorem airy_adjugate_first_entries
    (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) (p : PolarPoint) :
    (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a p =
        (1 / (h p ^ 2 * |planeJacobian F p|)) *
          ((fderiv ℝ F p (0, 1)).2 ^ 2 -
            (F p).1 * (fderiv ℝ F p (0, 1)).1 ^ 2) ∧
      (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).b p =
        (1 / (h p ^ 2 * |planeJacobian F p|)) *
          (-(fderiv ℝ F p (1, 0)).2 * (fderiv ℝ F p (0, 1)).2 +
            (F p).1 * (fderiv ℝ F p (1, 0)).1 * (fderiv ℝ F p (0, 1)).1) := by
  dsimp only [adjugateCoordinatePrincipalCoefficients, canonicalAiryPrincipalCoefficients,
    coefficientQuadratic]
  constructor <;> ring

/-- The actual discriminant square root follows from the determinant;
it is not an independent speed coefficient. -/
theorem sqrt_discriminant_adjugateAiry
    (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) (p : PolarPoint)
    (hJ : planeJacobian F p ≠ 0) (hh : h p ≠ 0) (hξ : 0 ≤ (F p).1) :
    Real.sqrt
        ((adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).b p ^ 2 -
          (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a p *
            (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).c p) =
      Real.sqrt (F p).1 / h p ^ 2 := by
  let B := adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h
  have hd : B.a p * B.c p - B.b p ^ 2 = -(F p).1 / h p ^ 4 := by
    simpa only [B, canonicalAiryPrincipalCoefficients, one_mul,
      zero_pow two_ne_zero, sub_zero] using
        adjugateCoordinatePrincipalCoefficients_determinant
          canonicalAiryPrincipalCoefficients F h p hJ hh
  have hdisc : B.b p ^ 2 - B.a p * B.c p = (F p).1 / h p ^ 4 := by
    rw [neg_div] at hd
    linarith only [hd]
  have hdisc0 : 0 ≤ B.b p ^ 2 - B.a p * B.c p := by
    rw [hdisc]
    exact div_nonneg hξ (by positivity)
  change Real.sqrt (B.b p ^ 2 - B.a p * B.c p) = Real.sqrt (F p).1 / h p ^ 2
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
    (div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))).mp
  rw [Real.sq_sqrt hdisc0, div_pow, Real.sq_sqrt hξ, hdisc]
  rw [show (h p ^ 2) ^ 2 = h p ^ 4 by ring]

private theorem airy_transport_scalar
    {A B R k ar aθ br bt s : ℝ} (hA : A ≠ 0)
    (ha : A = k * (bt ^ 2 - s ^ 2 * aθ ^ 2))
    (hb : B = k * (-br * bt + s ^ 2 * ar * aθ))
    (hR : R = k * s * (ar * bt - br * aθ)) :
    br + s * ar + (B / A - R / A) * (bt + s * aθ) = 0 ∧
      br - s * ar + (B / A + R / A) * (bt - s * aθ) = 0 := by
  constructor <;> field_simp [hA] <;> rw [ha, hb, hR] <;> ring

/-- A forward Airy chart with positive Jacobian supplies the actual
physical first integrals for both characteristic speeds. The only radial
noncharacteristic assumption is the nonzero actual coefficient B.a. -/
theorem airyFirstIntegral_characteristic_transport
    {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (hJ : 0 < planeJacobian F p)
    (hh : h p ≠ 0) (hξ : 0 < (F p).1)
    (ha : (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a p ≠ 0) :
    radialPartial (airyFirstIntegral F 1) p =
        -minusCharacteristicSpeed
          (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h) p *
          angularPartial (airyFirstIntegral F 1) p ∧
      radialPartial (airyFirstIntegral F (-1)) p =
        -plusCharacteristicSpeed
          (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h) p *
          angularPartial (airyFirstIntegral F (-1)) p := by
  let B := adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h
  let k : ℝ := 1 / (h p ^ 2 * |planeJacobian F p|)
  let s : ℝ := Real.sqrt (F p).1
  have hs : s ^ 2 = (F p).1 := Real.sq_sqrt hξ.le
  have he := airy_adjugate_first_entries F h p
  have hBa : B.a p = k * ((fderiv ℝ F p (0, 1)).2 ^ 2 -
      s ^ 2 * (fderiv ℝ F p (0, 1)).1 ^ 2) := by
    rw [hs]
    exact he.1
  have hBb : B.b p = k * (-(fderiv ℝ F p (1, 0)).2 * (fderiv ℝ F p (0, 1)).2 +
      s ^ 2 * (fderiv ℝ F p (1, 0)).1 * (fderiv ℝ F p (0, 1)).1) := by
    rw [hs]
    exact he.2
  have hroot : Real.sqrt (B.b p ^ 2 - B.a p * B.c p) =
      k * s * ((fderiv ℝ F p (1, 0)).1 * (fderiv ℝ F p (0, 1)).2 -
        (fderiv ℝ F p (1, 0)).2 * (fderiv ℝ F p (0, 1)).1) := by
    rw [sqrt_discriminant_adjugateAiry F h p hJ.ne' hh hξ.le]
    change s / h p ^ 2 = k * s * planeJacobian F p
    dsimp only [k]
    rw [abs_of_pos hJ]
    field_simp [hh, hJ.ne']
    <;> ring
  have htransport := airy_transport_scalar ha hBa hBb hroot
  dsimp only [s] at htransport
  have hplus := airyFirstIntegral_partials hF hξ (1 : ℝ)
  have hminus := airyFirstIntegral_partials hF hξ (-1 : ℝ)
  constructor
  · rw [hplus.1, hplus.2]
    simp only [minusCharacteristicSpeed, one_mul]
    change _ = -(B.b p / B.a p - Real.sqrt (B.b p ^ 2 - B.a p * B.c p) / B.a p) * _
    linear_combination htransport.1
  · rw [hminus.1, hminus.2]
    simp only [plusCharacteristicSpeed, neg_one_mul]
    change _ = -(B.b p / B.a p + Real.sqrt (B.b p ^ 2 - B.a p * B.c p) / B.a p) * _
    linear_combination htransport.2

end ContinuousFlexibility.Analysis

