import ContinuousFlexibility.Radial.InnerBorderTransport
import ContinuousFlexibility.Radial.InnerLiouvillePhysicalOperators
import ContinuousFlexibility.Radial.InnerModelCoefficientEnvelope
import ContinuousFlexibility.Radial.InnerMorseBufferCoefficients
import ContinuousFlexibility.Radial.InnerCoefficientCosts

/-!
# The actual local Dirichlet cost in the physical Hilbert space

The ordinary product realization of a model inverse is transported back
to the same Hilbert source used for the finite-chain adjoint. Its norm
has a fixed fourth power of the raw model coefficient. For the realized
Morse cells this is the fixed exponent thirty-six, before any weight
exponent or starting index is chosen. The cell-weight comparisons add
one power, giving the fixed localized loss thirty-seven.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {α : Type*} [MeasurableSpace α]

def innerBorderFromMaxOperator (μ : Measure α)
    (A : (Lp ℝ 2 μ × ℝ) →L[ℝ] (Lp ℝ 2 μ × ℝ)) :
    InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ :=
  ((innerBorderMaxEquiv μ).symm : (Lp ℝ 2 μ × ℝ) →L[ℝ] InnerBorderL2 μ) ∘L A ∘L
    (innerBorderMaxEquiv μ : InnerBorderL2 μ →L[ℝ] (Lp ℝ 2 μ × ℝ))

theorem innerBorderFromMaxOperator_apply (μ : Measure α)
    (A : (Lp ℝ 2 μ × ℝ) →L[ℝ] (Lp ℝ 2 μ × ℝ)) (F : InnerBorderL2 μ) :
    innerBorderFromMaxOperator μ A F = WithLp.toLp 2 (A (WithLp.ofLp F)) := by
  simp only [innerBorderFromMaxOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, innerBorderMaxEquiv_apply,
    innerBorderMaxEquiv_symm_apply]

theorem innerBorderToMaxOperator_fromMax (μ : Measure α)
    (A : (Lp ℝ 2 μ × ℝ) →L[ℝ] (Lp ℝ 2 μ × ℝ)) :
    innerBorderToMaxOperator μ (innerBorderFromMaxOperator μ A) = A := by
  apply ContinuousLinearMap.ext
  intro F
  simp only [innerBorderToMaxOperator_apply, innerBorderFromMaxOperator_apply,
    WithLp.ofLp_toLp]

theorem norm_innerBorderFromMaxOperator_le (μ : Measure α)
    (A : (Lp ℝ 2 μ × ℝ) →L[ℝ] (Lp ℝ 2 μ × ℝ)) :
    ‖innerBorderFromMaxOperator μ A‖ ≤ sqrt 2 * ‖A‖ := by
  unfold innerBorderFromMaxOperator
  calc
    _ ≤ ‖((innerBorderMaxEquiv μ).symm : (Lp ℝ 2 μ × ℝ) →L[ℝ] InnerBorderL2 μ)‖ *
        (‖A‖ * ‖(innerBorderMaxEquiv μ : InnerBorderL2 μ →L[ℝ] (Lp ℝ 2 μ × ℝ))‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ sqrt 2 * (‖A‖ * 1) :=
      mul_le_mul (norm_innerBorderMaxEquiv_symm_le_sqrt_two μ)
        (mul_le_mul_of_nonneg_left (norm_innerBorderMaxEquiv_le_one μ) (norm_nonneg A))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (sqrt_nonneg 2)
    _ = sqrt 2 * ‖A‖ := by rw [mul_one]

section Physical

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)

/-- The same localized model inverse, expressed in the physical
Hilbert space without changing either coordinate. -/
def innerLiouvilleHilbertDirichlet
    (G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ)) :
    InnerBorderL2 (radialHilbertMeasure D) →L[ℝ]
      InnerBorderL2 (radialHilbertMeasure D) :=
  innerBorderFromMaxOperator (radialHilbertMeasure D)
    (innerLiouvillePhysicalDirichlet D hab hlam hR hs hp hcore hw U hU hv G)

theorem innerLiouvilleHilbertDirichlet_apply
    (G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    (F : InnerBorderL2 (radialHilbertMeasure D)) :
    innerLiouvilleHilbertDirichlet D hab hlam hR hs hp hcore hw U hU hv G F =
      WithLp.toLp 2
        (innerLiouvillePhysicalDirichlet D hab hlam hR hs hp hcore hw U hU hv G
          (WithLp.ofLp F)) :=
  innerBorderFromMaxOperator_apply _ _ _

theorem innerLiouvilleHilbertDirichlet_coefficient_cost {B : BufferData} {C K coeff : ℝ}
    (M : InnerBufferLocalizedData B C K) (hB : BufferHypotheses B)
    (hC : 0 ≤ C) (hc : 1 ≤ coeff) (hB0 : B.B₀ ≤ coeff)
    (hmass : ∀ i, (B.mass i)⁻¹ ≤ coeff) (hUc : U ≤ coeff) :
    ‖innerLiouvilleHilbertDirichlet D hab hlam hR hs hp hcore hw U hU hv M.dirichlet‖ ≤
      (sqrt 2 * (sqrt 12 + 1) ^ 2 * (1 + 2 * C)) * coeff ^ 4 := by
  have hc0 : 0 ≤ coeff := zero_le_one.trans hc
  have hmax : max (sqrt 12 * U) 1 ≤ (sqrt 12 + 1) * coeff := by
    apply max_le
    · have h := mul_le_mul_of_nonneg_left hUc (sqrt_nonneg 12)
      nlinarith only [h, hc0]
    · have h := mul_nonneg (sqrt_nonneg 12) hc0
      nlinarith only [h, hc]
  have hmax0 : 0 ≤ max (sqrt 12 * U) 1 :=
    zero_le_one.trans (le_max_right _ _)
  have hdir := M.dirichlet_bound.trans
    (innerBuffer_dirichlet_envelope_le hB hC hc hB0 hmass)
  have hphysical := norm_innerLiouvillePhysicalDirichlet_le
    D hab hlam hR hs hp hcore hw U hU hv M.dirichlet
  calc
    _ ≤ sqrt 2 * ‖innerLiouvillePhysicalDirichlet
        D hab hlam hR hs hp hcore hw U hU hv M.dirichlet‖ :=
      norm_innerBorderFromMaxOperator_le _ _
    _ ≤ sqrt 2 * ((max (sqrt 12 * U) 1) ^ 2 * ‖M.dirichlet‖) :=
      mul_le_mul_of_nonneg_left hphysical (sqrt_nonneg 2)
    _ ≤ sqrt 2 * (((sqrt 12 + 1) * coeff) ^ 2 * ((1 + 2 * C) * coeff ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul ((sq_le_sq₀ hmax0 (by positivity)).mpr hmax) hdir
          (norm_nonneg _) (sq_nonneg _)) (sqrt_nonneg 2)
    _ = _ := by ring

end Physical

def innerMorseDirichletConstant (C : ℝ) : ℝ :=
  (sqrt 2 * (sqrt 12 + 1) ^ 2 * (1 + 2 * C)) * (16 * (3 : ℝ) ^ 9) ^ 4

theorem innerMorseDirichletConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ innerMorseDirichletConstant C := by
  unfold innerMorseDirichletConstant
  positivity

/-- The exponent is fixed independently of the prescribed weights,
the first retained cell, and the frequency. -/
theorem innerMorseHilbertDirichlet_cost (D : ReferenceData) (T : MorseChainData)
    (m : ℕ) (hd : T.d m = morseChainInteger m) {j C K : ℝ}
    (hj : 1 ≤ j) (hC : 0 ≤ C)
    (hB : BufferHypotheses (innerMorseBufferData (morseChainA T m) (morseChainB T m)
      j (8 * (T.d m : ℝ) ^ 9)))
    (M : InnerBufferLocalizedData
      (innerMorseBufferData (morseChainA T m) (morseChainB T m)
        j (8 * (T.d m : ℝ) ^ 9)) C K)
    {R s : ℝ → ℝ} {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
    (hcore : Ioo (R a) (R b) ⊆ radialCore D)
    (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)
    (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ 14) :
    ‖innerLiouvilleHilbertDirichlet D hab hlam hR hs hp hcore hw
      14 (by norm_num) hv M.dirichlet‖ ≤
        innerMorseDirichletConstant C * radialE m ^ (36 : ℝ) := by
  have hdNat : 2 ≤ T.d m := by rw [hd]; exact morseChainInteger_ge_two m
  have hd' : (2 : ℝ) ≤ T.d m := by exact_mod_cast hdNat
  have hc := innerMorseChain_buffer_coefficient_bounds T m hd' hj
  have hUc : 14 ≤ innerMorseBufferCoefficient T m :=
    (by norm_num : (14 : ℝ) ≤ 16).trans
      (innerMorseBufferCoefficient_ge T m ((by norm_num : (1 : ℝ) ≤ 2).trans hd'))
  have hlocal := innerLiouvilleHilbertDirichlet_coefficient_cost
    D hab hlam hR hs hp hcore hw 14 (by norm_num) hv M hB hC
      hc.1 hc.2.1 hc.2.2.2.1 hUc
  have hpower : innerMorseBufferCoefficient T m ^ 4 ≤
      (16 * (3 : ℝ) ^ 9) ^ 4 * radialE m ^ (36 : ℝ) := by
    have h := pow_le_pow_left₀ (zero_le_one.trans hc.1)
      (innerMorseBufferCoefficient_le_weight T m hd) 4
    rw [rpow_ofNat, mul_pow, ← pow_mul] at h
    simpa only [rpow_ofNat, Nat.reduceMul] using h
  apply hlocal.trans
  have h := mul_le_mul_of_nonneg_left hpower
    (show 0 ≤ sqrt 2 * (sqrt 12 + 1) ^ 2 * (1 + 2 * C) by positivity)
  simpa only [innerMorseDirichletConstant, mul_assoc] using h

/-- The actual reciprocal cell-weight comparisons add one fixed power
to the local physical inverse cost. -/
theorem innerMorseDirichlet_fixed_loss {C ratio g : ℝ} {N m : ℕ}
    (hC : 0 ≤ C) (hr : 0 ≤ ratio) (hg : 0 ≤ g)
    (hrE : ratio ≤ sqrt (radialE m))
    (hgE : g ≤ innerMorseDirichletConstant C * radialE m ^ (36 : ℝ))
    (hm : N ≤ m) :
    innerCoefficientLoss N 37 m * (ratio ^ 2 * g) ≤
      innerMorseDirichletConstant C * radialE N ^ (37 : ℝ) := by
  simpa only [show (36 : ℝ) + 1 = 37 by norm_num] using
    inner_dirichlet_fixed_loss_cost (innerMorseDirichletConstant_nonneg hC)
      hr hg hrE hgE hm (by norm_num : (36 : ℝ) + 1 ≤ 37)

end ContinuousFlexibility.Radial
