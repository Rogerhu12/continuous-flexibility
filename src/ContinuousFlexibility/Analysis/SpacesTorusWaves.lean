module

public import ContinuousFlexibility.Analysis.SpacesTorusFourier
public import ContinuousFlexibility.Analysis.SpacesCylinderIntegration

/-!
# Classical mixed jets of the physical Fourier waves

The radial period is six and the angular period is `π`. The actual mixed
derivatives have symbols `(π I k₁ / 3)^a (2 I k₂)^b`; taking real parts
commutes with all these derivatives. These are the concrete functions
used by Fourier synthesis, before multiplying by the radial envelopes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology ComplexConjugate

set_option backward.isDefEq.respectTransparency false

theorem spaces_iteratedDeriv_clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : ℝ → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t => L (f t)) x = L (iteratedDeriv n f x) := by
  have h := L.iteratedFDeriv_comp_left (x := x) hf.contDiffAt (i := n) (by simp)
  have he := congrArg (fun A : ℝ [×n]→L[ℝ] G => A (fun _ => 1)) h
  simpa only [iteratedDeriv_eq_iteratedFDeriv, Function.comp_def,
    ContinuousLinearMap.compContinuousMultilinearMap_coe] using he

/-- A unit-circle wave pulled back by an affine real coordinate. -/
def spacesUnitFourierAffine (j : ℤ) (a b x : ℝ) : ℂ :=
  fourier j ((a * x + b : ℝ) : UnitAddCircle)

def spacesUnitFourierSymbol (j : ℤ) (a : ℝ) : ℂ :=
  (a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))

theorem spacesUnitFourierAffine_contDiff (j : ℤ) (a b : ℝ) :
    ContDiff ℝ ∞ (spacesUnitFourierAffine j a b) := by
  unfold spacesUnitFourierAffine
  simp_rw [fourier_coe_apply]
  exact ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const))).div_const (1 : ℂ)).cexp

theorem spacesUnitFourierAffine_hasDerivAt (j : ℤ) (a b x : ℝ) :
    HasDerivAt (spacesUnitFourierAffine j a b)
      (spacesUnitFourierSymbol j a * spacesUnitFourierAffine j a b x) x := by
  have ha : HasDerivAt (fun t : ℝ => a * t + b) a x := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id x).const_mul a).add_const b)
  have h := (hasDerivAt_fourier (1 : ℝ) j (a * x + b)).scomp x ha
  convert h using 1
  · rfl
  · simp only [spacesUnitFourierSymbol, spacesUnitFourierAffine, Complex.ofReal_one,
      div_one, Complex.real_smul]
    ring

theorem spacesUnitFourierAffine_iteratedDeriv (j : ℤ) (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (spacesUnitFourierAffine j a b) =
      fun x => spacesUnitFourierSymbol j a ^ n * spacesUnitFourierAffine j a b x := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, (spacesUnitFourierAffine_hasDerivAt j a b x).deriv, pow_succ]
    ring

theorem spacesUnitFourierAffine_norm (j : ℤ) (a b x : ℝ) :
    ‖spacesUnitFourierAffine j a b x‖ = 1 := by
  simp only [spacesUnitFourierAffine, fourier_apply, Circle.norm_coe]

/-- The separated exponential wave on the actual material coordinate plane. -/
def spacesPhysicalFourierWave (n : ℤ) (j : SpacesTorusFrequency) (p : PolarPoint) : ℂ :=
  spacesUnitFourierAffine (j 0) (1 / 6) (-n / 6) p.1 *
    spacesUnitFourierAffine (j 1) (1 / Real.pi) 0 p.2

theorem spacesPhysicalFourierWave_contDiff (n : ℤ) (j : SpacesTorusFrequency) :
    ContDiff ℝ ∞ (spacesPhysicalFourierWave n j) :=
  ((spacesUnitFourierAffine_contDiff (j 0) (1 / 6) (-n / 6)).comp contDiff_fst).mul
    ((spacesUnitFourierAffine_contDiff (j 1) (1 / Real.pi) 0).comp contDiff_snd)

theorem spacesPhysicalFourierWave_norm (n : ℤ) (j : SpacesTorusFrequency) (p : PolarPoint) :
    ‖spacesPhysicalFourierWave n j p‖ = 1 := by
  simp only [spacesPhysicalFourierWave, norm_mul, spacesUnitFourierAffine_norm, one_mul]

/-- Real parts commute with the mixed derivatives of a separated smooth product. -/
theorem spaces_mixedDerivative_real_product {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (c : ℂ) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => (c * f q.1 * g q.2).re) p =
      (c * iteratedDeriv a f p.1 * iteratedDeriv b g p.2).re := by
  have hθ (r : ℝ) : iteratedDeriv b (fun θ => (c * f r * g θ).re) p.2 =
      (c * f r * iteratedDeriv b g p.2).re := by
    have h := spaces_iteratedDeriv_clm Complex.reCLM ((contDiff_const (c := c * f r)).mul hg) b p.2
    simpa only [Complex.reCLM_apply, iteratedDeriv_const_mul_field] using h
  unfold mixedDerivative
  simp_rw [hθ]
  have h := spaces_iteratedDeriv_clm Complex.reCLM
    (((contDiff_const (c := c)).mul hf).mul
      (contDiff_const (c := iteratedDeriv b g p.2))) a p.1
  simpa only [Complex.reCLM_apply, iteratedDeriv_mul_const_field,
    iteratedDeriv_const_mul_field] using h

/-- Exact mixed differentiation of each real physical Fourier mode. -/
theorem spacesPhysicalFourierWave_mixedDerivative (n : ℤ) (j : SpacesTorusFrequency)
    (c : ℂ) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => (c * spacesPhysicalFourierWave n j q).re) p =
      (c * spacesUnitFourierSymbol (j 0) (1 / 6) ^ a *
        spacesUnitFourierSymbol (j 1) (1 / Real.pi) ^ b * spacesPhysicalFourierWave n j p).re := by
  have he : (fun q => (c * spacesPhysicalFourierWave n j q).re) =
      fun q : PolarPoint => (c * spacesUnitFourierAffine (j 0) (1 / 6) (-n / 6) q.1 *
        spacesUnitFourierAffine (j 1) (1 / Real.pi) 0 q.2).re := by
    funext q
    rw [spacesPhysicalFourierWave, mul_assoc]
  rw [he, spaces_mixedDerivative_real_product
    (spacesUnitFourierAffine_contDiff (j 0) (1 / 6) (-n / 6))
    (spacesUnitFourierAffine_contDiff (j 1) (1 / Real.pi) 0)]
  simp only [spacesUnitFourierAffine_iteratedDeriv, spacesPhysicalFourierWave]
  congr 1
  ring

theorem spacesUnitFourierSymbol_norm (j : ℤ) (a : ℝ) :
    ‖spacesUnitFourierSymbol j a‖ = |a| * (2 * Real.pi * |(j : ℝ)|) := by
  simp only [spacesUnitFourierSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_two, abs_of_pos Real.pi_pos, Complex.norm_I, Complex.norm_intCast, mul_one]

/-- A uniform polynomial frequency bound for every mixed mode. -/
theorem spacesPhysicalFourierWave_mixedDerivative_bound (n : ℤ) (j : SpacesTorusFrequency)
    (c : ℂ) (a b : ℕ) (p : PolarPoint) :
    |mixedDerivative a b (fun q => (c * spacesPhysicalFourierWave n j q).re) p| ≤
      ‖c‖ * (Real.pi / 3 * |(j 0 : ℝ)|) ^ a * (2 * |(j 1 : ℝ)|) ^ b := by
  rw [spacesPhysicalFourierWave_mixedDerivative]
  refine (Complex.abs_re_le_norm _).trans_eq ?_
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
    spacesPhysicalFourierWave_norm, mul_one, spacesUnitFourierSymbol_norm, spacesUnitFourierSymbol_norm]
  have hr : |(1 / 6 : ℝ)| * (2 * Real.pi * |(j 0 : ℝ)|) = Real.pi / 3 * |(j 0 : ℝ)| := by
    norm_num
    ring
  have hθ : |1 / Real.pi| * (2 * Real.pi * |(j 1 : ℝ)|) = 2 * |(j 1 : ℝ)| := by
    rw [abs_of_pos (one_div_pos.mpr Real.pi_pos)]
    field_simp [Real.pi_ne_zero]
  rw [hr, hθ]

end ContinuousFlexibility.Statements
