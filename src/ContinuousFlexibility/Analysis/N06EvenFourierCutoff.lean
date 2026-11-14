module

public import ContinuousFlexibility.Analysis.N06CylinderFourierCutoff
public import ContinuousFlexibility.Analysis.CylinderTestPairing
public import ContinuousFlexibility.Radial.ReferenceCosineProjection
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# The actual even Fourier cutoff in the normalized cosine basis

Almost-everywhere reflection on the original half-period interval makes
the original Fourier coefficients real. Pairing the positive and negative
frequencies then identifies the same finite polynomial with the normalized
mean/cosine synthesis, including all actual angular derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology ComplexConjugate
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

theorem n06_circleFourierWave_reflection (n : ℤ) (θ : ℝ) :
    circleFourierWave n (Real.pi - θ) = conj (circleFourierWave n θ) := by
  simp only [circleFourierWave]
  rw [AddCircle.coe_sub, AddCircle.coe_period,
    zero_sub, fourier_apply, smul_neg, fourier_neg']

theorem n06_circleFourierWave_re (n : ℤ) (θ : ℝ) :
    (circleFourierWave n θ).re = Real.cos (2 * (n : ℝ) * θ) := by
  rw [circleFourierWave, fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * n * θ / Real.pi =
        ((2 * (n : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    <;> ring
  rw [harg, Complex.exp_ofReal_mul_I_re]

/-- Reflection is only required almost everywhere in the original measure. -/
theorem n06_circleFourierCoeff_conj_of_reflection {f : ℝ → ℝ}
    (hf : (fun θ => f (Real.pi - θ)) =ᵐ[angleMeasure] f) (n : ℤ) :
    conj (circleFourierCoeff f n) = circleFourierCoeff f n := by
  let g : ℝ → ℂ := fun θ => circleFourierWave (-n) θ * (f θ : ℂ)
  have hg : (fun θ => g (Real.pi - θ)) =ᵐ[angleMeasure] (fun θ => conj (g θ)) := by
    filter_upwards [hf] with θ hθ
    simp only [g, hθ, n06_circleFourierWave_reflection, map_mul, Complex.conj_ofReal]
  have hi : conj (∫ θ, g θ ∂angleMeasure) = ∫ θ, g θ ∂angleMeasure := by
    rw [← integral_conj]
    exact (integral_congr_ae hg.symm).trans
      (measurePreserving_angleReflection.integral_comp
        (measurableEmbedding_subLeft Real.pi) g)
  rw [circleFourierCoeff_integral, map_mul, map_inv₀, Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => (Real.pi : ℂ)⁻¹ * z) hi

theorem n06_circleFourierCoeff_im_eq_zero_of_reflection {f : ℝ → ℝ}
    (hf : (fun θ => f (Real.pi - θ)) =ᵐ[angleMeasure] f) (n : ℤ) :
    (circleFourierCoeff f n).im = 0 := by
  have h := congrArg Complex.im (n06_circleFourierCoeff_conj_of_reflection hf n)
  simp only [Complex.conj_im] at h
  linarith

theorem n06_circleFourierCoeff_re_eq_cosine {f : ℝ → ℝ}
    (hf : MemLp f 2 angleMeasure) (n : ℤ) :
    (circleFourierCoeff f n).re = Real.pi⁻¹ *
      ∫ θ, f θ * Real.cos (2 * (n : ℝ) * θ) ∂angleMeasure := by
  rw [(n06_circleFourierCoeff_parts hf n).1]
  congr 1
  apply integral_congr_ae
  filter_upwards with θ
  simp only [n06_circleFourierWave_re, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg]

theorem n06_halfCosineIntegral_zero {f : ℝ → ℝ} (hf : MemLp f 2 angleMeasure) :
    (Real.pi⁻¹ * ∫ θ, f θ * referenceAngularBasis 0 θ ∂angleMeasure) =
      (circleFourierCoeff f 0).re := by
  rw [n06_circleFourierCoeff_re_eq_cosine hf]
  simp only [referenceAngularBasis, Int.cast_zero, mul_zero, zero_mul, Real.cos_zero]

theorem n06_halfCosineIntegral_succ {f : ℝ → ℝ}
    (hf : MemLp f 2 angleMeasure) (n : ℕ) :
    (Real.pi⁻¹ * ∫ θ, f θ * referenceAngularBasis (n + 1) θ ∂angleMeasure) =
      Real.sqrt 2 * (circleFourierCoeff f ((n + 1 : ℕ) : ℤ)).re := by
  rw [n06_circleFourierCoeff_re_eq_cosine hf]
  simp only [referenceAngularBasis, cosineMode, Nat.cast_mul, Nat.cast_ofNat,
    Int.cast_natCast]
  have heq : (fun θ : ℝ => f θ *
      (Real.sqrt 2 * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ))) =
      fun θ => Real.sqrt 2 * (f θ * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ)) := by
    funext θ
    ring
  rw [heq, integral_const_mul]
  ring

/-- The centered integer cutoff pairs every strictly positive frequency
with its negative, leaving the mean exactly once. -/
theorem n06_sum_fourierCutoff (f : ℤ → ℝ) (N : ℕ) :
    (∑ n ∈ n06FourierCutoff N, f n) = f 0 +
      ∑ k ∈ Finset.range N,
        (f ((k + 1 : ℕ) : ℤ) + f (-((k + 1 : ℕ) : ℤ))) := by
  induction N with
  | zero => simp [n06FourierCutoff]
  | succ N ih =>
    have hset : n06FourierCutoff (N + 1) =
        insert (-((N + 1 : ℕ) : ℤ))
          (insert ((N + 1 : ℕ) : ℤ) (n06FourierCutoff N)) := by
      ext n
      simp only [n06FourierCutoff, Finset.mem_Icc, Finset.mem_insert]
      omega
    have hp : ((N + 1 : ℕ) : ℤ) ∉ n06FourierCutoff N := by
      simp only [n06FourierCutoff, Finset.mem_Icc]
      omega
    have hn : -((N + 1 : ℕ) : ℤ) ∉
        insert ((N + 1 : ℕ) : ℤ) (n06FourierCutoff N) := by
      simp only [Finset.mem_insert, n06FourierCutoff, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert hn, Finset.sum_insert hp, ih, Finset.sum_range_succ]
    ring

/-- The same polynomial is synthesized from the actual normalized
half-period cosine coefficients of the original representative. -/
theorem n06CircleFourierCut_eq_halfCosineSum {f : ℝ → ℝ}
    (hf : MemLp f 2 angleMeasure)
    (he : (fun θ => f (Real.pi - θ)) =ᵐ[angleMeasure] f) (N : ℕ) (θ : ℝ) :
    n06CircleFourierCut (n06FourierCutoff N) f θ =
      ∑ i ∈ Finset.range (N + 1),
        (Real.pi⁻¹ * ∫ η, f η * referenceAngularBasis i η ∂angleMeasure) *
          referenceAngularBasis i θ := by
  have hreal (n : ℤ) : (circleFourierCoeff f n * circleFourierWave n θ).re =
      (circleFourierCoeff f n).re * Real.cos (2 * (n : ℝ) * θ) := by
    rw [Complex.mul_re, n06_circleFourierCoeff_im_eq_zero_of_reflection he n,
      zero_mul, sub_zero, n06_circleFourierWave_re]
  have hzero : (circleFourierCoeff f 0 * circleFourierWave 0 θ).re =
      (Real.pi⁻¹ * ∫ η, f η * referenceAngularBasis 0 η ∂angleMeasure) *
        referenceAngularBasis 0 θ := by
    rw [hreal, n06_halfCosineIntegral_zero hf]
    simp only [Int.cast_zero, mul_zero, zero_mul, Real.cos_zero,
      referenceAngularBasis, mul_one]
  have hpair (i : ℕ) :
      (circleFourierCoeff f ((i + 1 : ℕ) : ℤ) *
        circleFourierWave ((i + 1 : ℕ) : ℤ) θ).re +
      (circleFourierCoeff f (-((i + 1 : ℕ) : ℤ)) *
        circleFourierWave (-((i + 1 : ℕ) : ℤ)) θ).re =
      (Real.pi⁻¹ * ∫ η, f η * referenceAngularBasis (i + 1) η ∂angleMeasure) *
        referenceAngularBasis (i + 1) θ := by
    rw [hreal, hreal, circleFourierCoeff_neg, n06_halfCosineIntegral_succ hf]
    simp only [Complex.conj_re, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg,
      referenceAngularBasis, cosineMode, Nat.cast_mul, Nat.cast_ofNat, Int.cast_natCast]
    have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hprod (a b : ℝ) : (Real.sqrt 2 * a) * (Real.sqrt 2 * b) = a * b + a * b := by
      calc
        _ = (Real.sqrt 2) ^ 2 * (a * b) := by ring
        _ = _ := by rw [hs]; ring
    exact (hprod _ _).symm
  simp only [n06CircleFourierCut, circleFourierPolynomial, Complex.re_sum]
  rw [n06_sum_fourierCutoff, hzero]
  simp_rw [hpair]
  rw [Finset.sum_range_succ']
  exact add_comm _ _

theorem n06CircleFourierCut_jet_eq_halfCosineSum {f : ℝ → ℝ}
    (hf : MemLp f 2 angleMeasure)
    (he : (fun θ => f (Real.pi - θ)) =ᵐ[angleMeasure] f)
    (N j : ℕ) (θ : ℝ) :
    iteratedDeriv j (n06CircleFourierCut (n06FourierCutoff N) f) θ =
      ∑ i ∈ Finset.range (N + 1),
        (Real.pi⁻¹ * ∫ η, f η * referenceAngularBasis i η ∂angleMeasure) *
          iteratedDeriv j (referenceAngularBasis i) θ := by
  have hfun : n06CircleFourierCut (n06FourierCutoff N) f =
      fun θ => ∑ i ∈ Finset.range (N + 1),
        (Real.pi⁻¹ * ∫ η, f η * referenceAngularBasis i η ∂angleMeasure) *
          referenceAngularBasis i θ :=
    funext (n06CircleFourierCut_eq_halfCosineSum hf he N)
  rw [hfun, iteratedDeriv_fun_sum
    (f := fun i θ =>
      (Real.pi⁻¹ * ∫ η, f η * referenceAngularBasis i η ∂angleMeasure) *
        referenceAngularBasis i θ)
    (fun i _ => ((contDiff_const (c := Real.pi⁻¹ *
      ∫ η, f η * referenceAngularBasis i η ∂angleMeasure)).mul
        (contDiff_referenceAngularBasis i)).contDiffAt.of_le (by simp))]
  simp only [iteratedDeriv_const_mul_field]

end ContinuousFlexibility.Statements
