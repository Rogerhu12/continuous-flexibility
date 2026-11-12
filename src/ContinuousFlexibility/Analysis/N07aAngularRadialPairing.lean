import ContinuousFlexibility.Analysis.N07aAngularRadialSymbol
import ContinuousFlexibility.Analysis.N07aAngularCoefficients
import ContinuousFlexibility.Analysis.N07aAngularClassical

/-!
# True weak radial derivatives from the full canonical Fourier transform

Only the test function is smooth. Its compact radial support removes the
boundary term when computing its radial Fourier coefficient. Parseval
then identifies Fourier multiplication with the original weak equation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology ComplexConjugate RealInnerProductSpace

variable {S : PhysicalSpacesData} {K : CanonicalData S}

def n07aCanonicalRadialFrequency (m : ℕ) : ℝ :=
  2 * Real.pi / (K.right m - K.left m)

theorem n07aCanonicalRadialFrequency_pos (m : ℕ) (hm : K.left m < K.right m) :
    0 < n07aCanonicalRadialFrequency (K := K) m :=
  div_pos (mul_pos (by norm_num) Real.pi_pos) (sub_pos.mpr hm)

theorem n07aCanonicalRadialSymbol_eq (m : ℕ) (j : SpacesTorusFrequency) :
    n07aRadialSymbol (n07aCanonicalRadialFrequency (K := K) m) j =
      spacesUnitFourierSymbol (j 0) (1 / (K.right m - K.left m)) := by
  unfold n07aRadialSymbol n07aCanonicalRadialFrequency spacesUnitFourierSymbol
  push_cast
  ring

theorem n07aAngularCanonicalWave_real_periodic (m : ℕ) (j : SpacesTorusFrequency)
    (c : ℂ) : Function.Periodic
      (fun p => (c * n07aAngularCanonicalWave (K := K) m j p).re) (0, Real.pi) := by
  intro p
  simp only [n07aAngularCanonicalWave_separated, n07aAngularWave,
    Prod.fst_add, Prod.snd_add, add_zero, circleFourierWave_periodic (j 1) p.2]

theorem n07aAngularCanonicalWave_real_radial (m : ℕ) (j : SpacesTorusFrequency)
    (c : ℂ) (a : ℕ) (p : PolarPoint) :
    mixedDerivative a 0 (fun q => (c * n07aAngularCanonicalWave (K := K) m j q).re) p =
      (c * n07aRadialSymbol (n07aCanonicalRadialFrequency (K := K) m) j ^ a *
        n07aAngularCanonicalWave (K := K) m j p).re := by
  have he : (fun q => (c * n07aAngularCanonicalWave (K := K) m j q).re) =
      (fun q : PolarPoint => (c *
        spacesUnitFourierAffine (j 0) (1 / (K.right m - K.left m))
          (-K.left m / (K.right m - K.left m)) q.1 * circleFourierWave (j 1) q.2).re) := by
    funext q
    rw [n07aAngularCanonicalWave_separated, n07aAngularWave, mul_assoc]
  rw [he, spaces_mixedDerivative_real_product
    (spacesUnitFourierAffine_contDiff _ _ _) (circleFourierWave_contDiff _) c a 0 p,
    spacesUnitFourierAffine_iteratedDeriv, iteratedDeriv_zero,
    n07aCanonicalRadialSymbol_eq, n07aAngularCanonicalWave_separated, n07aAngularWave]
  congr 1
  ring

/-- Pairing a canonical class with the real part of a complex wave. -/
theorem n07aCanonicalWave_real_pairing (m : ℕ) (j : SpacesTorusFrequency)
    (c : ℂ) (u : CanonicalL2 S K m) :
    (∫ p, u p * (c * n07aAngularCanonicalWave (K := K) m j p).re
      ∂canonicalMeasure S K m) =
      (c * ∫ p, n07aAngularCanonicalWave (K := K) m j p * (u p : ℂ)
        ∂canonicalMeasure S K m).re := by
  have hi : Integrable (fun p => n07aAngularCanonicalWave (K := K) m j p * (u p : ℂ))
      (canonicalMeasure S K m) := memLp_one_iff_integrable.mp
    ((n07aCanonicalContinuous_memLp m (n07aAngularCanonicalWave_contDiff m j).continuous).mul
      (Lp.memLp u).ofReal)
  have hr := integral_re (hi.const_mul c)
  change (∫ p, (c * (n07aAngularCanonicalWave (K := K) m j p * (u p : ℂ))).re
      ∂canonicalMeasure S K m) =
    (∫ p, c * (n07aAngularCanonicalWave (K := K) m j p * (u p : ℂ))
      ∂canonicalMeasure S K m).re at hr
  rw [integral_const_mul] at hr
  simpa only [← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, mul_comm] using hr

/-- The true derivative of a compact canonical test has the radial symbol. -/
theorem n07aCanonicalTest_radial_fourier (m : ℕ) (hm : K.left m < K.right m)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (j : SpacesTorusFrequency) :
    n07aAngularFourier m hm
      ((n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ 1 0)).toLp
        (mixedDerivative 1 0 φ)) j =
      n07aRadialSymbol (n07aCanonicalRadialFrequency (K := K) m) j *
        n07aAngularFourier m hm ((n07a_canonicalTest_memLp hφ).toLp φ) j := by
  let Φ : CanonicalL2 S K m := (n07a_canonicalTest_memLp hφ).toLp φ
  let Φr : CanonicalL2 S K m :=
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ 1 0)).toLp
      (mixedDerivative 1 0 φ)
  let z := n07aRadialSymbol (n07aCanonicalRadialFrequency (K := K) m) j
  let wave := n07aAngularCanonicalWave (K := K) m (-j)
  have hreal (c : ℂ) :
      (c * ∫ p, wave p * (Φr p : ℂ) ∂canonicalMeasure S K m).re =
        (c * z * ∫ p, wave p * (Φ p : ℂ) ∂canonicalMeasure S K m).re := by
    have hw : ContDiff ℝ ∞ (fun p => (c * wave p).re) :=
      Complex.reCLM.contDiff.comp
        (contDiff_const.mul (n07aAngularCanonicalWave_contDiff m (-j)))
    have hip := spaces_integral_mixedDerivative_mul hw
      (n07aAngularCanonicalWave_real_periodic m (-j) c)
      (n07a_canonicalTest_isCylinderTest hφ) 1 0
    have hleft : (∫ p, mixedDerivative 1 0 (fun q => (c * wave q).re) p * φ p
        ∂materialCylinderMeasure) =
        -(c * z * ∫ p, wave p * (Φ p : ℂ) ∂canonicalMeasure S K m).re := by
      rw [← n07a_canonicalIntegral_eq_cylinder (S := S) (K := K) (m := m)
        (fun p hp => by rw [n07a_canonicalTest_zero_outside hφ hp, mul_zero])]
      have he := n07aCanonicalWave_real_pairing m (-j) (-(c * z)) Φ
      have hc : n07aRadialSymbol (n07aCanonicalRadialFrequency (K := K) m) (-j) = -z := by
        simp only [n07aRadialSymbol, Pi.neg_apply, Int.cast_neg, z]
        ring
      dsimp only [wave]
      simp only [n07aAngularCanonicalWave_real_radial, pow_one, hc]
      have hi : (∫ p, (c * -z * wave p).re * φ p ∂canonicalMeasure S K m) =
          ∫ p, Φ p * (-(c * z) * wave p).re ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [(n07a_canonicalTest_memLp hφ).coeFn_toLp] with p hp
        dsimp only [Φ] at hp ⊢
        rw [hp]
        have heq : c * -z * wave p = -(c * z) * wave p := by ring
        rw [heq, mul_comm]
      rw [hi, he]
      simp only [neg_mul, Complex.neg_re]
    have hright : (∫ p, (c * wave p).re * mixedDerivative 1 0 φ p
        ∂materialCylinderMeasure) =
        (c * ∫ p, wave p * (Φr p : ℂ) ∂canonicalMeasure S K m).re := by
      rw [← n07a_canonicalIntegral_eq_cylinder (S := S) (K := K) (m := m)
        (fun p hp => by rw [n07a_canonicalTest_zero_outside
          (n07a_canonicalTest_mixedDerivative hφ 1 0) hp, mul_zero])]
      rw [← n07aCanonicalWave_real_pairing m (-j) c Φr]
      apply integral_congr_ae
      filter_upwards [(n07a_canonicalTest_memLp
        (n07a_canonicalTest_mixedDerivative hφ 1 0)).coeFn_toLp] with p hp
      dsimp only [Φr] at hp ⊢
      rw [hp]
      ring
    rw [hleft, hright] at hip
    simp only [Nat.add_zero, pow_one, neg_one_mul] at hip
    exact (neg_inj.mp hip).symm
  have hcomplex : (∫ p, wave p * (Φr p : ℂ) ∂canonicalMeasure S K m) =
      z * ∫ p, wave p * (Φ p : ℂ) ∂canonicalMeasure S K m := by
    apply Complex.ext
    · simpa only [one_mul] using hreal 1
    · simpa only [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg, mul_assoc]
        using hreal (-Complex.I)
  rw [n07aAngularFourier_coefficient, n07aAngularFourier_coefficient]
  change _ * (∫ p, wave p * (Φr p : ℂ) ∂canonicalMeasure S K m) =
    z * (_ * ∫ p, wave p * (Φ p : ℂ) ∂canonicalMeasure S K m)
  rw [hcomplex]
  ring

private theorem n07aRadialSymbol_inner (frequency : ℝ) (j : SpacesTorusFrequency) (x y : ℂ) :
    inner ℝ (n07aRadialSymbol frequency j * x) y = -inner ℝ x (n07aRadialSymbol frequency j * y) := by
  have hc : conj (n07aRadialSymbol frequency j) = -n07aRadialSymbol frequency j := by
    simp only [n07aRadialSymbol, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast]
    ring
  have he : y * conj (n07aRadialSymbol frequency j * x) =
      -((n07aRadialSymbol frequency j * y) * conj x) := by
    rw [map_mul, hc]
    ring
  rw [Complex.inner, Complex.inner, he, Complex.neg_re]

/-- Fourier multiplication gives the genuine first weak radial derivative. -/
theorem n07aCanonicalWeakRadial_of_fourier (m : ℕ) (hm : K.left m < K.right m)
    {u d : CanonicalL2 S K m}
    (hd : ∀ j, n07aAngularFourier m hm d j =
      n07aRadialSymbol (n07aCanonicalRadialFrequency (K := K) m) j *
        n07aAngularFourier m hm u j) :
    N07aWeakCanonicalMixedDerivative S K m u d 1 0 := by
  intro φ hφ
  let Φ : CanonicalL2 S K m := (n07a_canonicalTest_memLp hφ).toLp φ
  let Φr : CanonicalL2 S K m :=
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ 1 0)).toLp
      (mixedDerivative 1 0 φ)
  have hpair : inner ℝ d Φ = -inner ℝ u Φr := by
    rw [← (n07aAngularFourier m hm).inner_map_map d Φ,
      ← (n07aAngularFourier m hm).inner_map_map u Φr,
      lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_neg]
    apply tsum_congr
    intro j
    rw [hd j, n07aCanonicalTest_radial_fourier m hm hφ j]
    exact n07aRadialSymbol_inner _ _ _ _
  have hl : (∫ p, d p * φ p ∂canonicalMeasure S K m) = inner ℝ d Φ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(n07a_canonicalTest_memLp hφ).coeFn_toLp] with p hp
    simp only [Φ, hp, RCLike.inner_apply, conj_trivial]
    ring
  have hr : (∫ p, u p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m) =
      inner ℝ u Φr := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(n07a_canonicalTest_memLp
      (n07a_canonicalTest_mixedDerivative hφ 1 0)).coeFn_toLp] with p hp
    simp only [Φr, hp, RCLike.inner_apply, conj_trivial]
    ring
  simpa only [Nat.add_zero, pow_one, neg_one_mul, hl, hr] using hpair

end ContinuousFlexibility.Analysis
