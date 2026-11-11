import ContinuousFlexibility.Analysis.N07aAngularRadialPairing
import ContinuousFlexibility.Analysis.N07aWeakDivergenceEquation

/-!
# Local first normal regularity from the actual rough second-order equation

The equation `v_rr = h_r + g` is tested against a compact cutoff times
ordinary Fourier waves. Every term is an actual prescribed L² class.
The radial multiplier then produces a genuine first weak derivative of
`χ v`, including at any interior seam of the original physical atlas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology ComplexConjugate

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- An actual second-order distribution identity; no first radial jet is
part of this hypothesis. -/
def N07aCanonicalSecondPrimitiveEquation (v h g : CanonicalL2 S K m) : Prop :=
  ∀ φ, CanonicalTest S K m φ →
    (∫ p, v p * mixedDerivative 2 0 φ p ∂canonicalMeasure S K m) =
      -(∫ p, h p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m) +
        ∫ p, g p * φ p ∂canonicalMeasure S K m

theorem n07a_smoothCanonical_memLp {ψ : PolarPoint → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    MemLp ψ 2 (canonicalMeasure S K m) := by
  let := n07a_canonicalMeasure_finite S K m
  obtain ⟨A, hA⟩ := n07a_smoothCanonical_bounded (S := S) (K := K) (m := m) ψ hψ
  apply MemLp.of_bound hψ.continuous.aestronglyMeasurable A
  simpa only [Real.norm_eq_abs] using hA

private theorem n07a_mixedDerivative_second_radial_mul {χ ψ : PolarPoint → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ) (p : PolarPoint) :
    mixedDerivative 2 0 (fun q => χ q * ψ q) p =
      mixedDerivative 2 0 χ p * ψ p +
        2 * mixedDerivative 1 0 χ p * mixedDerivative 1 0 ψ p +
          χ p * mixedDerivative 2 0 ψ p := by
  rw [spaces_mixedDerivative_mul hχ hψ]
  norm_num [Finset.sum_range_succ, spaces_mixedDerivative_zero]
  ring

/-- Localizing the actual equation permits every smooth periodic test,
since its product with the cutoff is an admissible compact test. -/
theorem n07a_secondPrimitive_localize {χ : PolarPoint → ℝ}
    (hχ : CanonicalTest S K m χ) {v h g : CanonicalL2 S K m}
    (heq : N07aCanonicalSecondPrimitiveEquation v h g) :
    let M : CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m := n07aSmoothCanonicalMul χ hχ.1;
    let Mr : CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m := n07aSmoothCanonicalMul (mixedDerivative 1 0 χ)
      (contDiff_mixedDerivative hχ.1 1 0);
    let Mrr : CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m := n07aSmoothCanonicalMul (mixedDerivative 2 0 χ)
      (contDiff_mixedDerivative hχ.1 2 0);
    ∀ ψ, ContDiff ℝ ∞ ψ → Function.Periodic ψ (0, Real.pi) →
      (∫ p, M v p * mixedDerivative 2 0 ψ p ∂canonicalMeasure S K m) =
        -(∫ p, (M h + (2 : ℝ) • Mr v) p * mixedDerivative 1 0 ψ p
          ∂canonicalMeasure S K m) +
          ∫ p, (M g - Mr h - Mrr v) p * ψ p ∂canonicalMeasure S K m := by
  dsimp only
  let M : CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m := n07aSmoothCanonicalMul χ hχ.1
  let Mr : CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m := n07aSmoothCanonicalMul (mixedDerivative 1 0 χ)
    (contDiff_mixedDerivative hχ.1 1 0)
  let Mrr : CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m := n07aSmoothCanonicalMul (mixedDerivative 2 0 χ)
    (contDiff_mixedDerivative hχ.1 2 0)
  intro ψ hψ hψp
  let I (k : ℕ) : CanonicalL2 S K m →L[ℝ] ℝ :=
    n07aCanonicalTestPairing (mixedDerivative k 0 ψ)
      (n07a_smoothCanonical_memLp (contDiff_mixedDerivative hψ k 0))
  have hI (k : ℕ) (u : CanonicalL2 S K m) : I k u =
      ∫ p, u p * mixedDerivative k 0 ψ p ∂canonicalMeasure S K m :=
    n07aCanonicalTestPairing_apply _ _ u
  have hI0 (u : CanonicalL2 S K m) : I 0 u =
      ∫ p, u p * ψ p ∂canonicalMeasure S K m := by
    rw [hI, spaces_mixedDerivative_zero]
  have hi (k : ℕ) (u : CanonicalL2 S K m) :
      Integrable (fun p => u p * mixedDerivative k 0 ψ p) (canonicalMeasure S K m) :=
    (Lp.memLp u).integrable_mul
      (n07a_smoothCanonical_memLp (contDiff_mixedDerivative hψ k 0))
  have htest : CanonicalTest S K m (fun p => χ p * ψ p) := by
    simpa only [mul_comm] using n07a_canonicalTest_mul hχ hψ hψp
  have hleft : (∫ p, v p * mixedDerivative 2 0 (fun q => χ q * ψ q) p
      ∂canonicalMeasure S K m) = I 0 (Mrr v) + 2 * I 1 (Mr v) + I 2 (M v) := by
    simp only [hI]
    have houter := integral_add ((hi 0 (Mrr v)).add ((hi 1 (Mr v)).const_mul 2))
      (hi 2 (M v))
    simp only [Pi.add_apply] at houter
    rw [← integral_const_mul, ← integral_add (hi 0 (Mrr v)) ((hi 1 (Mr v)).const_mul 2),
      ← houter]
    apply integral_congr_ae
    filter_upwards [n07aSmoothCanonicalMul_ae χ hχ.1 v,
      n07aSmoothCanonicalMul_ae (mixedDerivative 1 0 χ) (contDiff_mixedDerivative hχ.1 1 0) v,
      n07aSmoothCanonicalMul_ae (mixedDerivative 2 0 χ) (contDiff_mixedDerivative hχ.1 2 0) v]
      with p hp hpr hprr
    rw [hp, hpr, hprr, n07a_mixedDerivative_second_radial_mul hχ.1 hψ,
      spaces_mixedDerivative_zero]
    ring
  have hright : (∫ p, h p * mixedDerivative 1 0 (fun q => χ q * ψ q) p
      ∂canonicalMeasure S K m) = I 0 (Mr h) + I 1 (M h) := by
    simp only [hI]
    rw [← integral_add (hi 0 (Mr h)) (hi 1 (M h))]
    apply integral_congr_ae
    filter_upwards [n07aSmoothCanonicalMul_ae χ hχ.1 h,
      n07aSmoothCanonicalMul_ae (mixedDerivative 1 0 χ) (contDiff_mixedDerivative hχ.1 1 0) h]
      with p hp hpr
    rw [hp, hpr, spaces_mixedDerivative_zero]
    have hd := congrFun (n07a_mixedDerivative_first_mul hχ.1 hψ (0 : Fin 2)) p
    simp only [n07aFirstOrder, Fin.isValue, ↓reduceIte] at hd
    rw [hd]
    ring
  have hsource : (∫ p, g p * (χ p * ψ p) ∂canonicalMeasure S K m) = I 0 (M g) := by
    rw [hI, spaces_mixedDerivative_zero]
    exact (n07aSmoothCanonicalMul_pairing χ hχ.1 g ψ).symm
  have ht := heq _ htest
  rw [hleft, hright, hsource] at ht
  rw [← hI 2 (M v), ← hI 1 (M h + (2 : ℝ) • Mr v),
    ← hI0 (M g - Mr h - Mrr v), map_add, map_smul, map_sub, map_sub]
  simp only [smul_eq_mul]
  linarith only [ht]

/-- A second-order identity tested against all smooth periodic functions
gives the exact full Fourier identity, including radial frequency zero. -/
theorem n07a_secondPrimitive_fourier (m : ℕ) (hm : K.left m < K.right m)
    (v h g : CanonicalL2 S K m)
    (heq : ∀ ψ, ContDiff ℝ ∞ ψ → Function.Periodic ψ (0, Real.pi) →
      (∫ p, v p * mixedDerivative 2 0 ψ p ∂canonicalMeasure S K m) =
        -(∫ p, h p * mixedDerivative 1 0 ψ p ∂canonicalMeasure S K m) +
          ∫ p, g p * ψ p ∂canonicalMeasure S K m) (j : SpacesTorusFrequency) :
    n07aRadialSymbol (n07aCanonicalRadialFrequency (K := K) m) j ^ 2 *
        n07aAngularFourier m hm v j =
      n07aRadialSymbol (n07aCanonicalRadialFrequency (K := K) m) j *
        n07aAngularFourier m hm h j + n07aAngularFourier m hm g j := by
  let z := n07aRadialSymbol (n07aCanonicalRadialFrequency (K := K) m) j
  let I (u : CanonicalL2 S K m) : ℂ :=
    ∫ p, n07aAngularCanonicalWave (K := K) m (-j) p * (u p : ℂ) ∂canonicalMeasure S K m
  have hz : n07aRadialSymbol (n07aCanonicalRadialFrequency (K := K) m) (-j) = -z := by
    simp only [n07aRadialSymbol, Pi.neg_apply, Int.cast_neg, z]
    ring
  have hreal (c : ℂ) : (c * (z ^ 2 * I v)).re = (c * (z * I h + I g)).re := by
    have hw : ContDiff ℝ ∞ (fun p =>
        (c * n07aAngularCanonicalWave (K := K) m (-j) p).re) :=
      Complex.reCLM.contDiff.comp
        (contDiff_const.mul (n07aAngularCanonicalWave_contDiff m (-j)))
    have ht := heq _ hw (n07aAngularCanonicalWave_real_periodic m (-j) c)
    simp only [n07aAngularCanonicalWave_real_radial, hz, pow_one, neg_sq] at ht
    simp_rw [n07aCanonicalWave_real_pairing] at ht
    dsimp only [I]
    simpa only [mul_neg, neg_mul, Complex.neg_re, neg_neg, mul_add, Complex.add_re,
      mul_assoc] using ht
  have hc : z ^ 2 * I v = z * I h + I g := by
    apply Complex.ext
    · simpa only [one_mul] using hreal 1
    · simpa only [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] using hreal (-Complex.I)
  rw [n07aAngularFourier_coefficient, n07aAngularFourier_coefficient,
    n07aAngularFourier_coefficient]
  let κ : ℂ := ((Real.sqrt (n07aAngularCellArea (K := K) m) *
    (n07aAngularCellArea (K := K) m)⁻¹ : ℝ) : ℂ)
  change z ^ 2 * (κ * I v) = z * (κ * I h) + κ * I g
  calc
    z ^ 2 * (κ * I v) = κ * (z ^ 2 * I v) := by ring
    _ = κ * (z * I h + I g) := congrArg (κ * ·) hc
    _ = _ := by ring

/-- A compact localization of a rough solution has a genuine first weak
normal derivative. No derivative or matching trace of the solution is assumed. -/
theorem n07a_secondPrimitive_exists_local_first (m : ℕ) (hm : K.left m < K.right m)
    {χ : PolarPoint → ℝ} (hχ : CanonicalTest S K m χ)
    {v h g : CanonicalL2 S K m} (heq : N07aCanonicalSecondPrimitiveEquation v h g) :
    ∃ d : CanonicalL2 S K m,
      N07aWeakCanonicalMixedDerivative S K m (n07aSmoothCanonicalMul χ hχ.1 v) d 1 0 := by
  let M : CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m := n07aSmoothCanonicalMul χ hχ.1
  let Mr : CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m := n07aSmoothCanonicalMul (mixedDerivative 1 0 χ)
    (contDiff_mixedDerivative hχ.1 1 0)
  let Mrr : CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m := n07aSmoothCanonicalMul (mixedDerivative 2 0 χ)
    (contDiff_mixedDerivative hχ.1 2 0)
  have hlocal := n07a_secondPrimitive_localize hχ heq
  obtain ⟨d, hd⟩ := n07a_exists_radialFirst_fourier m hm
    (n07aCanonicalRadialFrequency_pos m hm) (M v) (M h + (2 : ℝ) • Mr v)
    (M g - Mr h - Mrr v) (n07a_secondPrimitive_fourier m hm _ _ _ hlocal)
  exact ⟨d, n07aCanonicalWeakRadial_of_fourier m hm hd⟩

end ContinuousFlexibility.Analysis
