module

public import ContinuousFlexibility.Analysis.N07aAngularCoefficients
public import ContinuousFlexibility.Analysis.N07aAngularClassical

/-!
# Exact equivalence of the weak angular graph and its Fourier symbol

The reverse implication pairs arbitrary prescribed canonical tests using
the actual real `L²` Parseval identity. Their classical weak jets, already
proved by integration by parts, provide the dual Fourier symbol. Thus
the equivalence concerns every member of the frozen weak graph, not only
smooth source classes or formal Fourier sequences.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ComplexConjugate RealInnerProductSpace

theorem n07aAngularSymbol_inner (n : ℤ) (k : ℕ) (x y : ℂ) :
    inner ℝ ((2 * Complex.I * (n : ℂ)) ^ k * x) y =
      (-1 : ℝ) ^ k * inner ℝ x ((2 * Complex.I * (n : ℂ)) ^ k * y) := by
  have hconj : conj (2 * Complex.I * (n : ℂ)) = -(2 * Complex.I * (n : ℂ)) := by
    simp only [map_mul, map_ofNat, Complex.conj_I, map_intCast]
    ring
  have he : y * conj ((2 * Complex.I * (n : ℂ)) ^ k * x) =
      (((-1 : ℝ) ^ k : ℝ) : ℂ) *
        (((2 * Complex.I * (n : ℂ)) ^ k * y) * conj x) := by
    rw [map_mul, map_pow, hconj, neg_pow]
    push_cast
    ring
  rw [Complex.inner, Complex.inner, he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

variable {S : PhysicalSpacesData} {K : CanonicalData S}

/-- Fourier multiplication implies the original real weak derivative relation. -/
theorem n07aAngularWeak_of_fourier (m : ℕ) (hm : K.left m < K.right m)
    {f g : CanonicalL2 S K m} {k : ℕ}
    (hfg : ∀ j : SpacesTorusFrequency,
      n07aAngularFourier m hm g j =
        (2 * Complex.I * (j 1 : ℂ)) ^ k * n07aAngularFourier m hm f j) :
    WeakCanonicalAngularDerivative S K m f g k := by
  intro φ hφ
  let Φ : CanonicalL2 S K m := (n07a_canonicalTest_memLp hφ).toLp φ
  let Φk : CanonicalL2 S K m :=
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ 0 k)).toLp
      (mixedDerivative 0 k φ)
  have hΦk (j : SpacesTorusFrequency) :
      n07aAngularFourier m hm Φk j =
        (2 * Complex.I * (j 1 : ℂ)) ^ k * n07aAngularFourier m hm Φ j :=
    n07aAngularWeak_fourier m hm (n07a_canonicalTest_weakAngular hφ k) j
  have hpair : inner ℝ g Φ = (-1 : ℝ) ^ k * inner ℝ f Φk := by
    rw [← (n07aAngularFourier m hm).inner_map_map g Φ,
      ← (n07aAngularFourier m hm).inner_map_map f Φk,
      lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [hfg j, hΦk j]
    exact n07aAngularSymbol_inner (j 1) k _ _
  have hleft : (∫ p, g p * φ p ∂canonicalMeasure S K m) = inner ℝ g Φ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (n07a_canonicalTest_memLp hφ)] with p hp
    simp only [Φ, hp, RCLike.inner_apply, conj_trivial]
    ring
  have hright : (∫ p, f p * mixedDerivative 0 k φ p ∂canonicalMeasure S K m) =
      inner ℝ f Φk := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ 0 k))] with p hp
    simp only [Φk, hp, RCLike.inner_apply, conj_trivial]
    ring
  rw [hleft, hright]
  exact hpair

theorem n07aAngularWeak_fourier_iff (m : ℕ) (hm : K.left m < K.right m)
    (f g : CanonicalL2 S K m) (k : ℕ) :
    WeakCanonicalAngularDerivative S K m f g k ↔
      ∀ j : SpacesTorusFrequency, n07aAngularFourier m hm g j =
        (2 * Complex.I * (j 1 : ℂ)) ^ k * n07aAngularFourier m hm f j :=
  ⟨fun h j => n07aAngularWeak_fourier m hm h j, n07aAngularWeak_of_fourier m hm⟩

end ContinuousFlexibility.Analysis
