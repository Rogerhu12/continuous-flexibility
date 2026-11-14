module

public import ContinuousFlexibility.Analysis.N07aAngularRealFourier
public import ContinuousFlexibility.Analysis.N07aAngularWeakFourier
public import ContinuousFlexibility.Analysis.N07aAngularEven

/-!
# Actual angular-frequency projections on each canonical source piece

The bands retain every radial Fourier index. They are orthogonal
projections on the original real `L²` class, preserve the frozen weak
angular derivative and reflection conditions, and reconstruct the
original class in its actual norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ComplexConjugate RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

def n07aAngularFrequency (j : SpacesTorusFrequency) : ℕ := (j 1).natAbs

@[simp] theorem n07aAngularFrequency_neg (j : SpacesTorusFrequency) :
    n07aAngularFrequency (-j) = n07aAngularFrequency j := by
  simp only [n07aAngularFrequency, Pi.neg_apply, Int.natAbs_neg]

@[simp] theorem n07aAngularFrequency_reflection (j : SpacesTorusFrequency) :
    n07aAngularFrequency (n07aAngularFrequencyReflection j) = n07aAngularFrequency j := by
  simp only [n07aAngularFrequency, n07aAngularFrequencyReflection_one, Int.natAbs_neg]

variable {S : PhysicalSpacesData} {K : CanonicalData S}

def n07aAngularBand (m : ℕ) (hm : K.left m < K.right m) (n : ℕ) :
    CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m :=
  (n07aAngularFourierInverse m hm).comp
    ((lpSpectralBand n07aAngularFrequency n).comp (n07aAngularFourier m hm).toContinuousLinearMap)

@[simp] theorem n07aAngularBand_apply (m : ℕ) (hm : K.left m < K.right m) (n : ℕ)
    (u : CanonicalL2 S K m) :
    n07aAngularBand m hm n u = n07aAngularFourierInverse m hm
      (lpSpectralBand n07aAngularFrequency n (n07aAngularFourier m hm u)) := by
  simp only [n07aAngularBand, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap]

theorem n07aAngularBand_fourier (m : ℕ) (hm : K.left m < K.right m) (n : ℕ)
    (u : CanonicalL2 S K m) :
    n07aAngularFourier m hm (n07aAngularBand m hm n u) =
      lpSpectralBand n07aAngularFrequency n (n07aAngularFourier m hm u) := by
  rw [n07aAngularBand_apply]
  apply n07aAngularFourier_inverse
  intro j
  simp only [lpSpectralBand_apply, n07aAngularFrequency_neg, n07aAngularFourier_neg]
  split_ifs <;> simp only [map_zero]

theorem n07aAngularBand_coefficient (m : ℕ) (hm : K.left m < K.right m) (n : ℕ)
    (u : CanonicalL2 S K m) (j : SpacesTorusFrequency) :
    n07aAngularFourier m hm (n07aAngularBand m hm n u) j =
      if n07aAngularFrequency j = n then n07aAngularFourier m hm u j else 0 := by
  rw [n07aAngularBand_fourier, lpSpectralBand_apply]

theorem n07aAngularBand_norm_le (m : ℕ) (hm : K.left m < K.right m) (n : ℕ)
    (u : CanonicalL2 S K m) : ‖n07aAngularBand m hm n u‖ ≤ ‖u‖ := by
  rw [n07aAngularBand_apply]
  exact (n07aAngularFourierInverse_norm_le m hm _).trans
    ((lpSpectralBand_norm_le n07aAngularFrequency n _).trans_eq
      ((n07aAngularFourier m hm).norm_map u))

theorem n07aAngularBand_idempotent (m : ℕ) (hm : K.left m < K.right m) (n : ℕ)
    (u : CanonicalL2 S K m) :
    n07aAngularBand m hm n (n07aAngularBand m hm n u) = n07aAngularBand m hm n u := by
  apply (n07aAngularFourier m hm).injective
  apply lp.ext
  funext j
  simp only [n07aAngularBand_coefficient]
  split_ifs <;> rfl

theorem n07aAngularBand_comp_eq_zero (m : ℕ) (hm : K.left m < K.right m)
    {n l : ℕ} (hnl : n ≠ l) (u : CanonicalL2 S K m) :
    n07aAngularBand m hm n (n07aAngularBand m hm l u) = 0 := by
  apply (n07aAngularFourier m hm).injective
  apply lp.ext
  funext j
  simp only [n07aAngularBand_coefficient, map_zero, lp.coeFn_zero, Pi.zero_apply]
  split_ifs with hn hl
  · exact False.elim (hnl (hn.symm.trans hl))
  · rfl
  · rfl

theorem n07aAngularBand_symmetric (m : ℕ) (hm : K.left m < K.right m) (n : ℕ)
    (u v : CanonicalL2 S K m) :
    inner ℝ (n07aAngularBand m hm n u) v = inner ℝ u (n07aAngularBand m hm n v) := by
  rw [← (n07aAngularFourier m hm).inner_map_map,
    ← (n07aAngularFourier m hm).inner_map_map, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  simp only [n07aAngularBand_coefficient]
  split_ifs <;> simp only [inner_zero_left, inner_zero_right]

theorem n07aAngularBand_orthogonal (m : ℕ) (hm : K.left m < K.right m)
    {n l : ℕ} (hnl : n ≠ l) (u v : CanonicalL2 S K m) :
    inner ℝ (n07aAngularBand m hm n u) (n07aAngularBand m hm l v) = 0 := by
  rw [n07aAngularBand_symmetric, n07aAngularBand_comp_eq_zero m hm hnl,
    inner_zero_right]

theorem n07aAngularBand_hasSum (m : ℕ) (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) : HasSum (fun n => n07aAngularBand m hm n u) u := by
  have h := (hasSum_lpSpectralBand n07aAngularFrequency (n07aAngularFourier m hm u)).map
    (n07aAngularFourierInverse m hm) (n07aAngularFourierInverse m hm).continuous
  simpa only [Function.comp_def, ← n07aAngularBand_apply, n07aAngularFourierInverse_fourier] using h

/-- The spectral projection acts on the actual weak graph in both arguments. -/
theorem n07aAngularBand_weak (m : ℕ) (hm : K.left m < K.right m) (n : ℕ)
    {f g : CanonicalL2 S K m} {k : ℕ}
    (hfg : WeakCanonicalAngularDerivative S K m f g k) :
    WeakCanonicalAngularDerivative S K m
      (n07aAngularBand m hm n f) (n07aAngularBand m hm n g) k := by
  apply n07aAngularWeak_of_fourier m hm
  intro j
  rw [n07aAngularBand_coefficient, n07aAngularBand_coefficient,
    n07aAngularWeak_fourier m hm hfg]
  split_ifs <;> simp only [mul_zero]

/-- The same projection preserves the exact reflection in the frozen graph. -/
theorem n07aAngularBand_even (m : ℕ) (hm : K.left m < K.right m) (n : ℕ)
    {u : CanonicalL2 S K m}
    (hu : (fun p : PolarPoint => u (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m] u) :
    (fun p : PolarPoint => n07aAngularBand m hm n u (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] n07aAngularBand m hm n u := by
  apply (n07aAngularEven_fourier_iff m hm _).mpr
  have h := (n07aAngularEven_fourier_iff m hm u).mp hu
  intro j
  rw [n07aAngularBand_coefficient, n07aAngularBand_coefficient,
    n07aAngularFrequency_reflection, h j]

end ContinuousFlexibility.Statements
