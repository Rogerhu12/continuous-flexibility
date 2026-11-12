import ContinuousFlexibility.Analysis.N06CanonicalFourierCutoff

/-!
# The original canonical tests separate actual L2 fields and weak jets

The already proved weak Fourier symbols and the actual angular Fourier
isometry identify almost every radial slice. The original product-measure
completeness lemma then identifies the canonical L2 elements themselves.
No evenness, unit radial interval, or smooth source is required.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

theorem n06_canonicalL2_eq_of_fourierCoeff_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {f g : CanonicalL2 S K m}
    (hcoeff : ∀ n : ℤ,
      (fun r => circleFourierCoeff (fun θ => f (r, θ)) n)
        =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))]
          (fun r => circleFourierCoeff (fun θ => g (r, θ)) n)) : f = g := by
  have hall : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)), ∀ n : ℤ,
      circleFourierCoeff (fun θ => f (r, θ)) n =
        circleFourierCoeff (fun θ => g (r, θ)) n := ae_all_iff.mpr hcoeff
  have hsections : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      (fun θ => f (r, θ)) =ᵐ[angleMeasure] (fun θ => g (r, θ)) := by
    filter_upwards [hall, n06_canonicalL2_angular_sections f,
      n06_canonicalL2_angular_sections g] with r hr hfr hgr
    have hclass : hfr.toLp (fun θ => f (r, θ)) = hgr.toLp (fun θ => g (r, θ)) := by
      apply circleFourierCoeff_injective
      funext n
      rw [congrFun (circleFourierCoeff_congr_ae hfr.coeFn_toLp) n,
        congrFun (circleFourierCoeff_congr_ae hgr.coeFn_toLp) n]
      exact hr n
    have hae : (hfr.toLp (fun θ => f (r, θ)) : ℝ → ℝ) =ᵐ[angleMeasure]
        (hgr.toLp (fun θ => g (r, θ)) : ℝ → ℝ) :=
      Eventually.of_forall (fun θ => congrArg (fun u : AngleL2 => u θ) hclass)
    exact hfr.coeFn_toLp.symm.trans (hae.trans hgr.coeFn_toLp)
  have hprod := r11b_memLp_ae_eq_of_sections (n06_canonicalL2_memLp_prod f)
    (n06_canonicalL2_memLp_prod g) hsections
  apply Lp.ext
  exact (congrArg (fun ν : Measure PolarPoint =>
    (f : PolarPoint → ℝ) =ᵐ[ν] (g : PolarPoint → ℝ))
      (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mpr hprod

/-- Equality against exactly the frozen canonical test class determines
the original canonical L2 element, for every canonical cylinder. -/
theorem n06_canonicalL2_test_ext
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {f g : CanonicalL2 S K m}
    (hpair : ∀ φ, CanonicalTest S K m φ →
      (∫ p, f p * φ p ∂canonicalMeasure S K m) =
        ∫ p, g p * φ p ∂canonicalMeasure S K m) : f = g := by
  have hfg : WeakCanonicalAngularDerivative S K m f g 0 := by
    intro φ hφ
    simpa only [pow_zero, one_mul, spaces_mixedDerivative_zero] using (hpair φ hφ).symm
  apply n06_canonicalL2_eq_of_fourierCoeff_ae
  intro n
  simpa only [pow_zero, one_mul] using (hfg.n06_fourierCoeff_ae n).symm

theorem WeakCanonicalAngularDerivative.n06_unique
    {S : PhysicalSpacesData} {K : CanonicalData S} {m j : ℕ}
    {f g h : CanonicalL2 S K m}
    (hfg : WeakCanonicalAngularDerivative S K m f g j)
    (hfh : WeakCanonicalAngularDerivative S K m f h j) : g = h := by
  apply n06_canonicalL2_test_ext
  intro φ hφ
  exact (hfg φ hφ).trans (hfh φ hφ).symm

theorem n06_canonicalWeakJetRow_ext
    {S : PhysicalSpacesData} {K : CanonicalData S} {m b : ℕ}
    {v w : Fin (b + 1) → CanonicalL2 S K m}
    (hv : ∀ k, WeakCanonicalAngularDerivative S K m (v 0) (v k) k.val)
    (hw : ∀ k, WeakCanonicalAngularDerivative S K m (w 0) (w k) k.val)
    (hzero : v 0 = w 0) : v = w := by
  funext k
  apply n06_canonicalL2_test_ext
  intro φ hφ
  rw [hv k φ hφ, hw k φ hφ, hzero]

end ContinuousFlexibility.Statements
