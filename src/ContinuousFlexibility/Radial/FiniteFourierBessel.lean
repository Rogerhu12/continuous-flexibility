import ContinuousFlexibility.Radial.AngularMeanL2
import ContinuousFlexibility.Radial.FourierSineOrthogonality
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Finite Bessel inequalities for actual angular coefficients

The input is an arbitrary interval L² function. The coefficients and the
right-hand side are the normalized ordinary angular integrals. The proof
lifts only the finitely many basis functions to the normalized L² space
and applies the finite Hilbert-space Bessel inequality.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

/-- Finite Bessel inequality with an actual angular orthogonality hypothesis. -/
theorem angularPairing_finite_bessel {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (e : ι → ℝ → ℝ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    (∑ i ∈ s, angularPairing f (e i) ^ 2) ≤ angularAverage (fun θ => f θ ^ 2) := by
  classical
  let u : Lp ℝ 2 angularMeanMeasure := (memLp_angularMeanMeasure hf).toLp f
  let v : s → Lp ℝ 2 angularMeanMeasure := fun i =>
    (memLp_angularMeanMeasure (he i i.property)).toLp (e i)
  have hv : Orthonormal ℝ v := by
    apply orthonormal_iff_ite.mpr
    intro i j
    change ⟪(memLp_angularMeanMeasure (he i i.property)).toLp (e i),
        (memLp_angularMeanMeasure (he j j.property)).toLp (e j)⟫_ℝ =
      if i = j then 1 else 0
    rw [angularMean_inner_toLp]
    simpa only [Subtype.ext_iff] using horth i i.property j j.property
  have hcoeff (i : s) : ⟪v i, u⟫_ℝ = angularPairing f (e i) := by
    rw [real_inner_comm]
    exact angularMean_inner_toLp (memLp_angularMeanMeasure hf)
      (memLp_angularMeanMeasure (he i i.property))
  have hB := hv.sum_inner_products_le (x := u) (s := Finset.univ)
  calc
    (∑ i ∈ s, angularPairing f (e i) ^ 2) =
        ∑ i : s, ‖⟪v i, u⟫_ℝ‖ ^ 2 := by
      simp only [hcoeff, Real.norm_eq_abs, sq_abs, Finset.univ_eq_attach]
      exact (Finset.sum_attach s (fun i => angularPairing f (e i) ^ 2)).symm
    _ ≤ ‖u‖ ^ 2 := hB
    _ = angularAverage (fun θ => f θ ^ 2) :=
      angularMean_norm_sq_toLp (memLp_angularMeanMeasure hf)

theorem cosineMode_memLp_angularInterval (j : ℕ) :
    MemLp (cosineMode j) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  apply angularInterval_memLp_of_continuous
  exact continuous_const.mul
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))

theorem sineMode_memLp_angularInterval (j : ℕ) :
    MemLp (sineMode j) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
  angularInterval_memLp_of_continuous (continuous_sineMode j)

/-- Bessel's inequality for every finite set of positive cosine frequencies. -/
theorem cosineMode_finite_bessel (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 0 < j) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    (∑ j ∈ J, angularAverage (fun θ => f θ * cosineMode j θ) ^ 2) ≤
      angularAverage (fun θ => f θ ^ 2) :=
  angularPairing_finite_bessel J cosineMode hf
    (fun j _ => cosineMode_memLp_angularInterval j)
    (fun j hj k hk => angularPairing_cosineMode j k (hJ j hj) (hJ k hk))

/-- The sine inequality applies directly to the odd angular derivative of
an even source; no even-source membership is imposed on that derivative. -/
theorem sineMode_finite_bessel (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 0 < j) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    (∑ j ∈ J, angularAverage (fun θ => f θ * sineMode j θ) ^ 2) ≤
      angularAverage (fun θ => f θ ^ 2) :=
  angularPairing_finite_bessel J sineMode hf
    (fun j _ => sineMode_memLp_angularInterval j)
    (fun j hj k hk => angularPairing_sineMode j k (hJ j hj) (hJ k hk))

end

end ContinuousFlexibility.Radial
