import ContinuousFlexibility.Radial.FiniteFourierBessel
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Finite angular synthesis and projection contraction

Finite synthesis has exactly the sum-of-squares energy of its coefficients.
The actual finite cosine and sine projections therefore contract the
normalized angular L² norm for every interval L² input.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

/-- The finite projection is an actual finite sum of scalar functions. -/
def finiteAngularProjection {ι : Type*} (s : Finset ι)
    (e : ι → ℝ → ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∑ i ∈ s, angularPairing f (e i) * e i θ

theorem angularAverage_sq_finite_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (e : ι → ℝ → ℝ)
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (c : ι → ℝ) :
    angularAverage (fun θ => (∑ i ∈ s, c i * e i θ) ^ 2) = ∑ i ∈ s, c i ^ 2 := by
  classical
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
  let p : Lp ℝ 2 angularMeanMeasure := ∑ i : s, c i • v i
  have hterms (i : s) :
      ((c i • v i : Lp ℝ 2 angularMeanMeasure) : ℝ → ℝ) =ᵐ[angularMeanMeasure]
        (fun θ => c i * e i θ) := by
    filter_upwards [Lp.coeFn_smul (c i) (v i),
      (memLp_angularMeanMeasure (he i i.property)).coeFn_toLp] with θ hsmul heq
    simpa only [Pi.smul_apply, smul_eq_mul, heq] using hsmul
  have hae : (p : ℝ → ℝ) =ᵐ[angularMeanMeasure]
      (fun θ => ∑ i ∈ s, c i * e i θ) := by
    have hall : ∀ᵐ θ ∂angularMeanMeasure, ∀ i : s,
        (c i • v i : Lp ℝ 2 angularMeanMeasure) θ = c i * e i θ :=
      ae_all_iff.mpr hterms
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ : Finset s)
      (fun i : s => c i • v i), hall] with θ hsum hθ
    change (∑ i : s, c i • v i : Lp ℝ 2 angularMeanMeasure) θ =
      ∑ i ∈ s, c i * e i θ
    rw [hsum]
    simp only [hθ, Finset.univ_eq_attach, Finset.sum_attach]
  have hnorm : ‖p‖ ^ 2 = ∑ i ∈ s, c i ^ 2 := by
    calc
      _ = ⟪p, p⟫_ℝ := (real_inner_self_eq_norm_sq _).symm
      _ = ∑ i : s, c i ^ 2 := by
        simpa [p, pow_two] using
          hv.inner_sum (fun i : s => c i) (fun i : s => c i) Finset.univ
      _ = ∑ i ∈ s, c i ^ 2 := by
        simp only [Finset.univ_eq_attach, Finset.sum_attach]
  have hp : ‖p‖ ^ 2 = angularAverage (fun θ => p θ ^ 2) := by
    simpa only [Lp.toLp_coeFn] using angularMean_norm_sq_toLp (Lp.memLp p)
  calc
    angularAverage (fun θ => (∑ i ∈ s, c i * e i θ) ^ 2) =
        angularAverage (fun θ => p θ ^ 2) := by
      rw [angularAverage_eq_integral_angularMeanMeasure,
        angularAverage_eq_integral_angularMeanMeasure]
      exact integral_congr_ae (hae.symm.mono fun θ hθ => congrArg (fun x : ℝ => x ^ 2) hθ)
    _ = ‖p‖ ^ 2 := hp.symm
    _ = ∑ i ∈ s, c i ^ 2 := hnorm

theorem finiteAngularProjection_memLp {ι : Type*} (s : Finset ι)
    (e : ι → ℝ → ℝ) (f : ℝ → ℝ)
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    MemLp (finiteAngularProjection s e f) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hsum := memLp_finsetSum s
    (fun i hi => (he i hi).const_smul (angularPairing f (e i)))
  simpa only [finiteAngularProjection, Pi.smul_apply, smul_eq_mul] using hsum

theorem finiteAngularProjection_square_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (e : ι → ℝ → ℝ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    angularAverage (fun θ => finiteAngularProjection s e f θ ^ 2) ≤
      angularAverage (fun θ => f θ ^ 2) := by
  calc
    _ = ∑ i ∈ s, angularPairing f (e i) ^ 2 :=
      angularAverage_sq_finite_sum s e he horth (fun i => angularPairing f (e i))
    _ ≤ angularAverage (fun θ => f θ ^ 2) :=
      angularPairing_finite_bessel s e hf he horth

theorem finiteAngularProjection_norm_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (e : ι → ℝ → ℝ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    ‖(memLp_angularMeanMeasure (finiteAngularProjection_memLp s e f he)).toLp
        (finiteAngularProjection s e f)‖ ≤ ‖(memLp_angularMeanMeasure hf).toLp f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [angularMean_norm_sq_toLp, angularMean_norm_sq_toLp]
  exact finiteAngularProjection_square_le s e hf he horth

abbrev finiteCosineProjection (J : Finset ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  finiteAngularProjection J cosineMode f

abbrev finiteSineProjection (J : Finset ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  finiteAngularProjection J sineMode f

theorem finiteCosineProjection_square_le (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 0 < j) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    angularAverage (fun θ => finiteCosineProjection J f θ ^ 2) ≤
      angularAverage (fun θ => f θ ^ 2) :=
  finiteAngularProjection_square_le J cosineMode hf
    (fun j _ => cosineMode_memLp_angularInterval j)
    (fun j hj k hk => angularPairing_cosineMode j k (hJ j hj) (hJ k hk))

theorem finiteSineProjection_square_le (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 0 < j) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    angularAverage (fun θ => finiteSineProjection J f θ ^ 2) ≤
      angularAverage (fun θ => f θ ^ 2) :=
  finiteAngularProjection_square_le J sineMode hf
    (fun j _ => sineMode_memLp_angularInterval j)
    (fun j hj k hk => angularPairing_sineMode j k (hJ j hj) (hJ k hk))

end

end ContinuousFlexibility.Radial
