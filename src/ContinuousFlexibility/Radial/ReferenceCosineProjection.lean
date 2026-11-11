import ContinuousFlexibility.Radial.ReferenceGraphNorms
import ContinuousFlexibility.Radial.ReferenceWeightedRadialBase
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Finite cosine projections with the physical normalization

The constant mode and the positive even cosine modes form an orthonormal
family for the actual probability measure `(2π)⁻¹ dθ` on one full period.
Bessel's inequality therefore controls finite angular projections before
any radial weight is introduced.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace InnerProductSpace

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

noncomputable section

/-- Normalized angular measure on the same full period as the frozen norms. -/
abbrev referenceAngularProbability : Measure ℝ :=
  ContinuousFlexibility.Statements.referenceAngularMeasure

theorem integral_referenceAngularProbability (f : ℝ → ℝ) :
    (∫ θ, f θ ∂referenceAngularProbability) = radialAngularMean f :=
  ContinuousFlexibility.Statements.integral_referenceAngularMeasure f

theorem memLp_referenceAngular_interval_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let : IsFiniteMeasure μ :=
    ⟨by
      dsimp only [μ]
      rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
      exact ENNReal.ofReal_lt_top⟩
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi))).bddAbove_image
      hf.norm.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  exact hC ⟨θ, ⟨hθ.1.le, hθ.2⟩, rfl⟩

theorem memLp_referenceAngularProbability {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    MemLp f 2 referenceAngularProbability :=
  hf.smul_measure ENNReal.ofReal_ne_top

/-- Index zero is the constant mode; positive indices are the normalized
cosines at frequencies `2n`. -/
def referenceAngularBasis : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => cosineMode (2 * (n + 1))

theorem contDiff_referenceAngularBasis (n : ℕ) : ContDiff ℝ ∞ (referenceAngularBasis n) := by
  cases n with
  | zero => exact contDiff_const
  | succ n =>
    change ContDiff ℝ ∞ (fun θ : ℝ => Real.sqrt 2 * Real.cos (((2 * (n + 1) : ℕ) : ℝ) * θ))
    exact contDiff_const.mul ((contDiff_const.mul contDiff_id).cos)

theorem referenceAngularBasis_pairing (i j : ℕ) :
    radialAngularMean (fun θ => referenceAngularBasis i θ * referenceAngularBasis j θ) =
      if i = j then 1 else 0 := by
  cases i with
  | zero =>
    cases j with
    | zero =>
      simp only [referenceAngularBasis, mul_one, ite_true]
      simp only [radialAngularMean, intervalIntegral.integral_const, sub_zero,
        smul_eq_mul, mul_one]
      exact inv_mul_cancel₀ (by positivity)
    | succ j =>
      change radialAngularMean (fun θ => 1 * cosineMode (2 * (j + 1)) θ) = 0
      simpa only [one_mul, radialAngularMean, angularAverage, one_div] using
        angularAverage_cosineMode (2 * (j + 1)) (by omega)
  | succ i =>
    cases j with
    | zero =>
      change radialAngularMean (fun θ => cosineMode (2 * (i + 1)) θ * 1) = 0
      simpa only [mul_one, radialAngularMean, angularAverage, one_div] using
        angularAverage_cosineMode (2 * (i + 1)) (by omega)
    | succ j =>
      have h := angularPairing_cosineMode (2 * (i + 1)) (2 * (j + 1))
        (by omega) (by omega)
      by_cases hij : i = j
      · subst j
        simpa only [referenceAngularBasis, angularPairing, angularAverage,
          radialAngularMean, one_div, ite_true] using h
      · have hfreq : 2 * (i + 1) ≠ 2 * (j + 1) := by omega
        have hsucc : i + 1 ≠ j + 1 := by omega
        simpa only [referenceAngularBasis, angularPairing, angularAverage,
          radialAngularMean, one_div, if_neg hfreq, if_neg hsucc] using h

theorem memLp_referenceAngularBasis (n : ℕ) :
    MemLp (referenceAngularBasis n) 2 referenceAngularProbability :=
  memLp_referenceAngularProbability
    (memLp_referenceAngular_interval_of_continuous (contDiff_referenceAngularBasis n).continuous)

def referenceAngularBasisL2 (n : ℕ) : Lp ℝ 2 referenceAngularProbability :=
  (memLp_referenceAngularBasis n).toLp (referenceAngularBasis n)

theorem orthonormal_referenceAngularBasisL2 :
    Orthonormal ℝ referenceAngularBasisL2 := by
  apply orthonormal_iff_ite.mpr
  intro i j
  change ⟪(memLp_referenceAngularBasis i).toLp (referenceAngularBasis i),
    (memLp_referenceAngularBasis j).toLp (referenceAngularBasis j)⟫_ℝ = _
  rw [reference_memLp_inner_eq_integral, integral_referenceAngularProbability,
    referenceAngularBasis_pairing]

/-- Actual normalized angular coefficient, including the mean at index zero. -/
def referenceAngularCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  radialAngularMean (fun θ => f θ * referenceAngularBasis n θ)

@[simp] theorem referenceAngularCoefficient_zero (f : ℝ → ℝ) :
    referenceAngularCoefficient f 0 = radialAngularMean f := by
  simp only [referenceAngularCoefficient, referenceAngularBasis, mul_one]

@[simp] theorem referenceAngularCoefficient_succ (f : ℝ → ℝ) (n : ℕ) :
    referenceAngularCoefficient f (n + 1) =
      radialAngularMean (fun θ => f θ * cosineMode (2 * (n + 1)) θ) := rfl

theorem referenceAngularCoefficient_eq_inner {f : ℝ → ℝ}
    (hf : MemLp f 2 referenceAngularProbability) (n : ℕ) :
    referenceAngularCoefficient f n =
      ⟪referenceAngularBasisL2 n, hf.toLp f⟫_ℝ := by
  unfold referenceAngularCoefficient
  change _ = ⟪(memLp_referenceAngularBasis n).toLp (referenceAngularBasis n), hf.toLp f⟫_ℝ
  rw [reference_memLp_inner_eq_integral, integral_referenceAngularProbability]
  apply congrArg radialAngularMean
  funext θ
  exact mul_comm _ _

theorem referenceAngularCoefficient_const_mul (c : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    referenceAngularCoefficient (fun θ => c * f θ) n =
      c * referenceAngularCoefficient f n := by
  simp only [referenceAngularCoefficient, radialAngularMean, mul_assoc,
    intervalIntegral.integral_const_mul]
  ring

/-- Projection onto any finite set of the mean/cosine basis. -/
def angularBasisProjection (I : Finset ℕ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∑ n ∈ I, referenceAngularCoefficient f n * referenceAngularBasis n θ

theorem continuous_angularBasisProjection (I : Finset ℕ) (f : ℝ → ℝ) :
    Continuous (angularBasisProjection I f) := by
  unfold angularBasisProjection
  apply continuous_finset_sum
  intro n _hn
  exact continuous_const.mul (contDiff_referenceAngularBasis n).continuous

theorem angularBasisProjection_toLp (I : Finset ℕ) (f : ℝ → ℝ) :
    (memLp_referenceAngularProbability
      (memLp_referenceAngular_interval_of_continuous
        (continuous_angularBasisProjection I f))).toLp (angularBasisProjection I f) =
      ∑ n ∈ I, referenceAngularCoefficient f n • referenceAngularBasisL2 n := by
  let hp := memLp_referenceAngularProbability
    (memLp_referenceAngular_interval_of_continuous (continuous_angularBasisProjection I f))
  have he (n : ℕ) :
      ((referenceAngularCoefficient f n • referenceAngularBasisL2 n :
        Lp ℝ 2 referenceAngularProbability) : ℝ → ℝ)
        =ᵐ[referenceAngularProbability]
          (fun θ => referenceAngularCoefficient f n * referenceAngularBasis n θ) := by
    filter_upwards [Lp.coeFn_smul (referenceAngularCoefficient f n) (referenceAngularBasisL2 n),
      (memLp_referenceAngularBasis n).coeFn_toLp] with θ hsmul hb
    calc
      ((referenceAngularCoefficient f n • referenceAngularBasisL2 n :
          Lp ℝ 2 referenceAngularProbability) : ℝ → ℝ) θ =
          referenceAngularCoefficient f n *
            (referenceAngularBasisL2 n : ℝ → ℝ) θ := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
      _ = referenceAngularCoefficient f n * referenceAngularBasis n θ :=
        congrArg (fun z : ℝ => referenceAngularCoefficient f n * z) hb
  have hall := ae_all_iff.mpr he
  apply Lp.ext
  filter_upwards [hp.coeFn_toLp,
    Lp.coeFn_fun_finsetSum I
      (fun n => referenceAngularCoefficient f n • referenceAngularBasisL2 n), hall]
    with θ hpθ hsum hθ
  rw [hpθ, hsum]
  change (∑ n ∈ I, referenceAngularCoefficient f n * referenceAngularBasis n θ) = _
  exact Finset.sum_congr rfl (fun n _ => (hθ n).symm)

theorem angularBasisProjection_sq (I : Finset ℕ) (f : ℝ → ℝ) :
    radialAngularMean (fun θ => angularBasisProjection I f θ ^ 2) =
      ∑ n ∈ I, referenceAngularCoefficient f n ^ 2 := by
  let hp := memLp_referenceAngularProbability
    (memLp_referenceAngular_interval_of_continuous (continuous_angularBasisProjection I f))
  rw [← integral_referenceAngularProbability, ← reference_memLp_norm_sq_eq_integral hp,
    angularBasisProjection_toLp, ← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro n hn
  rw [inner_smul_left, orthonormal_referenceAngularBasisL2.inner_right_sum _ hn]
  simp only [conj_trivial, pow_two]

/-- Bessel's inequality with the exact normalization of the frozen cell norm. -/
theorem referenceAngularCoefficient_sum_sq_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) (I : Finset ℕ) :
    (∑ n ∈ I, referenceAngularCoefficient f n ^ 2) ≤
      radialAngularMean (fun θ => f θ ^ 2) := by
  let h := memLp_referenceAngularProbability hf
  have hb := orthonormal_referenceAngularBasisL2.sum_inner_products_le
    (s := I) (x := h.toLp f)
  simpa only [← referenceAngularCoefficient_eq_inner h,
    Real.norm_eq_abs, sq_abs, reference_memLp_norm_sq_eq_integral,
    integral_referenceAngularProbability] using hb

theorem referenceAngularCoefficient_sq_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) (n : ℕ) :
    referenceAngularCoefficient f n ^ 2 ≤ radialAngularMean (fun θ => f θ ^ 2) := by
  simpa only [Finset.sum_singleton] using referenceAngularCoefficient_sum_sq_le hf {n}

theorem angularBasisProjection_sq_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) (I : Finset ℕ) :
    radialAngularMean (fun θ => angularBasisProjection I f θ ^ 2) ≤
      radialAngularMean (fun θ => f θ ^ 2) := by
  rw [angularBasisProjection_sq]
  exact referenceAngularCoefficient_sum_sq_le hf I

/-- The public finite projection keeps the mean and the specified positive modes.
The index `n` corresponds to the frequency `2(n+1)`. -/
def angularCosineProjection (J : Finset ℕ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  radialAngularMean f +
    ∑ n ∈ J, referenceAngularCoefficient f (n + 1) * cosineMode (2 * (n + 1)) θ

theorem angularCosineProjection_eq_basis (J : Finset ℕ) (f : ℝ → ℝ) :
    angularCosineProjection J f = angularBasisProjection (insert 0 (J.image Nat.succ)) f := by
  funext θ
  have hz : (0 : ℕ) ∉ J.image Nat.succ := by simp
  simp only [angularCosineProjection, angularBasisProjection, Finset.sum_insert hz,
    referenceAngularCoefficient_zero, referenceAngularBasis, mul_one,
    Finset.sum_image (fun i _ j _ hij => Nat.succ_injective hij)]

theorem angularCosineProjection_sq_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) (J : Finset ℕ) :
    radialAngularMean (fun θ => angularCosineProjection J f θ ^ 2) ≤
      radialAngularMean (fun θ => f θ ^ 2) := by
  rw [angularCosineProjection_eq_basis]
  exact angularBasisProjection_sq_le hf _

/-- Finite angular projection of an actual polar field. -/
def referenceCosineProjection (J : Finset ℕ) (u : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  angularCosineProjection J (fun θ => u (x.1, θ)) x.2

theorem referenceCosineProjection_apply (J : Finset ℕ) (u : PolarPoint → ℝ) (r θ : ℝ) :
    referenceCosineProjection J u (r, θ) =
      radialAngularMean (fun η => u (r, η)) +
        ∑ n ∈ J, referenceMode u (2 * (n + 1)) r * cosineMode (2 * (n + 1)) θ := rfl

end

end ContinuousFlexibility.Radial
