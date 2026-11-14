module

public import ContinuousFlexibility.Analysis.N07aAngularEven
public import ContinuousFlexibility.Radial.ReferenceCosineAlgebra
public import ContinuousFlexibility.Radial.ReferenceCosineParseval

/-!
# The same angular bands in the physical and canonical Fourier conventions

The physical cosine coefficients average over a full `2π` interval.  The
canonical complex coefficients average over a `π` interval.  For the actual
even, `π`-periodic fields the two normalizations agree, with the usual
`sqrt 2` factor for positive cosine modes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open scoped ComplexConjugate ContDiff

private instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem n07aCircleFourierCoeff_interval (f : ℝ → ℝ) (n : ℤ) :
    circleFourierCoeff f n = ((Real.pi⁻¹ : ℝ) : ℂ) *
      ∫ θ in (0 : ℝ)..Real.pi, circleFourierWave (-n) θ * (f θ : ℂ) := by
  rw [circleFourierCoeff_integral, intervalIntegral.integral_of_le Real.pi_pos.le]
  simp only [angleMeasure, Complex.ofReal_inv]

theorem n07aCircleFourierCoeff_conj {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (he : Function.Even f) (n : ℤ) :
    conj (circleFourierCoeff f n) = circleFourierCoeff f n := by
  let g (θ : ℝ) : ℂ := circleFourierWave (-n) θ * (f θ : ℂ)
  have hreflect (θ : ℝ) : g (Real.pi - θ) = conj (g θ) := by
    have hf : f (Real.pi - θ) = f θ := by
      rw [sub_eq_add_neg, add_comm, hp, he]
    dsimp only [g]
    rw [hf, n07aCircleFourierWave_reflection, neg_neg]
    simp only [circleFourierWave, fourier_neg, map_mul, Complex.conj_ofReal,
      starRingEnd_self_apply]
  have hi : conj (∫ θ in (0 : ℝ)..Real.pi, g θ) =
      ∫ θ in (0 : ℝ)..Real.pi, g θ := by
    rw [← intervalIntegral.intervalIntegral_conj]
    calc
      (∫ θ in (0 : ℝ)..Real.pi, conj (g θ)) =
          ∫ θ in (0 : ℝ)..Real.pi, g (Real.pi - θ) :=
        intervalIntegral.integral_congr (fun θ _ => (hreflect θ).symm)
      _ = ∫ θ in (0 : ℝ)..Real.pi, g θ := by
        rw [intervalIntegral.integral_comp_sub_left]
        simp only [sub_self, sub_zero]
  rw [n07aCircleFourierCoeff_interval, map_mul, Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => ((Real.pi⁻¹ : ℝ) : ℂ) * z) hi

theorem n07aCircleFourierCoeff_neg_eq {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (he : Function.Even f) (n : ℤ) :
    circleFourierCoeff f (-n) = circleFourierCoeff f n := by
  rw [circleFourierCoeff_neg, n07aCircleFourierCoeff_conj hp he]

theorem n07aCircleFourierWave_re (n : ℤ) (θ : ℝ) :
    (circleFourierWave n θ).re = Real.cos (2 * (n : ℝ) * θ) := by
  rw [circleFourierWave, fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * n * θ / Real.pi =
        ((2 * (n : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [harg, Complex.exp_ofReal_mul_I_re]

theorem n07aCircleFourierCoeff_re {f : ℝ → ℝ}
    (hf : IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 Real.pi) (n : ℤ) :
    (circleFourierCoeff f n).re =
      Real.pi⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, f θ * Real.cos (2 * (n : ℝ) * θ) := by
  have hg : IntervalIntegrable
      (fun θ => circleFourierWave (-n) θ * (f θ : ℂ)) volume 0 Real.pi :=
    hf.continuousOn_mul (circleFourierWave_contDiff (-n)).continuous.continuousOn
  rw [n07aCircleFourierCoeff_interval]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hre : (∫ θ in (0 : ℝ)..Real.pi,
        circleFourierWave (-n) θ * (f θ : ℂ)).re =
      ∫ θ in (0 : ℝ)..Real.pi,
        (circleFourierWave (-n) θ * (f θ : ℂ)).re :=
    (intervalIntegral.intervalIntegral_re hg).symm
  rw [hre]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    n07aCircleFourierWave_re, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg]
  ring

private theorem n07a_referenceAngularCoefficient_nat {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hp : Function.Periodic f Real.pi) (he : Function.Even f) (n : ℕ) :
    (referenceAngularCoefficient f n : ℂ) =
      ((if n = 0 then 1 else Real.sqrt 2 : ℝ) : ℂ) * circleFourierCoeff f (n : ℤ) := by
  let : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  let : IsFiniteMeasure angleMeasure := by
    constructor
    rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hhalf : MemLp f 2 angleMeasure := hf.mono_measure
    (Measure.restrict_mono_set _ (Ioc_subset_Ioc le_rfl (by linarith [Real.pi_pos])))
  have hi : IntervalIntegrable f volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr
      (hf.integrable (by norm_num))
  have hiC : IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 Real.pi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr
      (hhalf.ofReal.integrable (by norm_num))
  have hr : referenceAngularCoefficient f n =
      (if n = 0 then 1 else Real.sqrt 2) * (circleFourierCoeff f (n : ℤ)).re := by
    cases n with
    | zero =>
      rw [referenceAngularCoefficient_zero, radialAngularMean_eq_halfPeriod hp hi,
        n07aCircleFourierCoeff_re hiC]
      simp only [ite_true, one_mul, Nat.cast_zero, Int.cast_zero, mul_zero,
        zero_mul, Real.cos_zero, mul_one]
    | succ n =>
      rw [n07aCircleFourierCoeff_re hiC]
      have hcos : IntervalIntegrable
          (fun θ => f θ * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ))
          volume 0 (2 * Real.pi) :=
        hi.mul_continuousOn
          (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
      have hper : Function.Periodic
          (fun θ => f θ * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ)) Real.pi := by
        intro θ
        dsimp only
        rw [hp θ]
        congr 1
        convert Real.cos_add_int_mul_two_pi (2 * ((n + 1 : ℕ) : ℝ) * θ)
          ((n + 1 : ℕ) : ℤ) using 1
        congr 1
        push_cast
        ring
      have hscale : referenceAngularCoefficient f (n + 1) =
          Real.sqrt 2 * radialAngularMean
            (fun θ => f θ * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ)) := by
        unfold referenceAngularCoefficient referenceAngularBasis cosineMode
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        have heq : (fun θ => f θ * (Real.sqrt 2 * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ))) =
            (fun θ => Real.sqrt 2 * (f θ * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ))) := by
          funext θ
          ring
        rw [heq, radialAngularMean_const_mul]
      rw [hscale, radialAngularMean_eq_halfPeriod hper hcos]
      simp only [Nat.succ_ne_zero, ite_false, Int.cast_natCast]
  rw [← Complex.conj_eq_iff_re.mp (n07aCircleFourierCoeff_conj hp he (n : ℤ)),
    ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal hr

/-- Exact coefficient conversion, retaining both signs of each complex mode. -/
theorem n07a_referenceAngularCoefficient_fourier {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hp : Function.Periodic f Real.pi) (he : Function.Even f) (k : ℤ) :
    (referenceAngularCoefficient f k.natAbs : ℂ) =
      ((if k.natAbs = 0 then 1 else Real.sqrt 2 : ℝ) : ℂ) * circleFourierCoeff f k := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · simpa only [Int.natAbs_natCast] using n07a_referenceAngularCoefficient_nat hf hp he n
  · simpa only [Int.natAbs_neg, Int.natAbs_natCast, n07aCircleFourierCoeff_neg_eq hp he]
      using n07a_referenceAngularCoefficient_nat hf hp he n

/-- The actual physical cosine projection is exactly the signed angular
Fourier mask on each even periodic section. -/
theorem n07a_circleFourierCoeff_basisProjection {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hp : Function.Periodic f Real.pi) (he : Function.Even f)
    (I : Finset ℕ) (k : ℤ) :
    circleFourierCoeff (angularBasisProjection I f) k =
      if k.natAbs ∈ I then circleFourierCoeff f k else 0 := by
  have hpf := memLp_referenceAngular_interval_of_continuous (continuous_angularBasisProjection I f)
  have hpp : Function.Periodic (angularBasisProjection I f) Real.pi := by
    intro θ
    exact referenceBasisProjection_periodic I (fun x : PolarPoint => f x.2) (0, θ)
  have hpe : Function.Even (angularBasisProjection I f) :=
    referenceBasisProjection_even I (fun x : PolarPoint => f x.2) 0
  have h := n07a_referenceAngularCoefficient_fourier hpf hpp hpe k
  have hc : (((if k.natAbs = 0 then 1 else Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    split_ifs
    · exact one_ne_zero
    · exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  apply mul_left_cancel₀ hc
  rw [← h, referenceAngularCoefficient_projection]
  by_cases hk : k.natAbs ∈ I
  · rw [ite_eq_left hk, ite_eq_left hk, n07a_referenceAngularCoefficient_fourier hf hp he]
  · simp only [ite_eq_right hk, Complex.ofReal_zero, mul_zero]

end ContinuousFlexibility.Statements
