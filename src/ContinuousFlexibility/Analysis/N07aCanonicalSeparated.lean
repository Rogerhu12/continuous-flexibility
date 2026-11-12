import ContinuousFlexibility.Analysis.N07aCanonicalBandRadial
import ContinuousFlexibility.Analysis.N07aCircleBlockCoefficients
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Actual separated L² fields and their angular weak derivative

Only the angular factor is differentiated. The radial factor is an
arbitrary actual interval L² representative, and Fubini is justified by
the compact-test L² pairing before integration by parts on the circle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

private instance n07aSeparatedAngleFinite : IsFiniteMeasure angleMeasure := by
  constructor
  rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  exact ENNReal.ofReal_lt_top

theorem n07a_circle_first_pairing {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f Real.pi) (hgp : Function.Periodic g Real.pi) :
    (∫ θ, deriv f θ * g θ ∂angleMeasure) =
      -(∫ θ, f θ * deriv g θ ∂angleMeasure) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hf.continuous.continuousOn hg.continuous.continuousOn
    (fun θ _ => (hf.differentiable (by simp) θ).hasDerivAt)
    (fun θ _ => (hg.differentiable (by simp) θ).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp hf).2.continuous.intervalIntegrable 0 Real.pi)
    ((contDiff_infty_iff_deriv.mp hg).2.continuous.intervalIntegrable 0 Real.pi)
  have hfend : f Real.pi = f 0 := by simpa only [zero_add] using hfp 0
  have hgend : g Real.pi = g 0 := by simpa only [zero_add] using hgp 0
  rw [hfend, hgend, sub_self, zero_sub] at h
  simp only [intervalIntegral.integral_of_le Real.pi_pos.le] at h
  change (∫ θ, f θ * deriv g θ ∂angleMeasure) =
    -(∫ θ, deriv f θ * g θ ∂angleMeasure) at h
  linarith only [h]

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aCanonicalSeparated_memLp {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hg : Continuous g) (M : ℝ) (hM : ∀ θ, |g θ| ≤ M) :
    MemLp (fun p : PolarPoint => f p.1 * g p.2) 2 (canonicalMeasure S K m) := by
  rw [n07aCanonicalMeasure_eq_prod]
  have hprod := hf.comp_fst angleMeasure
  apply hprod.of_le_mul (c := M)
    (hprod.aestronglyMeasurable.mul (hg.comp continuous_snd).aestronglyMeasurable)
  exact Eventually.of_forall fun p => by
    simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hM p.2) (abs_nonneg (f p.1))).trans_eq (mul_comm _ _)

def n07aCanonicalSeparated {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hg : Continuous g) (M : ℝ) (hM : ∀ θ, |g θ| ≤ M) : CanonicalL2 S K m :=
  (n07aCanonicalSeparated_memLp hf hg M hM).toLp (fun p => f p.1 * g p.2)

theorem n07aCanonicalSeparated_ae {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hg : Continuous g) (M : ℝ) (hM : ∀ θ, |g θ| ≤ M) :
    (n07aCanonicalSeparated hf hg M hM : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => f p.1 * g p.2 := MemLp.coeFn_toLp _

theorem n07aCanonicalSeparated_firstAngular {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g Real.pi)
    (M N : ℝ) (hM : ∀ θ, |g θ| ≤ M) (hN : ∀ θ, |deriv g θ| ≤ N) :
    N07aWeakCanonicalMixedDerivative S K m
      (n07aCanonicalSeparated hf hg.continuous M hM)
      (n07aCanonicalSeparated hf (contDiff_infty_iff_deriv.mp hg).2.continuous N hN) 0 1 := by
  intro φ hφ
  let U := n07aCanonicalSeparated hf hg.continuous M hM
  let D := n07aCanonicalSeparated hf (contDiff_infty_iff_deriv.mp hg).2.continuous N hN
  let left : PolarPoint → ℝ := fun p => (f p.1 * deriv g p.2) * φ p
  let right : PolarPoint → ℝ := fun p => (f p.1 * g p.2) * mixedDerivative 0 1 φ p
  have heL : (fun p => D p * φ p) =ᵐ[canonicalMeasure S K m] left :=
    (n07aCanonicalSeparated_ae hf (contDiff_infty_iff_deriv.mp hg).2.continuous N hN).mono
      (fun p hp => congrArg (· * φ p) hp)
  have heR : (fun p => U p * mixedDerivative 0 1 φ p) =ᵐ[canonicalMeasure S K m] right :=
    (n07aCanonicalSeparated_ae hf hg.continuous M hM).mono
      (fun p hp => congrArg (· * mixedDerivative 0 1 φ p) hp)
  have hiL := ((Lp.memLp D).integrable_mul (n07a_canonicalTest_memLp hφ)).congr heL
  have hiR := ((Lp.memLp U).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ 0 1))).congr heR
  have hrows (r : ℝ) : (∫ θ, left (r, θ) ∂angleMeasure) =
      -(∫ θ, right (r, θ) ∂angleMeasure) := by
    have hrow : ContDiff ℝ ∞ (fun θ => φ (r, θ)) :=
      hφ.1.comp (contDiff_const.prodMk contDiff_id)
    have hper : Function.Periodic (fun θ => φ (r, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hφ.2.1 (r, θ)
    have h := n07a_circle_first_pairing hg hrow hp hper
    simp only [left, right, mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one]
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_const_mul, h, mul_neg]
  simp only [Nat.zero_add, pow_one, neg_one_mul]
  rw [integral_congr_ae heL, integral_congr_ae heR]
  rw [n07aCanonicalMeasure_eq_prod] at hiL hiR ⊢
  rw [integral_prod _ hiL, integral_prod _ hiR, ← integral_neg]
  exact integral_congr_ae (Eventually.of_forall hrows)

end ContinuousFlexibility.Analysis
