import ContinuousFlexibility.Analysis.N06GlobalFourierApproximants
import ContinuousFlexibility.Analysis.N06WeakAngularMultiplier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Fourier truncation preserves the actual canonical weak graph

The truncated fields have smooth angular sections, but their radial
coefficients are arbitrary L2 functions. Angular integration by parts and
Fubini identify their actual weak jets on every original canonical interval.
The zeroth reflection condition follows from the genuine cosine synthesis.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

private theorem n06_circle_deriv_pairing
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f Real.pi) (hgp : Function.Periodic g Real.pi) :
    (∫ θ, deriv f θ * g θ ∂angleMeasure) =
      -(∫ θ, f θ * deriv g θ ∂angleMeasure) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := Real.pi)
    (fun θ _ => (hf.differentiable (by simp) θ).hasDerivAt)
    (fun θ _ => (hg.differentiable (by simp) θ).hasDerivAt)
    ((hf.continuous_deriv (by simp)).intervalIntegrable _ _)
    ((hg.continuous_deriv (by simp)).intervalIntegrable _ _)
  have hfπ : f Real.pi = f 0 := by simpa only [zero_add] using hfp 0
  have hgπ : g Real.pi = g 0 := by simpa only [zero_add] using hgp 0
  simp only [hfπ, hgπ, sub_self, zero_sub] at h
  have h' : (∫ θ in (0 : ℝ)..Real.pi, deriv f θ * g θ) =
      -(∫ θ in (0 : ℝ)..Real.pi, f θ * deriv g θ) := by
    linarith only [h]
  simpa only [intervalIntegral.integral_of_le Real.pi_pos.le, angleMeasure] using h'

theorem n06_circle_iteratedDeriv_pairing
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f Real.pi) (hgp : Function.Periodic g Real.pi) (j : ℕ) :
    (∫ θ, iteratedDeriv j f θ * g θ ∂angleMeasure) =
      (-1 : ℝ) ^ j * ∫ θ, f θ * iteratedDeriv j g θ ∂angleMeasure := by
  induction j generalizing g with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ j ih =>
    have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
    have hgdp : Function.Periodic (deriv g) Real.pi := by
      simpa only [iteratedDeriv_one] using circleFourier_periodic_iteratedDeriv hgp 1
    rw [iteratedDeriv_succ,
      n06_circle_deriv_pairing (circleFourier_contDiff_iteratedDeriv hf j) hg
        (circleFourier_periodic_iteratedDeriv hfp j) hgp,
      ih hgd hgdp, ← iteratedDeriv_succ', pow_succ]
    ring

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- Only angular smoothness is used; the original radial variable remains
measurable and square-integrable. -/
theorem n06_canonicalAngularPairing_of_sections
    {f : PolarPoint → ℝ} (j : ℕ)
    (hf : MemLp f 2 (canonicalMeasure S K m))
    (hfj : MemLp (mixedDerivative 0 j f) 2 (canonicalMeasure S K m))
    (hsm : ∀ r : ℝ, ContDiff ℝ ∞ (fun θ : ℝ => f (r, θ)))
    (hp : ∀ r : ℝ, Function.Periodic (fun θ : ℝ => f (r, θ)) Real.pi)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, mixedDerivative 0 j f p * φ p ∂canonicalMeasure S K m) =
      (-1 : ℝ) ^ j * ∫ p, f p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m := by
  have hi : Integrable (fun p => mixedDerivative 0 j f p * φ p)
      (canonicalMeasure S K m) := hfj.integrable_mul hφ.n06_memLp
  have hj : Integrable (fun p => f p * mixedDerivative 0 j φ p)
      (canonicalMeasure S K m) := hf.integrable_mul (hφ.n06_mixedDerivative 0 j).n06_memLp
  rw [n06_canonicalMeasure_eq_radial_prod] at hi hj ⊢
  rw [integral_prod _ hi, integral_prod _ hj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  have hψ : ContDiff ℝ ∞ (fun θ : ℝ => φ (r, θ)) :=
    hφ.1.comp (contDiff_const.prodMk contDiff_id)
  have hψp : Function.Periodic (fun θ : ℝ => φ (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hφ.2.1 (r, θ)
  simpa only [mixedDerivative, iteratedDeriv_zero] using
    n06_circle_iteratedDeriv_pairing (hsm r) hψ (hp r) hψp j

/-- The actual L2 cutoff commutes with every stored weak angular derivative. -/
theorem WeakCanonicalAngularDerivative.n06_fourierCut
    {f g : CanonicalL2 S K m} {j : ℕ}
    (hfg : WeakCanonicalAngularDerivative S K m f g j) (N : ℕ) :
    WeakCanonicalAngularDerivative S K m
      (n06CanonicalFourierCutL2 N f) (n06CanonicalFourierCutL2 N g) j := by
  intro φ hφ
  have hG : (n06CanonicalFourierCutL2 N g : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        mixedDerivative 0 j (n06CylinderFourierCut (n06FourierCutoff N) f) :=
    (n06CanonicalFourierCutL2_coe_ae N g).trans
      (hfg.n06_fourierCut_angularJet_ae _ (n06FourierCutoff_neg N)).symm
  calc
    _ = ∫ p, mixedDerivative 0 j (n06CylinderFourierCut (n06FourierCutoff N) f) p *
        φ p ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [hG] with p hp
      rw [hp]
    _ = (-1 : ℝ) ^ j * ∫ p, n06CylinderFourierCut (n06FourierCutoff N) f p *
        mixedDerivative 0 j φ p ∂canonicalMeasure S K m :=
      n06_canonicalAngularPairing_of_sections j
        (n06_canonicalFourierCut_memLp f N)
        (n06_canonicalFourierCut_angularJet_memLp f _ j)
        (fun r => n06CircleFourierCut_contDiff _ (fun θ => f (r, θ)))
        (fun r => n06CircleFourierCut_periodic _ (fun θ => f (r, θ))) hφ
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [n06CanonicalFourierCutL2_coe_ae N f] with p hp
      rw [hp]

theorem n06CanonicalFourierCutL2_reflection
    (N : ℕ) (f : CanonicalL2 S K m)
    (he : (fun p : PolarPoint => f (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (f : PolarPoint → ℝ)) :
    (fun p : PolarPoint => n06CanonicalFourierCutL2 N f (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (n06CanonicalFourierCutL2 N f : PolarPoint → ℝ) := by
  have hc := n06CanonicalFourierCutL2_coe_cosine_ae N f he
  have hr := n06_measurePreserving_canonicalAngularReflection.quasiMeasurePreserving.ae_eq_comp hc
  filter_upwards [hr, hc] with p hp hq
  change n06CanonicalFourierCutL2 N f (p.1, Real.pi - p.2) =
    n06CylinderCosineCut N f (p.1, Real.pi - p.2) at hp
  rw [hp, hq]
  simp only [n06CylinderCosineCut, r11bFiniteSynthesis]
  apply Finset.sum_congr rfl
  intro i _
  have he' : referenceAngularBasis i (Real.pi - p.2) = referenceAngularBasis i p.2 := by
    rw [sub_eq_add_neg, add_comm, referenceAngularBasis_periodic, referenceAngularBasis_even]
  rw [he']

end ContinuousFlexibility.Statements
