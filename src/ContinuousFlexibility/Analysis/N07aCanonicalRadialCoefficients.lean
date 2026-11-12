import ContinuousFlexibility.Analysis.N07aAngularEven
import ContinuousFlexibility.Analysis.N07aCanonicalWeakJets
import ContinuousFlexibility.Analysis.IntervalWeakPrimitive
import ContinuousFlexibility.Radial.ReferenceGraphCoefficients
import ContinuousFlexibility.Radial.ReferenceCosineParseval

/-!
# Actual radial cosine coefficients of canonical weak derivatives

Canonical classes are integrated over their prescribed half period. No
periodic representative is presumed. Zero extension to the other half
period is used only to reuse the existing scalar L² coefficient estimate.
Separated compact tests then identify the genuine first weak derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

/-- Actual normalized cosine coefficient on the canonical angular interval. -/
def n07aHalfRadialCoefficient (u : PolarPoint → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  Real.pi⁻¹ * ∫ θ in Ioc (0 : ℝ) Real.pi, u (r, θ) * referenceAngularBasis n θ

private def n07aAngularZeroExtension (u : PolarPoint → ℝ) : PolarPoint → ℝ :=
  (univ ×ˢ Ioc (0 : ℝ) Real.pi).indicator u

private theorem n07aAngularZeroExtension_memLp {μ : Measure ℝ} [SFinite μ]
    {u : PolarPoint → ℝ} (hu : MemLp u 2 (μ.prod angleMeasure)) :
    MemLp (n07aAngularZeroExtension u) 2
      (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  unfold n07aAngularZeroExtension
  rw [memLp_indicator_iff_restrict (MeasurableSet.univ.prod measurableSet_Ioc),
    ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_restrict measurableSet_Ioc]
  have hs : Ioc (0 : ℝ) Real.pi ⊆ Ioc (0 : ℝ) (2 * Real.pi) :=
    Ioc_subset_Ioc le_rfl (by linarith [Real.pi_pos])
  rw [inter_eq_left.mpr hs]
  exact hu

private theorem n07aHalfRadialCoefficient_zeroExtension (u : PolarPoint → ℝ)
    (n : ℕ) (r : ℝ) :
    n07aHalfRadialCoefficient u n r =
      2 * referenceRadialCoefficient (n07aAngularZeroExtension u) n r := by
  have he : (fun θ => n07aAngularZeroExtension u (r, θ) * referenceAngularBasis n θ) =
      (Ioc (0 : ℝ) Real.pi).indicator (fun θ => u (r, θ) * referenceAngularBasis n θ) := by
    funext θ
    rw [Set.indicator_mul_left]
    by_cases hθ : θ ∈ Ioc (0 : ℝ) Real.pi
    · rw [indicator_of_mem hθ]
      have hp : (r, θ) ∈ univ ×ˢ Ioc (0 : ℝ) Real.pi := ⟨mem_univ r, hθ⟩
      simp only [n07aAngularZeroExtension, indicator_of_mem hp]
    · rw [indicator_of_notMem hθ]
      have hp : (r, θ) ∉ univ ×ˢ Ioc (0 : ℝ) Real.pi := fun h => hθ h.2
      simp only [n07aAngularZeroExtension, indicator_of_notMem hp]
  unfold referenceRadialCoefficient referenceAngularCoefficient radialAngularMean
  rw [intervalIntegral.integral_of_le (by positivity), he, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have hs : Ioc (0 : ℝ) Real.pi ⊆ Ioc (0 : ℝ) (2 * Real.pi) :=
    Ioc_subset_Ioc le_rfl (by linarith [Real.pi_pos])
  rw [inter_eq_left.mpr hs]
  unfold n07aHalfRadialCoefficient
  field_simp [Real.pi_ne_zero]

theorem n07aHalfRadialCoefficient_memLp {μ : Measure ℝ} [SFinite μ]
    {u : PolarPoint → ℝ} (hu : MemLp u 2 (μ.prod angleMeasure)) (n : ℕ) :
    MemLp (n07aHalfRadialCoefficient u n) 2 μ := by
  have h := (memLp_referenceRadialCoefficient_prod
    (n07aAngularZeroExtension_memLp hu) n).const_mul 2
  apply (memLp_congr_ae ?_).mp h
  exact Eventually.of_forall fun r => (n07aHalfRadialCoefficient_zeroExtension u n r).symm

/-- For a genuine periodic representative this is exactly the already
fixed physical coefficient, with no new normalization. -/
theorem n07aHalfRadialCoefficient_eq_reference {u : PolarPoint → ℝ} (n : ℕ) (r : ℝ)
    (hp : Function.Periodic (fun θ => u (r, θ)) Real.pi)
    (hu : IntervalIntegrable (fun θ => u (r, θ)) volume 0 (2 * Real.pi)) :
    n07aHalfRadialCoefficient u n r = referenceRadialCoefficient u n r := by
  have hper : Function.Periodic (fun θ => u (r, θ) * referenceAngularBasis n θ) Real.pi :=
    hp.mul (referenceAngularBasis_periodic n)
  have hi := hu.mul_continuousOn (contDiff_referenceAngularBasis n).continuous.continuousOn
  have h := radialAngularMean_eq_halfPeriod hper hi
  simpa only [referenceRadialCoefficient, referenceAngularCoefficient,
    n07aHalfRadialCoefficient, intervalIntegral.integral_of_le Real.pi_pos.le] using h.symm

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aCanonicalRadialCoefficient_memLp (u : CanonicalL2 S K m) (n : ℕ) :
    MemLp (n07aHalfRadialCoefficient u n) 2
      (volume.restrict (Ioo (K.left m) (K.right m))) := by
  let f : PolarPoint → ℝ := u
  have hu : MemLp f 2 (canonicalMeasure S K m) := Lp.memLp u
  rw [n07aCanonicalMeasure_eq_prod] at hu
  exact n07aHalfRadialCoefficient_memLp hu n

theorem n07a_canonical_basis_test {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (K.left m) (K.right m)) (n : ℕ) :
    CanonicalTest S K m (fun p => φ p.1 * referenceAngularBasis n p.2) := by
  refine ⟨(hφ.comp contDiff_fst).mul ((contDiff_referenceAngularBasis n).comp contDiff_snd),
    ?_, tsupport φ, hc, hs, ?_⟩
  · intro p
    simp only [Prod.fst_add, Prod.snd_add, add_zero, referenceAngularBasis_periodic n p.2]
  · intro r hr θ
    dsimp only
    rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]

theorem n07a_canonical_basis_radial {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (p : PolarPoint) :
    mixedDerivative 1 0 (fun q => φ q.1 * referenceAngularBasis n q.2) p =
      deriv φ p.1 * referenceAngularBasis n p.2 := by
  simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one]
  exact ((hφ.differentiable (by simp) p.1).hasDerivAt.mul_const
    (referenceAngularBasis n p.2)).deriv

/-- Fubini identifies the actual separated test pairing. -/
theorem n07a_canonical_basis_pairing (u : CanonicalL2 S K m) (n : ℕ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (K.left m) (K.right m)) :
    (∫ p, u p * (φ p.1 * referenceAngularBasis n p.2) ∂canonicalMeasure S K m) =
      Real.pi * ∫ r in Ioo (K.left m) (K.right m), n07aHalfRadialCoefficient u n r * φ r := by
  let f : PolarPoint → ℝ := u
  have hi : Integrable (fun p => f p * (φ p.1 * referenceAngularBasis n p.2))
      (canonicalMeasure S K m) := (Lp.memLp u).integrable_mul
    (n07a_canonicalTest_memLp (n07a_canonical_basis_test hφ hc hs n))
  change (∫ p, f p * (φ p.1 * referenceAngularBasis n p.2) ∂canonicalMeasure S K m) =
    Real.pi * ∫ r in Ioo (K.left m) (K.right m), n07aHalfRadialCoefficient f n r * φ r
  rw [n07aCanonicalMeasure_eq_prod] at hi ⊢
  rw [integral_prod _ hi, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by
    dsimp only
    have he : (fun θ => f (r, θ) * (φ r * referenceAngularBasis n θ)) =
        (fun θ => (f (r, θ) * referenceAngularBasis n θ) * φ r) := by
      funext θ
      ring
    rw [he, integral_mul_const]
    unfold n07aHalfRadialCoefficient
    change _ = Real.pi * ((Real.pi⁻¹ *
      ∫ θ in Ioc (0 : ℝ) Real.pi, f (r, θ) * referenceAngularBasis n θ) * φ r)
    unfold angleMeasure
    field_simp [Real.pi_ne_zero]

/-- First canonical weak differentiation commutes with the genuine cosine
coefficient, including arbitrary choices of L² representatives. -/
theorem n07a_canonical_firstNormal_coefficient {u d : CanonicalL2 S K m}
    (hd : N07aWeakCanonicalMixedDerivative S K m u d 1 0) (n : ℕ) :
    HasIntervalWeakDerivative (K.left m) (K.right m)
      (n07aHalfRadialCoefficient u n) (n07aHalfRadialCoefficient d n) := by
  intro φ hφ hc hs
  have htest := n07a_canonical_basis_test hφ hc hs n
  have h := hd _ htest
  simp only [Nat.add_zero, pow_one, neg_one_mul, n07a_canonical_basis_radial hφ] at h
  have hder := (contDiff_infty_iff_deriv.mp hφ).2
  have hds := tsupport_deriv_subset.trans hs
  rw [n07a_canonical_basis_pairing d n hφ hc hs,
    n07a_canonical_basis_pairing u n hder hc.deriv hds] at h
  have he₀ : (∫ r in Ioo (K.left m) (K.right m),
      n07aHalfRadialCoefficient d n r * φ r) =
        ∫ r, n07aHalfRadialCoefficient d n r * φ r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hr (hs hh)), mul_zero]
  have he₁ : (∫ r in Ioo (K.left m) (K.right m),
      n07aHalfRadialCoefficient u n r * deriv φ r) =
        ∫ r, n07aHalfRadialCoefficient u n r * deriv φ r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hr (hds hh)), mul_zero]
  rw [he₀, he₁] at h
  nlinarith [Real.pi_pos]

end ContinuousFlexibility.Analysis
