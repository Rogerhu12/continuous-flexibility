import ContinuousFlexibility.Analysis.N07aCanonicalOpenTests
import ContinuousFlexibility.Analysis.N07aWeakDivergenceEquation

/-!
# Interior Green pairing on the actual canonical cylinder

The coefficients and the smooth comparison field need only be smooth on
the open canonical piece. Every differentiated product contains a compact
canonical test, so no boundary trace or global extension is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonicalOpen_integrable_mul_test {f φ : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hfp : ∀ p ∈ canonicalOpen S K m, f (p + (0, Real.pi)) = f p)
    (hφ : CanonicalTest S K m φ) :
    Integrable (fun p => f p * φ p) (canonicalMeasure S K m) := by
  let := n07a_canonicalMeasure_finite S K m
  exact (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hφ hf hfp)).integrable
    (by norm_num)

theorem n07a_canonicalTest_integral_first_eq_zero {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) (j : Fin 2) :
    (∫ p, mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 φ p
      ∂canonicalMeasure S K m) = 0 := by
  have h := spaces_integral_mixedDerivative_mul (f := fun _ : PolarPoint => (1 : ℝ))
    contDiff_const (fun _ => rfl) (n07a_canonicalTest_isCylinderTest hφ)
    (n07aFirstOrder j).1 (n07aFirstOrder j).2
  have hconst : mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2
      (fun _ : PolarPoint => (1 : ℝ)) = fun _ => 0 := by
    funext p
    fin_cases j <;> simp [n07aFirstOrder, mixedDerivative, iteratedDeriv_one]
  rw [hconst] at h
  simp only [zero_mul, integral_zero, one_mul, n07aFirstOrder_sum,
    pow_one, neg_one_mul] at h
  rw [n07a_canonicalIntegral_eq_cylinder (fun p hp =>
    n07a_canonicalTest_zero_outside (n07a_canonicalTest_mixedDerivative hφ _ _) hp)]
  exact neg_eq_zero.mp h.symm

/-- First integration by parts for a genuinely interior smooth coefficient.
The open coefficient times the compact test is itself a global test. -/
theorem n07a_canonicalOpen_first_pairing {f φ : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hfp : ∀ p ∈ canonicalOpen S K m, f (p + (0, Real.pi)) = f p)
    (hφ : CanonicalTest S K m φ) (j : Fin 2) :
    (∫ p, mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 f p * φ p
      ∂canonicalMeasure S K m) =
      -(∫ p, f p * mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 φ p
        ∂canonicalMeasure S K m) := by
  have hdf := contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hf
    (n07aFirstOrder j).1 (n07aFirstOrder j).2
  have hdfp := n07a_mixedDerivative_periodic_on hfp
    (n07aFirstOrder j).1 (n07aFirstOrder j).2
  have hi₁ := n07a_canonicalOpen_integrable_mul_test hdf hdfp hφ
  have hi₂ := n07a_canonicalOpen_integrable_mul_test hf hfp
    (n07a_canonicalTest_mixedDerivative hφ (n07aFirstOrder j).1 (n07aFirstOrder j).2)
  have hz := n07a_canonicalTest_integral_first_eq_zero
    (n07a_canonicalTest_mul_on hφ hf hfp) j
  have he := n07a_mixedDerivative_first_mul_on hf hφ.1.contDiffOn j
  have hae : mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2
      (fun p => f p * φ p) =ᵐ[canonicalMeasure S K m]
      fun p => mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 f p * φ p +
        f p * mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 φ p :=
    n07a_canonicalOpen_ae.mono (fun p hp => he hp)
  rw [integral_congr_ae hae, integral_add hi₁ hi₂] at hz
  linarith only [hz]

theorem n07a_open_radialPartial_eq {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m)) :
    EqOn (radialPartial f) (mixedDerivative 1 0 f) (canonicalOpen S K m) := by
  intro p hp
  simpa only [spaces_mixedDerivative_zero, zero_add] using
    n07a_radialPartial_mixedDerivative_on (isOpen_Ioo.prod isOpen_univ) hf 0 0 hp

theorem n07a_open_angularPartial_eq {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m)) :
    EqOn (angularPartial f) (mixedDerivative 0 1 f) (canonicalOpen S K m) := by
  intro p hp
  simpa only [spaces_mixedDerivative_zero, zero_add] using
    n07a_angularPartial_zero_mixedDerivative_on (isOpen_Ioo.prod isOpen_univ) hf 0 hp

theorem n07a_open_divergence_mixed (A : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ A.a (canonicalOpen S K m))
    (hb : ContDiffOn ℝ ∞ A.b (canonicalOpen S K m))
    (hc : ContDiffOn ℝ ∞ A.c (canonicalOpen S K m))
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m)) :
    EqOn (divergenceOperator A f)
      (fun p => mixedDerivative 1 0
          (fun q => A.a q * mixedDerivative 1 0 f q + A.b q * mixedDerivative 0 1 f q) p +
        mixedDerivative 0 1
          (fun q => A.b q * mixedDerivative 1 0 f q + A.c q * mixedDerivative 0 1 f q) p)
      (canonicalOpen S K m) := by
  have hfr := contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hf 1 0
  have hft := contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hf 0 1
  intro p hp
  have hnear := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hr : (fun q => A.a q * radialPartial f q + A.b q * angularPartial f q) =ᶠ[𝓝 p]
      (fun q => A.a q * mixedDerivative 1 0 f q + A.b q * mixedDerivative 0 1 f q) := by
    filter_upwards [hnear] with q hq
    rw [n07a_open_radialPartial_eq hf hq, n07a_open_angularPartial_eq hf hq]
  have ht : (fun q => A.b q * radialPartial f q + A.c q * angularPartial f q) =ᶠ[𝓝 p]
      (fun q => A.b q * mixedDerivative 1 0 f q + A.c q * mixedDerivative 0 1 f q) := by
    filter_upwards [hnear] with q hq
    rw [n07a_open_radialPartial_eq hf hq, n07a_open_angularPartial_eq hf hq]
  have hr' := congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0))
    (hr.fderiv_eq (𝕜 := ℝ))
  have ht' := congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1))
    (ht.fderiv_eq (𝕜 := ℝ))
  exact (congrArg₂ (· + ·) hr' ht').trans (congrArg₂ (· + ·)
    (n07a_open_radialPartial_eq ((ha.mul hfr).add (hb.mul hft)) hp)
    (n07a_open_angularPartial_eq ((hb.mul hfr).add (hc.mul hft)) hp))

/-- Green's identity uses the same symmetric divergence coefficients on
both sides, with no global extension of the smooth comparison field. -/
theorem n07a_canonicalOpen_green (A : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ A.a (canonicalOpen S K m))
    (hb : ContDiffOn ℝ ∞ A.b (canonicalOpen S K m))
    (hc : ContDiffOn ℝ ∞ A.c (canonicalOpen S K m))
    (hap : ∀ p ∈ canonicalOpen S K m, A.a (p + (0, Real.pi)) = A.a p)
    (hbp : ∀ p ∈ canonicalOpen S K m, A.b (p + (0, Real.pi)) = A.b p)
    (hcp : ∀ p ∈ canonicalOpen S K m, A.c (p + (0, Real.pi)) = A.c p)
    {f φ : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hfp : ∀ p ∈ canonicalOpen S K m, f (p + (0, Real.pi)) = f p)
    (hφ : CanonicalTest S K m φ) :
    (∫ p, f p * divergenceOperator A φ p ∂canonicalMeasure S K m) =
      ∫ p, divergenceOperator A f p * φ p ∂canonicalMeasure S K m := by
  let fr := mixedDerivative 1 0 f
  let ft := mixedDerivative 0 1 f
  let pr := mixedDerivative 1 0 φ
  let pt := mixedDerivative 0 1 φ
  let wr := fun p => A.a p * fr p + A.b p * ft p
  let wt := fun p => A.b p * fr p + A.c p * ft p
  let qr := fun p => A.a p * pr p + A.b p * pt p
  let qt := fun p => A.b p * pr p + A.c p * pt p
  have hfr := contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hf 1 0
  have hft := contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hf 0 1
  have hfrp := n07a_mixedDerivative_periodic_on hfp 1 0
  have hftp := n07a_mixedDerivative_periodic_on hfp 0 1
  have hpr := n07a_canonicalTest_mixedDerivative hφ 1 0
  have hpt := n07a_canonicalTest_mixedDerivative hφ 0 1
  have hwr : ContDiffOn ℝ ∞ wr (canonicalOpen S K m) := (ha.mul hfr).add (hb.mul hft)
  have hwt : ContDiffOn ℝ ∞ wt (canonicalOpen S K m) := (hb.mul hfr).add (hc.mul hft)
  have hwrp : ∀ p ∈ canonicalOpen S K m, wr (p + (0, Real.pi)) = wr p := by
    intro p hp
    dsimp only [wr, fr, ft]
    rw [hap p hp, hbp p hp, hfrp p hp, hftp p hp]
  have hwtp : ∀ p ∈ canonicalOpen S K m, wt (p + (0, Real.pi)) = wt p := by
    intro p hp
    dsimp only [wt, fr, ft]
    rw [hbp p hp, hcp p hp, hfrp p hp, hftp p hp]
  have hqr : CanonicalTest S K m qr := n07a_canonicalTest_add
    (n07a_canonicalTest_mul_on hpr ha hap) (n07a_canonicalTest_mul_on hpt hb hbp)
  have hqt : CanonicalTest S K m qt := n07a_canonicalTest_add
    (n07a_canonicalTest_mul_on hpr hb hbp) (n07a_canonicalTest_mul_on hpt hc hcp)
  have h₁ := n07a_canonicalOpen_first_pairing hf hfp hqr (0 : Fin 2)
  have h₂ := n07a_canonicalOpen_first_pairing hf hfp hqt (1 : Fin 2)
  have h₃ := n07a_canonicalOpen_first_pairing hwr hwrp hφ (0 : Fin 2)
  have h₄ := n07a_canonicalOpen_first_pairing hwt hwtp hφ (1 : Fin 2)
  simp [n07aFirstOrder] at h₁ h₂ h₃ h₄
  have heφ : (fun p => f p * divergenceOperator A φ p) =ᵐ[canonicalMeasure S K m]
      fun p => f p * mixedDerivative 1 0 qr p + f p * mixedDerivative 0 1 qt p := by
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    rw [n07a_open_divergence_mixed A ha hb hc hφ.1.contDiffOn hp]
    exact mul_add _ _ _
  have hef : (fun p => divergenceOperator A f p * φ p) =ᵐ[canonicalMeasure S K m]
      fun p => mixedDerivative 1 0 wr p * φ p + mixedDerivative 0 1 wt p * φ p := by
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    rw [n07a_open_divergence_mixed A ha hb hc hf hp]
    exact add_mul _ _ _
  have hi₁ := n07a_canonicalOpen_integrable_mul_test hf hfp
    (n07a_canonicalTest_mixedDerivative hqr 1 0)
  have hi₂ := n07a_canonicalOpen_integrable_mul_test hf hfp
    (n07a_canonicalTest_mixedDerivative hqt 0 1)
  have hi₃ := n07a_canonicalOpen_integrable_mul_test
    (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hwr 1 0)
    (n07a_mixedDerivative_periodic_on hwrp 1 0) hφ
  have hi₄ := n07a_canonicalOpen_integrable_mul_test
    (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hwt 0 1)
    (n07a_mixedDerivative_periodic_on hwtp 0 1) hφ
  have henergy : (∫ p, fr p * qr p ∂canonicalMeasure S K m) +
      (∫ p, ft p * qt p ∂canonicalMeasure S K m) =
      (∫ p, wr p * pr p ∂canonicalMeasure S K m) +
      (∫ p, wt p * pt p ∂canonicalMeasure S K m) := by
    rw [← integral_add (n07a_canonicalOpen_integrable_mul_test hfr hfrp hqr)
      (n07a_canonicalOpen_integrable_mul_test hft hftp hqt),
      ← integral_add (n07a_canonicalOpen_integrable_mul_test hwr hwrp hpr)
        (n07a_canonicalOpen_integrable_mul_test hwt hwtp hpt)]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by dsimp only [qr, qt, wr, wt]; ring
  rw [integral_congr_ae heφ, integral_add hi₁ hi₂,
    integral_congr_ae hef, integral_add hi₃ hi₄]
  linarith only [h₁, h₂, h₃, h₄, henergy]

end ContinuousFlexibility.Analysis
