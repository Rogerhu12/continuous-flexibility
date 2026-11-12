import ContinuousFlexibility.Analysis.N07aAngularDivergencePrimitive
import ContinuousFlexibility.Analysis.N07aAngularPhysicalCoefficients
import ContinuousFlexibility.Analysis.N07aOpenNormalBootstrap
import ContinuousFlexibility.Analysis.N07aOpenDistributionFlux
import ContinuousFlexibility.Analysis.N07aCanonicalRepresentationPairing

/-!
# The actual interior distribution equation supplies every weak jet

The coefficient functions are only smooth on the open strip. Products
with compact tests are genuine global tests, so the first weak radial
and angular jets determine the actual flux equation without extending a
coefficient across either radial endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- The source can be a genuine globally smooth periodic function with
no radial compact support. The test supplies the needed compactness. -/
theorem n07a_smoothCanonical_weakMixed {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (0, Real.pi)) (a b : ℕ) :
    N07aWeakCanonicalMixedDerivative S K m
      ((n07a_smoothCanonical_memLp hf).toLp f)
      ((n07a_smoothCanonical_memLp (contDiff_mixedDerivative hf a b)).toLp
        (mixedDerivative a b f)) a b := by
  intro φ hφ
  have hφd := n07a_canonicalTest_mixedDerivative hφ a b
  have hi (g : PolarPoint → ℝ) (hg : MemLp g 2 (canonicalMeasure S K m))
      (ψ : PolarPoint → ℝ) :
      (∫ p, hg.toLp g p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, g p * ψ p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hg] with p hp
    rw [hp]
  rw [hi, hi]
  rw [n07a_canonicalIntegral_eq_cylinder (fun p hp => by
    rw [n07a_canonicalTest_zero_outside hφ hp, mul_zero]),
    n07a_canonicalIntegral_eq_cylinder (fun p hp => by
      rw [n07a_canonicalTest_zero_outside hφd hp, mul_zero])]
  exact spaces_integral_mixedDerivative_mul hf hp (n07a_canonicalTest_isCylinderTest hφ) a b

def n07aCanonicalOne : CanonicalL2 S K m :=
  (n07a_smoothCanonical_memLp (S := S) (K := K) (m := m)
    (ψ := fun _ : PolarPoint => (1 : ℝ)) contDiff_const).toLp (fun _ => 1)

theorem n07aCanonicalOne_ae :
    (n07aCanonicalOne (S := S) (K := K) (m := m) : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] fun _ => 1 := by
  exact MemLp.coeFn_toLp _

theorem n07aCanonicalOne_normalRegular (n : ℕ) :
    N07aCanonicalNormalRegular S K m n07aCanonicalOne n := by
  intro a _ b
  exact ⟨_, n07a_smoothCanonical_weakMixed (f := fun _ : PolarPoint => (1 : ℝ))
    contDiff_const (fun _ => rfl) a b⟩

/-- The existing genuine source class of a bounded open coefficient has
every mixed weak derivative. No global smooth extension is used. -/
theorem N07aCanonicalOpenCoefficient.toLp_normalRegular
    (χ : N07aCanonicalOpenCoefficient S K m) (n : ℕ) :
    N07aCanonicalNormalRegular S K m χ.toLp n := by
  have he : χ.mul n07aCanonicalOne = χ.toLp := by
    apply Lp.ext
    filter_upwards [χ.mul_ae n07aCanonicalOne, χ.toLp_ae,
      n07aCanonicalOne_ae (S := S) (K := K) (m := m)] with p hp hχ h1
    simpa only [h1, mul_one, hχ] using hp
  rw [← he]
  exact χ.normalRegular n _ (n07aCanonicalOne_normalRegular n)

/-- The true distribution equation, its first normal graph, and the
actual source jets yield every weak mixed order of the same solution. -/
theorem n07a_openDistribution_allNormal
    (a b c ρ : N07aCanonicalOpenCoefficient S K m)
    (hinv : ∀ᵐ p ∂canonicalMeasure S K m, ρ.value p * a.value p = 1)
    {u F : CanonicalL2 S K m}
    (hu : N07aCanonicalNormalRegular S K m u 1)
    (hF : ∀ n, N07aCanonicalNormalRegular S K m F n)
    (heq : N07aCanonicalDistributionEquation S K m
      ⟨a.value, b.value, c.value⟩ u F) :
    ∀ n, N07aCanonicalNormalRegular S K m u n := by
  obtain ⟨ur, hr⟩ := hu 1 le_rfl 0
  obtain ⟨uθ, hθ⟩ := hu 0 (by omega) 1
  have hur : N07aCanonicalNormalRegular S K m ur 0 := hu.derivative hr
  have huθ : N07aCanonicalNormalRegular S K m uθ 0 := (hu.mono (by omega)).derivative hθ
  obtain ⟨urθ, hrθ⟩ := hur 0 le_rfl 1
  obtain ⟨uθθ, hθθ⟩ := huθ 0 le_rfl 1
  have hzero : (N07aCanonicalOpenCoefficient.constant (S := S) (K := K) (m := m) 0).mul u = 0 := by
    apply Lp.ext
    filter_upwards [(N07aCanonicalOpenCoefficient.constant (S := S) (K := K) (m := m) 0).mul_ae u,
      Lp.coeFn_zero (E := ℝ) (μ := canonicalMeasure S K m) (p := 2)] with p hp h0
    rw [h0]
    simpa only [N07aCanonicalOpenCoefficient.constant, zero_mul, Pi.zero_apply] using hp
  apply n07a_openWeak_divergenceBootstrap a b c ρ
    (N07aCanonicalOpenCoefficient.constant 0) hinv hr hθ hrθ hθθ hu hF
  rw [hzero, sub_zero]
  exact n07a_openDistribution_flux a b c hr hθ heq

end ContinuousFlexibility.Analysis
