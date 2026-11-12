import ContinuousFlexibility.Analysis.N07aCanonicalWeakJets
import ContinuousFlexibility.Analysis.SpacesHeightAlgebra

/-!+# Coefficient multiplication on canonical weak jets

The multiplier is an actual continuous linear operator on the prescribed
canonical L² class.  Its product rule is proved by testing the weak
equation against the coefficient times a compact radial test.  The same
proof covers either coordinate direction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonical_memLp_mul {χ : PolarPoint → ℝ}
    (hχ : AEStronglyMeasurable χ (canonicalMeasure S K m)) {A : ℝ}
    (hA : ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A)
    (u : CanonicalL2 S K m) :
    MemLp (fun p => χ p * u p) 2 (canonicalMeasure S K m) := by
  apply (Lp.memLp u).of_le_mul (c := A) (hχ.mul (Lp.aestronglyMeasurable u))
  filter_upwards [hA] with p hp
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

def n07aCanonicalMul (χ : PolarPoint → ℝ)
    (hχ : AEStronglyMeasurable χ (canonicalMeasure S K m)) (A : ℝ)
    (hA : ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A)
    (u : CanonicalL2 S K m) : CanonicalL2 S K m :=
  (n07a_canonical_memLp_mul hχ hA u).toLp (fun p => χ p * u p)

theorem n07aCanonicalMul_ae (χ : PolarPoint → ℝ)
    (hχ : AEStronglyMeasurable χ (canonicalMeasure S K m)) (A : ℝ)
    (hA : ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A)
    (u : CanonicalL2 S K m) :
    (n07aCanonicalMul χ hχ A hA u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      (fun p => χ p * u p) :=
  MemLp.coeFn_toLp _

def n07aCanonicalMultiplier (χ : PolarPoint → ℝ)
    (hχ : AEStronglyMeasurable χ (canonicalMeasure S K m)) (A : ℝ)
    (hA : ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A) :
    CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m := by
  let M : CanonicalL2 S K m →ₗ[ℝ] CanonicalL2 S K m :=
    { toFun := n07aCanonicalMul χ hχ A hA
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [n07aCanonicalMul_ae χ hχ A hA (u + v),
          n07aCanonicalMul_ae χ hχ A hA u, n07aCanonicalMul_ae χ hχ A hA v,
          Lp.coeFn_add u v,
          Lp.coeFn_add (n07aCanonicalMul χ hχ A hA u) (n07aCanonicalMul χ hχ A hA v)]
          with p hsum hu hv hp hprod
        rw [hsum, hprod, hp]
        simp only [Pi.add_apply]
        rw [hu, hv]
        ring
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [n07aCanonicalMul_ae χ hχ A hA (c • u),
          n07aCanonicalMul_ae χ hχ A hA u, Lp.coeFn_smul c u,
          Lp.coeFn_smul c (n07aCanonicalMul χ hχ A hA u)] with p hmul hu hp hprod
        simp only [RingHom.id_apply]
        rw [hmul, hprod, hp]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hu]
        ring }
  apply M.mkContinuous A
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [n07aCanonicalMul_ae χ hχ A hA u, hA] with p hp hbound
  change ‖n07aCanonicalMul χ hχ A hA u p‖ ≤ A * ‖u p‖
  rw [hp]
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_right hbound (abs_nonneg (u p))

theorem n07aCanonicalMultiplier_ae (χ : PolarPoint → ℝ)
    (hχ : AEStronglyMeasurable χ (canonicalMeasure S K m)) (A : ℝ)
    (hA : ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A)
    (u : CanonicalL2 S K m) :
    (n07aCanonicalMultiplier χ hχ A hA u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      (fun p => χ p * u p) :=
  n07aCanonicalMul_ae χ hχ A hA u

theorem n07aCanonicalMultiplier_norm_le (χ : PolarPoint → ℝ)
    (hχ : AEStronglyMeasurable χ (canonicalMeasure S K m)) (A : ℝ)
    (hA : ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A)
    (u : CanonicalL2 S K m) :
    ‖n07aCanonicalMultiplier χ hχ A hA u‖ ≤ A * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [n07aCanonicalMultiplier_ae χ hχ A hA u, hA] with p hp hbound
  rw [hp]
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_right hbound (abs_nonneg (u p))

theorem n07aCanonicalMultiplier_pairing (χ : PolarPoint → ℝ)
    (hχ : AEStronglyMeasurable χ (canonicalMeasure S K m)) (A : ℝ)
    (hA : ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A)
    (u : CanonicalL2 S K m) (φ : PolarPoint → ℝ) :
    (∫ p, n07aCanonicalMultiplier χ hχ A hA u p * φ p ∂canonicalMeasure S K m) =
      ∫ p, u p * (χ p * φ p) ∂canonicalMeasure S K m := by
  apply integral_congr_ae
  filter_upwards [n07aCanonicalMultiplier_ae χ hχ A hA u] with p hp
  rw [hp]
  ring

/-- Either coordinate derivative, still expressed using the frozen
mixed-derivative notation. -/
def n07aFirstOrder (j : Fin 2) : ℕ × ℕ := if j = 0 then (1, 0) else (0, 1)

theorem n07aFirstOrder_sum (j : Fin 2) : (n07aFirstOrder j).1 + (n07aFirstOrder j).2 = 1 := by
  fin_cases j <;> simp [n07aFirstOrder]

theorem n07a_mixedDerivative_first_mul {χ φ : PolarPoint → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hφ : ContDiff ℝ ∞ φ) (j : Fin 2) :
    mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 (fun p => χ p * φ p) =
      fun p => mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ p * φ p +
        χ p * mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 φ p := by
  funext p
  fin_cases j <;> simp only [n07aFirstOrder, Fin.isValue, ↓reduceIte, Prod.fst, Prod.snd]
  all_goals
    rw [spaces_mixedDerivative_mul hχ hφ]
    simp [Finset.sum_range_succ, mixedDerivative, iteratedDeriv_zero]
    <;> ring

/-- The weak first-order product rule, in either coordinate direction. -/
theorem n07a_weakCanonical_first_product {χ : PolarPoint → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχp : Function.Periodic χ (0, Real.pi))
    (j : Fin 2) (A B : ℝ)
    (hA : ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A)
    (hB : ∀ᵐ p ∂canonicalMeasure S K m,
      |mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ p| ≤ B)
    {f g : CanonicalL2 S K m}
    (hfg : N07aWeakCanonicalMixedDerivative S K m f g
      (n07aFirstOrder j).1 (n07aFirstOrder j).2) :
    N07aWeakCanonicalMixedDerivative S K m
      (n07aCanonicalMultiplier χ hχ.continuous.aestronglyMeasurable A hA f)
      (n07aCanonicalMultiplier χ hχ.continuous.aestronglyMeasurable A hA g +
        n07aCanonicalMultiplier
          (mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ)
          (contDiff_mixedDerivative hχ _ _).continuous.aestronglyMeasurable B hB f)
      (n07aFirstOrder j).1 (n07aFirstOrder j).2 := by
  let dχ := mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ
  have hdχ : ContDiff ℝ ∞ dχ := contDiff_mixedDerivative hχ _ _
  have hdχp : Function.Periodic dχ (0, Real.pi) := by
    have hper (r : ℝ) : Function.Periodic (fun θ => χ (r, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hχp (r, θ)
    rintro ⟨r, θ⟩
    simpa only [Prod.mk_add_mk, add_zero] using
      mixedDerivative_angular_periodic hper (n07aFirstOrder j).1 (n07aFirstOrder j).2 r θ
  intro φ hφ
  let dφ := mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 φ
  have hdφ := n07a_canonicalTest_mixedDerivative hφ (n07aFirstOrder j).1 (n07aFirstOrder j).2
  have hi₁ : Integrable (fun p => f p * (dχ p * φ p)) (canonicalMeasure S K m) :=
    (Lp.memLp f).integrable_mul (n07a_canonicalTest_memLp (n07a_canonicalTest_mul hφ hdχ hdχp))
  have hi₂ : Integrable (fun p => f p * (χ p * dφ p)) (canonicalMeasure S K m) :=
    (Lp.memLp f).integrable_mul (n07a_canonicalTest_memLp (n07a_canonicalTest_mul hdφ hχ hχp))
  have htest := hfg (fun p => χ p * φ p) (n07a_canonicalTest_mul hφ hχ hχp)
  rw [n07aFirstOrder_sum, pow_one, neg_one_mul,
    n07a_mixedDerivative_first_mul hχ hφ.1] at htest
  have hsplit :
      (∫ p, f p * (dχ p * φ p + χ p * dφ p) ∂canonicalMeasure S K m) =
        (∫ p, f p * (dχ p * φ p) ∂canonicalMeasure S K m) +
          ∫ p, f p * (χ p * dφ p) ∂canonicalMeasure S K m := by
    simp_rw [mul_add]
    exact integral_add hi₁ hi₂
  change (∫ p, g p * (χ p * φ p) ∂canonicalMeasure S K m) =
    -(∫ p, f p * (dχ p * φ p + χ p * dφ p) ∂canonicalMeasure S K m) at htest
  rw [hsplit] at htest
  rw [← n07aCanonicalTestPairing_apply φ (n07a_canonicalTest_memLp hφ), map_add,
    n07aCanonicalTestPairing_apply, n07aCanonicalTestPairing_apply,
    n07aCanonicalMultiplier_pairing, n07aCanonicalMultiplier_pairing,
    n07aFirstOrder_sum, pow_one, neg_one_mul, n07aCanonicalMultiplier_pairing]
  change (∫ p, g p * (χ p * φ p) ∂canonicalMeasure S K m) +
    (∫ p, f p * (dχ p * φ p) ∂canonicalMeasure S K m) =
      -(∫ p, f p * (χ p * dφ p) ∂canonicalMeasure S K m)
  linarith only [htest]

end ContinuousFlexibility.Analysis
