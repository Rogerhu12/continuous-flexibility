module

public import ContinuousFlexibility.Radial.ReferenceCosineCoefficients
public import ContinuousFlexibility.Radial.ReferenceCosineParseval
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Partial angular Parseval with the radial variable kept in L²

The existing actual even-cosine Parseval theorem is integrated against an
arbitrary radial measure. No periodic extension in the radial variable is
introduced. The resulting sequence consists of the genuine radial L²
classes of the angular coefficients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Radial ContinuousFlexibility.Statements
open scoped ENNReal Topology

variable {μ : Measure ℝ} [SFinite μ] {u : PolarPoint → ℝ}

/-- Angular Parseval and Fubini give the actual radial energy series. -/
theorem n07a_hasSum_integral_radialCoefficient_sq
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))))
    (hp : ∀ᵐ r ∂μ, Function.Periodic (fun θ => u (r, θ)) Real.pi)
    (he : ∀ᵐ r ∂μ, Function.Even (fun θ => u (r, θ))) :
    HasSum (fun n : ℕ => ∫ r, referenceRadialCoefficient u n r ^ 2 ∂μ)
      ((2 * Real.pi)⁻¹ *
        ∫ p, u p ^ 2 ∂μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  let energy : ℝ → ℝ := fun r => radialAngularMean (fun θ => u (r, θ) ^ 2)
  have hsum : ∀ᵐ r ∂μ, HasSum
      (fun n : ℕ => referenceRadialCoefficient u n r ^ 2) (energy r) := by
    filter_upwards [memLp_two_prod_sections hu, hp, he] with r hr hpr her
    exact hasSum_sq_referenceAngularCoefficient hr hpr her
  have henergy : Integrable energy μ := integrable_radialAngularMean_sq hu
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun r => referenceRadialCoefficient u n r ^ 2) μ :=
    (aestronglyMeasurable_referenceRadialCoefficient hu.aestronglyMeasurable n).pow 2
  have htotal : Integrable
      (fun r => ∑' n : ℕ, referenceRadialCoefficient u n r ^ 2) μ :=
    henergy.congr (hsum.mono fun _ hr => hr.tsum_eq.symm)
  have hi := hasSum_integral_of_dominated_convergence
    (fun (n : ℕ) (r : ℝ) => referenceRadialCoefficient u n r ^ 2)
    hmeas (fun n => Eventually.of_forall fun r => by
      rw [Real.norm_of_nonneg (sq_nonneg _)])
    (hsum.mono fun _ hr => hr.summable) htotal hsum
  have heq : (∫ r, energy r ∂μ) = (2 * Real.pi)⁻¹ *
      ∫ p, u p ^ 2 ∂μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    simp only [energy, radialAngularMean,
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
    rw [integral_const_mul, ← integral_prod _ hu.integrable_sq]
  exact heq ▸ hi

/-- The radial coefficient is retained as its actual prescribed L² class. -/
def n07aRadialCoefficientLp
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))))
    (n : ℕ) : Lp ℝ 2 μ :=
  (memLp_referenceRadialCoefficient_prod hu n).toLp (referenceRadialCoefficient u n)

theorem n07aRadialCoefficientLp_ae
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))))
    (n : ℕ) :
    (n07aRadialCoefficientLp hu n : ℝ → ℝ) =ᵐ[μ] referenceRadialCoefficient u n :=
  MemLp.coeFn_toLp _

theorem n07aRadialCoefficientLp_norm_sq
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))))
    (n : ℕ) :
    ‖n07aRadialCoefficientLp hu n‖ ^ 2 =
      ∫ r, referenceRadialCoefficient u n r ^ 2 ∂μ :=
  reference_memLp_norm_sq_eq_integral (memLp_referenceRadialCoefficient_prod hu n)

theorem n07aRadialCoefficientLp_memℓp
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))))
    (hp : ∀ᵐ r ∂μ, Function.Periodic (fun θ => u (r, θ)) Real.pi)
    (he : ∀ᵐ r ∂μ, Function.Even (fun θ => u (r, θ))) :
    Memℓp (n07aRadialCoefficientLp hu) 2 := by
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, n07aRadialCoefficientLp_norm_sq] using
    (n07a_hasSum_integral_radialCoefficient_sq hu hp he).summable

/-- The whole partial angular transform, with values in radial L². -/
def n07aRadialCosineSequence
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))))
    (hp : ∀ᵐ r ∂μ, Function.Periodic (fun θ => u (r, θ)) Real.pi)
    (he : ∀ᵐ r ∂μ, Function.Even (fun θ => u (r, θ))) :
    lp (fun _ : ℕ => Lp ℝ 2 μ) 2 :=
  ⟨n07aRadialCoefficientLp hu, n07aRadialCoefficientLp_memℓp hu hp he⟩

theorem n07aRadialCosineSequence_apply
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))))
    (hp : ∀ᵐ r ∂μ, Function.Periodic (fun θ => u (r, θ)) Real.pi)
    (he : ∀ᵐ r ∂μ, Function.Even (fun θ => u (r, θ))) (n : ℕ) :
    n07aRadialCosineSequence hu hp he n = n07aRadialCoefficientLp hu n := rfl

/-- This equality is the exact partial Parseval normalization. -/
theorem n07aRadialCosineSequence_norm_sq
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))))
    (hp : ∀ᵐ r ∂μ, Function.Periodic (fun θ => u (r, θ)) Real.pi)
    (he : ∀ᵐ r ∂μ, Function.Even (fun θ => u (r, θ))) :
    ‖n07aRadialCosineSequence hu hp he‖ ^ 2 =
      (2 * Real.pi)⁻¹ *
        ∫ p, u p ^ 2 ∂μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (n07aRadialCosineSequence hu hp he)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, n07aRadialCosineSequence_apply,
    n07aRadialCoefficientLp_norm_sq] at hn
  exact hn.trans (n07a_hasSum_integral_radialCoefficient_sq hu hp he).tsum_eq

end ContinuousFlexibility.Analysis
