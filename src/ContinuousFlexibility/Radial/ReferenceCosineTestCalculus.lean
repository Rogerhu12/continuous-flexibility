import ContinuousFlexibility.Radial.ReferenceCosineAnalysis
import ContinuousFlexibility.Radial.RadialHeight
import ContinuousFlexibility.Analysis.RootCompositionIntegral
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Actual cosine coefficients of smooth radial tests

Compact-interval parameter integration gives genuine smoothness and
commutation with radial derivatives. A compact radial support remains
a support for every angular coefficient. The angular variable of the
test need not be even or have period pi.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem reference_contDiff_radialPartial {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (radialPartial ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_radialPartial hψ.contDiffAt (by simp)

theorem reference_contDiff_angularPartial {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (angularPartial ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_angularPartial hψ.contDiffAt (by simp)

theorem referenceCircleCosine_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fun θ : ℝ => referenceCircleCosine n (θ : AddCircle Real.pi)) := by
  cases n with
  | zero =>
    simp only [referenceCircleCosine_zero]
    exact contDiff_const
  | succ n =>
    simp only [referenceCircleCosine_succ_coe]
    unfold Radial.cosineMode
    fun_prop

theorem referenceCosineCoefficient_eq_angularMean
    (ψ : PolarPoint → ℝ) (n : ℕ) (r : ℝ) :
    referenceCosineCoefficient ψ n r =
      radialAngularMean (fun θ =>
        ψ (r, θ) * referenceCircleCosine n (θ : AddCircle Real.pi)) := by
  exact integral_referenceAngularMeasure _

theorem contDiff_radialAngularMean {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (fun r => radialAngularMean (fun θ => ψ (r, θ))) := by
  change ContDiff ℝ ∞
    (fun r => (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ψ (r, θ))
  exact contDiff_const.mul
    (Analysis.contDiff_intervalIntegral_of_contDiff hψ 0 (2 * Real.pi))

/-- Differentiate the genuine angular integral, not a formal coefficient. -/
theorem hasDerivAt_radialAngularMean {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) :
    HasDerivAt (fun s => radialAngularMean (fun θ => ψ (s, θ)))
      (radialAngularMean (fun θ => radialPartial ψ (r, θ))) r := by
  have hψ' : ContDiff ℝ ∞ (fun q : PolarPoint =>
      (fderiv ℝ ψ q).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) :=
    (contDiff_infty_iff_fderiv.mp hψ).2.clm_comp contDiff_const
  have hi : IntervalIntegrable (fun θ : ℝ =>
      (fderiv ℝ ψ (r, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ))
      volume 0 (2 * Real.pi) :=
    (hψ'.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hd := (Analysis.hasFDerivAt_intervalIntegral_of_contDiff
    hψ 0 (2 * Real.pi) r).hasDerivAt
  rw [ContinuousLinearMap.intervalIntegral_apply hi] at hd
  change HasDerivAt (fun s => ∫ θ in (0 : ℝ)..2 * Real.pi, ψ (s, θ))
    (∫ θ in (0 : ℝ)..2 * Real.pi, radialPartial ψ (r, θ)) r at hd
  exact hd.const_mul ((2 * Real.pi)⁻¹)

theorem contDiff_radialAngularMean_mul {ψ : PolarPoint → ℝ} {k : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hk : ContDiff ℝ ∞ k) :
    ContDiff ℝ ∞ (fun r => radialAngularMean (fun θ => ψ (r, θ) * k θ)) :=
  contDiff_radialAngularMean (hψ.mul (hk.comp contDiff_snd))

theorem hasDerivAt_radialAngularMean_mul {ψ : PolarPoint → ℝ} {k : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hk : ContDiff ℝ ∞ k) (r : ℝ) :
    HasDerivAt (fun s => radialAngularMean (fun θ => ψ (s, θ) * k θ))
      (radialAngularMean (fun θ => radialPartial ψ (r, θ) * k θ)) r := by
  let G : PolarPoint → ℝ := fun x => ψ x * k x.2
  have hG : ContDiff ℝ ∞ G := hψ.mul (hk.comp contDiff_snd)
  have heq : (fun θ => radialPartial G (r, θ)) =
      (fun θ => radialPartial ψ (r, θ) * k θ) := by
    funext θ
    exact (Radial.hasDerivAt_radialSlice (hG.differentiable (by simp) (r, θ))).unique
      ((Radial.hasDerivAt_radialSlice (hψ.differentiable (by simp) (r, θ))).mul_const (k θ))
  have hd := hasDerivAt_radialAngularMean hG r
  rw [heq] at hd
  exact hd

theorem contDiff_referenceCosineCoefficient {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (n : ℕ) :
    ContDiff ℝ ∞ (referenceCosineCoefficient ψ n) := by
  have heq : referenceCosineCoefficient ψ n =
      (fun r => radialAngularMean (fun θ =>
        ψ (r, θ) * referenceCircleCosine n (θ : AddCircle Real.pi))) :=
    funext (referenceCosineCoefficient_eq_angularMean ψ n)
  rw [heq]
  exact contDiff_radialAngularMean_mul hψ (referenceCircleCosine_contDiff n)

theorem hasDerivAt_referenceCosineCoefficient {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (n : ℕ) (r : ℝ) :
    HasDerivAt (referenceCosineCoefficient ψ n)
      (referenceCosineCoefficient (radialPartial ψ) n r) r := by
  have hd := hasDerivAt_radialAngularMean_mul hψ (referenceCircleCosine_contDiff n) r
  simpa only [referenceCosineCoefficient, referenceCosineCoeff,
    integral_referenceAngularMeasure] using hd

theorem deriv_referenceCosineCoefficient {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (n : ℕ) :
    deriv (referenceCosineCoefficient ψ n) =
      referenceCosineCoefficient (radialPartial ψ) n := by
  funext r
  exact (hasDerivAt_referenceCosineCoefficient hψ n r).deriv

theorem deriv_deriv_referenceCosineCoefficient {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (n : ℕ) :
    deriv (deriv (referenceCosineCoefficient ψ n)) =
      referenceCosineCoefficient (radialPartial (radialPartial ψ)) n := by
  rw [deriv_referenceCosineCoefficient hψ n,
    deriv_referenceCosineCoefficient (reference_contDiff_radialPartial hψ) n]

theorem referenceCosineCoefficient_eq_zero_of_radial_support
    {K : Set ℝ} {ψ : PolarPoint → ℝ}
    (hs : ∀ r ∉ K, ∀ θ, ψ (r, θ) = 0) (n : ℕ) {r : ℝ} (hr : r ∉ K) :
    referenceCosineCoefficient ψ n r = 0 := by
  unfold referenceCosineCoefficient referenceCosineCoeff
  simp only [hs r hr, zero_mul, integral_zero]

/-- Every actual test coefficient is an admissible smooth, strictly interior radial test. -/
theorem RadialTest.cosineCoefficient_test {D : ReferenceData}
    {ψ : PolarPoint → ℝ} (hψ : RadialTest D ψ) (n : ℕ) :
    ContDiff ℝ ∞ (referenceCosineCoefficient ψ n) ∧
      HasCompactSupport (referenceCosineCoefficient ψ n) ∧
      tsupport (referenceCosineCoefficient ψ n) ⊆ radialCore D := by
  obtain ⟨hψ, _, K, hK, hKcore, hs⟩ := hψ
  have hsub : tsupport (referenceCosineCoefficient ψ n) ⊆ K := by
    change closure (Function.support (referenceCosineCoefficient ψ n)) ⊆ K
    apply closure_minimal ?_ hK.isClosed
    intro r hr
    by_contra hrK
    exact hr (referenceCosineCoefficient_eq_zero_of_radial_support hs n hrK)
  refine ⟨contDiff_referenceCosineCoefficient hψ n, ?_, hsub.trans hKcore⟩
  change IsCompact (closure (Function.support (referenceCosineCoefficient ψ n)))
  exact hK.of_isClosed_subset isClosed_closure hsub

end ContinuousFlexibility.Statements
