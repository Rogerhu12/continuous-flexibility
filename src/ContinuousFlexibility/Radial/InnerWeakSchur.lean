import Mathlib.LinearAlgebra.Basic
import Mathlib.Data.Real.Basic

/-!
# Schur assembly with the actual weak boundary functional

The interface may be represented by its weak conormal functional, so
no additional Riesz-identification hypothesis is needed for the domain
argument. Local Dirichlet and Poisson realizations give a single solution
map. Both inverse identities follow from their source/trace identities,
the same interface equivalence, and local zero-Dirichlet uniqueness.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

section WeakSchur

variable {H V B C : Type*}
  [AddCommGroup H] [Module ℝ H] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]

/-- One assembled solution, using the outgoing flux of the actual
Dirichlet solution as the interface source. -/
def innerWeakSchurSolution (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V)
    (flux : V →ₗ[ℝ] C) (S : B ≃ₗ[ℝ] C) : H →ₗ[ℝ] V :=
  d + p.comp (S.symm.toLinearMap.comp (-(flux.comp d)))

theorem innerWeakSchurSolution_apply (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V)
    (flux : V →ₗ[ℝ] C) (S : B ≃ₗ[ℝ] C) (F : H) :
    innerWeakSchurSolution d p flux S F = d F + p (S.symm (-flux (d F))) := by
  simp only [innerWeakSchurSolution, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.neg_apply, LinearEquiv.coe_coe]

theorem innerWeakSchurSolution_source
    (L : V →ₗ[ℝ] H) (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V)
    (flux : V →ₗ[ℝ] C) (S : B ≃ₗ[ℝ] C)
    (hd : ∀ F, L (d F) = F) (hp : ∀ ξ, L (p ξ) = 0) (F : H) :
    L (innerWeakSchurSolution d p flux S F) = F := by
  rw [innerWeakSchurSolution_apply, map_add, hd, hp, add_zero]

theorem innerWeakSchurSolution_flux
    (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V)
    (flux : V →ₗ[ℝ] C) (S : B ≃ₗ[ℝ] C)
    (hp : ∀ ξ, flux (p ξ) = S ξ) (F : H) :
    flux (innerWeakSchurSolution d p flux S F) = 0 := by
  rw [innerWeakSchurSolution_apply, map_add, hp, S.apply_symm_apply, add_neg_cancel]

/-- A broken field is determined by its actual source and trace:
subtract the two local realizations and use local zero-endpoint
uniqueness. This decomposition is proved, not assumed. -/
theorem innerWeakSchur_decomposition
    (L : V →ₗ[ℝ] H) (tr : V →ₗ[ℝ] B)
    (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V)
    (hdL : ∀ F, L (d F) = F) (hdtr : ∀ F, tr (d F) = 0)
    (hpL : ∀ ξ, L (p ξ) = 0) (hptr : ∀ ξ, tr (p ξ) = ξ)
    (hzero : ∀ v, L v = 0 → tr v = 0 → v = 0) (v : V) :
    v = d (L v) + p (tr v) := by
  have hz : v - d (L v) - p (tr v) = 0 := by
    apply hzero
    · rw [map_sub, map_sub, hdL, hpL, sub_self, sub_zero]
    · rw [map_sub, map_sub, hdtr, hptr, sub_zero, sub_self]
  exact sub_eq_zero.mp (by simpa only [sub_sub] using hz)

/-- The same assembled map is the left inverse on the true matched
domain, selected by vanishing total weak outward flux. -/
theorem innerWeakSchurSolution_left_inverse
    (L : V →ₗ[ℝ] H) (tr : V →ₗ[ℝ] B)
    (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V)
    (flux : V →ₗ[ℝ] C) (S : B ≃ₗ[ℝ] C)
    (hdL : ∀ F, L (d F) = F) (hdtr : ∀ F, tr (d F) = 0)
    (hpL : ∀ ξ, L (p ξ) = 0) (hptr : ∀ ξ, tr (p ξ) = ξ)
    (hpflux : ∀ ξ, flux (p ξ) = S ξ)
    (hzero : ∀ v, L v = 0 → tr v = 0 → v = 0)
    (v : V) (hv : flux v = 0) :
    innerWeakSchurSolution d p flux S (L v) = v := by
  have hdec := innerWeakSchur_decomposition L tr d p hdL hdtr hpL hptr hzero v
  have hflux : flux (d (L v)) + S (tr v) = 0 := by
    rw [← hpflux, ← map_add, ← hdec]
    exact hv
  have htrace : S.symm (-flux (d (L v))) = tr v := by
    apply S.injective
    rw [S.apply_symm_apply]
    apply add_left_cancel (a := flux (d (L v)))
    rw [add_neg_cancel, hflux]
  rw [innerWeakSchurSolution_apply, htrace]
  exact hdec.symm

/-- When the proved forced-flux formula is minus the Poisson adjoint,
the very same solution has the usual plus Poisson-correction formula. -/
theorem innerWeakSchurSolution_correction
    (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V) (flux : V →ₗ[ℝ] C)
    (S : B ≃ₗ[ℝ] C) (adjointSource : H →ₗ[ℝ] C)
    (hflux : ∀ F, flux (d F) = -adjointSource F) (F : H) :
    innerWeakSchurSolution d p flux S F =
      d F + p (S.symm (adjointSource F)) := by
  rw [innerWeakSchurSolution_apply, hflux, neg_neg]

end WeakSchur

end ContinuousFlexibility.Radial
