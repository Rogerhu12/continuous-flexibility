import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Weak gluing on a finite family of actual closed piece domains

A matched field is a zero-endpoint field on each piece plus a common
boundary lift. This module proves the gluing equivalence by decomposing
every test field. Neither the global weak equation nor an inverse is
part of the input data. The radial specialization supplies the actual
physical closures, affine lifts, and energy-minus-forcing functionals.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped BigOperators

section FinitePieces

variable {ι E B : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup E] [Module ℝ E] [AddCommGroup B] [Module ℝ B]

/-- Matched fields with a single common boundary vector. -/
def innerMatchedPieceDomain (Z : ι → Submodule ℝ E)
    (lift : ι → B →ₗ[ℝ] E) : Submodule ℝ (ι → E) where
  carrier := {q | ∃ ξ : B, ∀ p, q p - lift p ξ ∈ Z p}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro p
    simpa only [Pi.zero_apply, map_zero, sub_zero] using (Z p).zero_mem
  add_mem' := by
    rintro q r ⟨ξ, hξ⟩ ⟨η, hη⟩
    refine ⟨ξ + η, ?_⟩
    intro p
    have he : (q + r) p - lift p (ξ + η) =
        (q p - lift p ξ) + (r p - lift p η) := by
      rw [Pi.add_apply, map_add]
      abel
    rw [he]
    exact (Z p).add_mem (hξ p) (hη p)
  smul_mem' := by
    rintro c q ⟨ξ, hξ⟩
    refine ⟨c • ξ, ?_⟩
    intro p
    rw [Pi.smul_apply, map_smul, ← smul_sub]
    exact (Z p).smul_mem c (hξ p)

theorem mem_innerMatchedPieceDomain (Z : ι → Submodule ℝ E)
    (lift : ι → B →ₗ[ℝ] E) (q : ι → E) :
    q ∈ innerMatchedPieceDomain Z lift ↔
      ∃ ξ : B, ∀ p, q p - lift p ξ ∈ Z p := Iff.rfl

theorem innerMatchedPieceDomain_lift (Z : ι → Submodule ℝ E)
    (lift : ι → B →ₗ[ℝ] E) (ξ : B) :
    (fun p => lift p ξ) ∈ innerMatchedPieceDomain Z lift := by
  refine ⟨ξ, ?_⟩
  intro p
  simpa only [sub_self] using (Z p).zero_mem

/-- Every local zero-endpoint test embeds in the matched test domain. -/
theorem innerMatchedPieceDomain_single (Z : ι → Submodule ℝ E)
    (lift : ι → B →ₗ[ℝ] E) (p : ι) {v : E} (hv : v ∈ Z p) :
    Pi.single p v ∈ innerMatchedPieceDomain Z lift := by
  classical
  refine ⟨0, ?_⟩
  intro k
  rw [map_zero, sub_zero]
  by_cases hk : k = p
  · subst k
    simpa only [Pi.single_eq_same] using hv
  · simpa only [Pi.single_eq_of_ne hk] using (Z k).zero_mem

/-- The total weak residual on fixed common boundary lifts. -/
def innerMatchedWeakFlux (lift : ι → B →ₗ[ℝ] E)
    (residual : ι → E →ₗ[ℝ] ℝ) : B →ₗ[ℝ] ℝ :=
  ∑ p, (residual p).comp (lift p)

theorem innerMatchedWeakFlux_apply (lift : ι → B →ₗ[ℝ] E)
    (residual : ι → E →ₗ[ℝ] ℝ) (ξ : B) :
    innerMatchedWeakFlux lift residual ξ = ∑ p, residual p (lift p ξ) := by
  simp only [innerMatchedWeakFlux, LinearMap.sum_apply, LinearMap.comp_apply]

/-- The global weak equation is equivalent to the local zero-endpoint
equations and cancellation of the total boundary residual. This is the
two-way weak gluing argument for arbitrary, possibly nonsmooth fields. -/
theorem innerMatchedPiece_weak_gluing (Z : ι → Submodule ℝ E)
    (lift : ι → B →ₗ[ℝ] E) (residual : ι → E →ₗ[ℝ] ℝ) :
    (∀ r ∈ innerMatchedPieceDomain Z lift, ∑ p, residual p (r p) = 0) ↔
      (∀ p, ∀ v ∈ Z p, residual p v = 0) ∧
        innerMatchedWeakFlux lift residual = 0 := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro p v hv
      have he := h (Pi.single p v) (innerMatchedPieceDomain_single Z lift p hv)
      have hs : (∑ k, residual k (Pi.single p v k)) = residual p v := by
        calc
          _ = residual p (Pi.single p v p) := by
            apply Finset.sum_eq_single p
            · intro k _ hk
              rw [Pi.single_eq_of_ne hk, map_zero]
            · intro hp
              exact (hp (Finset.mem_univ p)).elim
          _ = residual p v := by rw [Pi.single_eq_same]
      exact hs.symm.trans he
    · apply LinearMap.ext
      intro ξ
      rw [innerMatchedWeakFlux_apply]
      exact h (fun p => lift p ξ) (innerMatchedPieceDomain_lift Z lift ξ)
  · rintro ⟨hlocal, hflux⟩ r ⟨ξ, hξ⟩
    have he (p : ι) : residual p (r p) = residual p (lift p ξ) := by
      have hz := hlocal p (r p - lift p ξ) (hξ p)
      rw [map_sub] at hz
      exact sub_eq_zero.mp hz
    calc
      _ = ∑ p, residual p (lift p ξ) := Finset.sum_congr rfl (fun p _ => he p)
      _ = innerMatchedWeakFlux lift residual ξ :=
        (innerMatchedWeakFlux_apply lift residual ξ).symm
      _ = 0 := by rw [hflux, LinearMap.zero_apply]

end FinitePieces

end ContinuousFlexibility.Radial
