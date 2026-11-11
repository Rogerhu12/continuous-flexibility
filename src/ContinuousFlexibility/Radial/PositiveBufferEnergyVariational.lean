import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Variational minimization with prescribed boundary data

This module gives the Hilbert-space part of the positive-buffer construction.
The zero-boundary fields form a closed submodule. Lax--Milgram removes the
component of an arbitrary boundary lift detected by that submodule. For a
symmetric form the resulting stationary field is the unique energy minimizer.

The actual differential energy space and its trace maps are separate analytic
inputs; no assertion identifying them with abstract data is made here.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restriction of a coercive energy form to the zero-boundary subspace. -/
theorem positiveBuffer_restrict_isCoercive
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B) (K : Submodule ℝ E) :
    IsCoercive (B.bilinearComp K.subtypeL K.subtypeL) := by
  obtain ⟨c, hc, hco⟩ := hB
  refine ⟨c, hc, fun u => ?_⟩
  simpa only [ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply,
    Submodule.norm_coe] using hco (u : E)

/-- Coercivity detects a zero-energy vector without any symmetry assumption. -/
theorem positiveBuffer_eq_zero_of_energy_eq_zero
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B) {u : E}
    (hu : B u u = 0) : u = 0 := by
  obtain ⟨c, hc, hco⟩ := hB
  have h := hco u
  rw [hu] at h
  by_contra hne
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hne
  exact (not_le_of_gt (mul_pos (mul_pos hc hn) hn)) h

/-- The variational Dirichlet problem on an affine translate of a closed
zero-boundary subspace has exactly one solution. -/
theorem positiveBuffer_exists_unique_stationary_of_restrict [CompleteSpace E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (K : Submodule ℝ E) (hK : IsClosed (K : Set E))
    (hBK : IsCoercive (B.bilinearComp K.subtypeL K.subtypeL)) (lift : E) :
    ∃! u : E, u - lift ∈ K ∧ ∀ v : E, v ∈ K → B u v = 0 := by
  letI : CompleteSpace K := hK.completeSpace_coe
  let BK : K →L[ℝ] K →L[ℝ] ℝ := B.bilinearComp K.subtypeL K.subtypeL
  let ell : K →L[ℝ] ℝ := (B lift).comp K.subtypeL
  let z : K := hBK.continuousLinearEquivOfBilin.symm ((toDual ℝ K).symm ell)
  have hz (v : K) : B (z : E) (v : E) = B lift (v : E) := by
    calc
      B (z : E) (v : E) = BK z v :=
        (ContinuousLinearMap.bilinearComp_apply B K.subtypeL K.subtypeL z v).symm
      _ = ⟪hBK.continuousLinearEquivOfBilin z, v⟫_ℝ :=
        (hBK.continuousLinearEquivOfBilin_apply z v).symm
      _ = ⟪(toDual ℝ K).symm ell, v⟫_ℝ := by
        rw [show hBK.continuousLinearEquivOfBilin z = (toDual ℝ K).symm ell from
          hBK.continuousLinearEquivOfBilin.apply_symm_apply _]
      _ = ell v := toDual_symm_apply
      _ = B lift (v : E) := ContinuousLinearMap.comp_apply _ _ _
  let u : E := lift - (z : E)
  have huK : u - lift ∈ K := by
    have he : u - lift = -(z : E) := by dsimp [u]; abel
    rw [he]
    exact K.neg_mem z.property
  have hu (v : E) (hv : v ∈ K) : B u v = 0 := by
    dsimp [u]
    rw [map_sub B lift (z : E), ContinuousLinearMap.sub_apply]
    exact sub_eq_zero.mpr (hz ⟨v, hv⟩).symm
  refine ⟨u, ⟨huK, hu⟩, ?_⟩
  rintro w ⟨hwK, hw⟩
  have hdK : w - u ∈ K := by
    have he : w - u = (w - lift) - (u - lift) := by abel
    rw [he]
    exact K.sub_mem hwK huK
  have hd : B (w - u) (w - u) = 0 := by
    rw [map_sub B w u, ContinuousLinearMap.sub_apply, hw _ hdK, hu _ hdK, sub_self]
  have hzero : (⟨w - u, hdK⟩ : K) = 0 :=
    positiveBuffer_eq_zero_of_energy_eq_zero BK hBK
      (by simpa only [BK, ContinuousLinearMap.bilinearComp_apply,
        Submodule.subtypeL_apply] using hd)
  exact sub_eq_zero.mp (congrArg (fun z : K => (z : E)) hzero)

/-- Global coercivity is a sufficient condition for the preceding result. -/
theorem positiveBuffer_exists_unique_stationary [CompleteSpace E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B)
    (K : Submodule ℝ E) (hK : IsClosed (K : Set E)) (lift : E) :
    ∃! u : E, u - lift ∈ K ∧ ∀ v : E, v ∈ K → B u v = 0 :=
  positiveBuffer_exists_unique_stationary_of_restrict B K hK
    (positiveBuffer_restrict_isCoercive B hB K) lift

/-- Exact energy decomposition around a stationary field. This is the
variational identity used for both the finite buffer and the exterior. -/
theorem positiveBuffer_stationary_energy_identity
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hBsymm : ∀ u v : E, B u v = B v u)
    (K : Submodule ℝ E) {u v : E}
    (hu : ∀ w : E, w ∈ K → B u w = 0) (hv : v - u ∈ K) :
    B v v = B u u + B (v - u) (v - u) := by
  have hcross : B u (v - u) = 0 := hu _ hv
  have hcross' : B (v - u) u = 0 := (hBsymm _ _).trans hcross
  have he : v = u + (v - u) := by abel
  conv_lhs => rw [he]
  rw [map_add B u (v - u), ContinuousLinearMap.add_apply,
    map_add (B u) u (v - u), map_add (B (v - u)) u (v - u), hcross, hcross']
  ring

/-- A stationary field minimizes every symmetric coercive energy, with
equality precisely for that field. -/
theorem positiveBuffer_stationary_energy_minimum
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B)
    (hBsymm : ∀ u v : E, B u v = B v u)
    (K : Submodule ℝ E) {u v : E}
    (hu : ∀ w : E, w ∈ K → B u w = 0) (hv : v - u ∈ K) :
    B u u ≤ B v v ∧ (B u u = B v v ↔ u = v) := by
  have hid := positiveBuffer_stationary_energy_identity B hBsymm K hu hv
  have hn : 0 ≤ B (v - u) (v - u) := by
    obtain ⟨c, hc, hco⟩ := hB
    exact (mul_nonneg (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).trans
      (hco _)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hzero : B (v - u) (v - u) = 0 := by linarith
    exact (sub_eq_zero.mp (positiveBuffer_eq_zero_of_energy_eq_zero B hB hzero)).symm
  · rintro rfl
    rfl

/-- Applying the abstract construction to a continuous trace gives the
variational solution with any prescribed value attained by a boundary lift. -/
theorem positiveBuffer_exists_unique_trace_stationary [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B)
    (trace : E →L[ℝ] F) (lift : E) :
    ∃! u : E, trace u = trace lift ∧ ∀ v : E, trace v = 0 → B u v = 0 := by
  obtain ⟨u, hu, huniq⟩ := positiveBuffer_exists_unique_stationary B hB
    trace.ker trace.isClosed_ker lift
  have hmem (v : E) : v - lift ∈ trace.ker ↔ trace v = trace lift := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero]
  refine ⟨u, ⟨(hmem u).mp hu.1, ?_⟩, ?_⟩
  · intro v hv
    exact hu.2 v (LinearMap.mem_ker.mpr hv)
  · rintro v ⟨hv, hvzero⟩
    apply huniq v
    exact ⟨(hmem v).mpr hv, fun w hw => hvzero w (LinearMap.mem_ker.mp hw)⟩

end ContinuousFlexibility.Radial
