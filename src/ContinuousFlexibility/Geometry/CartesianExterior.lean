module

public import ContinuousFlexibility.Geometry.CartesianDevelopment
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Connected exteriors for Cartesian reconstruction

The norm in this file is used only to specify an exterior and a compact support region.
No norm is identified with the coordinate-square metric on `PolarPoint`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Metric
open scoped ContDiff

theorem isPreconnected_norm_exterior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hdim : 1 < Module.rank ℝ E) {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected {x : E | R < ‖x‖} := by
  let f : E × ℝ → E := fun q => q.2 • q.1
  have hs := isPreconnected_sphere hdim (0 : E) 1
  have hprod := hs.prod (convex_Ioi R).isPreconnected
  have hf : Continuous f := continuous_snd.smul continuous_fst
  have himage : f '' (sphere (0 : E) 1 ×ˢ Ioi R) = {x : E | R < ‖x‖} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by simpa using hu
      have ht0 : 0 ≤ t := hR.trans ht.le
      simpa [f, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, hu'] using ht
    · intro x hx
      have hx0 : ‖x‖ ≠ 0 := ne_of_gt (hR.trans_lt hx)
      refine ⟨(‖x‖⁻¹ • x, ‖x‖), ⟨?_, hx⟩, ?_⟩
      · simp [norm_smul, inv_mul_cancel₀ hx0]
      · simp [f, smul_smul, mul_inv_cancel₀ hx0]
  rw [← himage]
  exact hprod.image f hf.continuousOn

theorem isPreconnected_complex_radius_exterior {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected {x : PolarPoint | R < ‖Complex.equivRealProdCLM.symm x‖} := by
  let e := Complex.equivRealProdCLM
  have hs : IsPreconnected {z : ℂ | R < ‖z‖} :=
    isPreconnected_norm_exterior (by simp [Complex.rank_real_complex]) hR
  have heq : e '' {z : ℂ | R < ‖z‖} = {x : PolarPoint | R < ‖e.symm x‖} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  rw [← heq]
  exact hs.image e e.continuous.continuousOn

theorem isOpen_complex_radius_exterior (R : ℝ) :
    IsOpen {x : PolarPoint | R < ‖Complex.equivRealProdCLM.symm x‖} :=
  isOpen_lt continuous_const Complex.equivRealProdCLM.symm.continuous.norm

theorem isCompact_complex_radius_sublevel (R : ℝ) :
    IsCompact {x : PolarPoint | ‖Complex.equivRealProdCLM.symm x‖ ≤ R} := by
  let e := Complex.equivRealProdCLM
  have heq : e '' closedBall (0 : ℂ) R = {x : PolarPoint | ‖e.symm x‖ ≤ R} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨e.symm x, by simpa using hx, e.apply_symm_apply x⟩
  rw [← heq]
  exact (isCompact_closedBall (0 : ℂ) R).image e.continuous

/-- The geometric radius version of the complete Cartesian reconstruction.
It produces the development, its smooth global inverse, exterior normalization,
and preservation of the filled disk from actual Cartan data. -/
theorem exists_global_development_of_flat_cartesian_coframe_on_disk
    (d : FlatCartesianCoframe) {R : ℝ} (hR : 0 ≤ R)
    (hzero : ∀ x : PolarPoint, R < ‖Complex.equivRealProdCLM.symm x‖ →
      d.connection.radial x = 0 ∧ d.connection.angular x = 0)
    (hstd : ∀ x : PolarPoint, R < ‖Complex.equivRealProdCLM.symm x‖ →
      d.first.radial x = 1 ∧ d.first.angular x = 0 ∧
      d.second.radial x = 0 ∧ d.second.angular x = 1) :
    ∃ e : PolarPoint ≃ₜ PolarPoint,
      (∀ x, ContDiffAt ℝ ∞ (e : PolarPoint → PolarPoint) x) ∧
      (∀ y, ContDiffAt ℝ ∞ (e.symm : PolarPoint → PolarPoint) y) ∧
      (∀ x, R < ‖Complex.equivRealProdCLM.symm x‖ → e x = x) ∧
      e '' {x | ‖Complex.equivRealProdCLM.symm x‖ ≤ R} =
        {x | ‖Complex.equivRealProdCLM.symm x‖ ≤ R} ∧
      ∀ x v : PolarPoint,
        (fderiv ℝ (e : PolarPoint → PolarPoint) x v).1 ^ 2 +
          (fderiv ℝ (e : PolarPoint → PolarPoint) x v).2 ^ 2 =
            formValue d.first x v ^ 2 + formValue d.second x v ^ 2 := by
  let U : Set PolarPoint := {x | R < ‖Complex.equivRealProdCLM.symm x‖}
  let K : Set PolarPoint := {x | ‖Complex.equivRealProdCLM.symm x‖ ≤ R}
  have hout : Kᶜ ⊆ U := fun x hx => by
    simpa only [K, U, mem_compl_iff, mem_ofPred_eq, not_le] using hx
  obtain ⟨ψ, e, _, _, _, hes, heis, heout, _, hemetric⟩ :=
    exists_global_development_of_flat_cartesian_coframe d
      (isOpen_complex_radius_exterior R) (isPreconnected_complex_radius_exterior hR)
      hzero hstd (isCompact_complex_radius_sublevel R) hout
  have hfix : ∀ x, x ∉ K → e x = x := fun x hx => heout (hout hx)
  exact ⟨e, hes, heis, heout,
    image_eq_self_of_bijective_eq_id_outside e.bijective hfix, hemetric⟩

end ContinuousFlexibility
