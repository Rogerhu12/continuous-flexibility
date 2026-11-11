import ContinuousFlexibility.Analysis.AngularRawResolvent
import ContinuousFlexibility.Analysis.AngularResolventDomains
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# From an arbitrary angular operator to its bounded resolvent

The real spectrum of a partially defined operator is the complement of
the parameters for which the operator minus that parameter has an actual
bounded two-sided inverse.  An integer spectral hypothesis therefore
supplies the shifted inverse at `-1`.  A direct resolvent identity proves
the reciprocal spectral condition used by the bounded spectral theorem.
The reconstructed unbounded operator is proved equal to the original
operator, including its domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

/-- The real spectrum of a partially defined operator, using genuine
bounded inverses of `A - r I` on its actual domain. -/
def angularRawSpectrum (A : H →ₗ.[𝕜] H) : Set ℝ :=
  {r | ¬ Nonempty (AngularRawResolventData A r)}

theorem angularRawResolvent_nonempty_of_not_mem {A : H →ₗ.[𝕜] H} {r : ℝ}
    (hr : r ∉ angularRawSpectrum A) : Nonempty (AngularRawResolventData A r) := by
  classical
  simpa only [angularRawSpectrum, mem_setOf_eq, not_not] using hr

/-- The original integer spectral hypothesis already supplies the
shifted inverse; no positivity or surjectivity premise is added. -/
def angularRawShiftedResolvent (A : H →ₗ.[𝕜] H)
    (hSpectrum : angularRawSpectrum A ⊆ range (fun n : ℕ => (n : ℝ))) :
    AngularRawResolventData A (-1) :=
  Classical.choice (angularRawResolvent_nonempty_of_not_mem (by
    intro h
    obtain ⟨n, hn⟩ := hSpectrum h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith))

namespace AngularRawResolventData

variable {A : H →ₗ.[𝕜] H}

/-- A genuine shifted inverse reconstructs the original partial
operator, with equality of both domain and action. -/
theorem frequency_eq (Q : AngularRawResolventData A (-1)) :
    angularResolventOperator Q.operator Q.injective = A := by
  apply LinearPMap.ext
  · exact Q.range_eq_domain
  · intro x hxQ hxA
    have h := Q.injective
      ((angularResolventOperator_right_inverse Q.operator Q.injective ⟨x, hxQ⟩).trans
        (Q.right_shifted ⟨x, hxA⟩).symm)
    exact add_left_cancel h

private theorem comp_left_identity (Q : AngularRawResolventData A (-1))
    {t : ℝ} (T : AngularRawResolventData A t) (x : H) :
    (t + 1) • Q.operator (T.operator x) = T.operator x - Q.operator x := by
  have hAT : A ⟨T.operator x, T.mapsDomain x⟩ = x + t • T.operator x := by
    simpa only [← RCLike.real_smul_eq_coe_smul (K := 𝕜)] using
      (sub_eq_iff_eq_add.mp (T.left x))
  calc
    (t + 1) • Q.operator (T.operator x) =
        Q.operator (t • T.operator x + T.operator x) := by
      rw [map_add, ContinuousLinearMap.map_smul_of_tower]
      module
    _ = Q.operator ((T.operator x + A ⟨T.operator x, T.mapsDomain x⟩) - x) := by
      rw [hAT]
      congr 1
      module
    _ = T.operator x - Q.operator x := by
      rw [map_sub]
      exact congrArg (fun y : H => y - Q.operator x)
        (Q.right_shifted ⟨T.operator x, T.mapsDomain x⟩)

private theorem comp_right_identity (Q : AngularRawResolventData A (-1))
    {t : ℝ} (T : AngularRawResolventData A t) (x : H) :
    (t + 1) • T.operator (Q.operator x) = T.operator x - Q.operator x := by
  have hAQ : A ⟨Q.operator x, Q.mapsDomain x⟩ = x - Q.operator x := by
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using Q.left_shifted x
  have hT : T.operator (A ⟨Q.operator x, Q.mapsDomain x⟩ - t • Q.operator x) =
      Q.operator x := by
    simpa only [← RCLike.real_smul_eq_coe_smul (K := 𝕜)] using
      T.right ⟨Q.operator x, Q.mapsDomain x⟩
  calc
    (t + 1) • T.operator (Q.operator x) = T.operator ((t + 1) • Q.operator x) := by
      rw [ContinuousLinearMap.map_smul_of_tower]
    _ = T.operator (x - (A ⟨Q.operator x, Q.mapsDomain x⟩ - t • Q.operator x)) := by
      rw [hAQ]
      congr 1
      module
    _ = T.operator x - Q.operator x := by rw [map_sub, hT]

/-- The reciprocal spectral transformation is an explicit bounded
inverse identity, rather than an assumed spectral-mapping theorem. -/
theorem isUnit_scalar_sub_of_raw_resolvent (Q : AngularRawResolventData A (-1))
    {r : ℝ} (hr : r ≠ 0) (T : AngularRawResolventData A (r⁻¹ - 1)) :
    IsUnit (algebraMap ℝ (H →L[𝕜] H) r - Q.operator) := by
  have hrinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have hinvr : r⁻¹ * r = 1 := inv_mul_cancel₀ hr
  have hrr : r * (r⁻¹) ^ 2 = r⁻¹ := by field_simp [hr]
  have hrr' : (r⁻¹) ^ 2 * r = r⁻¹ := by rw [mul_comm]; exact hrr
  have hmul : r * ((r⁻¹ - 1) + 1) = 1 := by rw [sub_add_cancel, hrinv]
  have hQT (x : H) : Q.operator (T.operator x) = r • (T.operator x - Q.operator x) := by
    calc
      _ = (r * ((r⁻¹ - 1) + 1)) • Q.operator (T.operator x) := by
        rw [hmul, one_smul]
      _ = r • (((r⁻¹ - 1) + 1) • Q.operator (T.operator x)) := by rw [smul_smul]
      _ = r • (T.operator x - Q.operator x) := by rw [comp_left_identity]
  have hTQ (x : H) : T.operator (Q.operator x) = r • (T.operator x - Q.operator x) := by
    calc
      _ = (r * ((r⁻¹ - 1) + 1)) • T.operator (Q.operator x) := by
        rw [hmul, one_smul]
      _ = r • (((r⁻¹ - 1) + 1) • T.operator (Q.operator x)) := by rw [smul_smul]
      _ = r • (T.operator x - Q.operator x) := by rw [comp_right_identity]
  let S : H →L[𝕜] H :=
    r⁻¹ • ContinuousLinearMap.id 𝕜 H + (r⁻¹) ^ 2 • T.operator
  apply isUnit_iff_exists.mpr
  refine ⟨S, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    simp only [mul_apply_eq_comp, one_apply_eq_self, sub_apply,
      ContinuousLinearMap.algebraMap_apply, S, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_add, ContinuousLinearMap.map_smul_of_tower,
      hQT, smul_add, smul_sub, smul_smul, hrinv, hinvr, hrr, hrr', one_smul]
    module
  · apply ContinuousLinearMap.ext
    intro x
    simp only [mul_apply_eq_comp, one_apply_eq_self, sub_apply,
      ContinuousLinearMap.algebraMap_apply, S, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_sub, ContinuousLinearMap.map_smul_of_tower,
      hTQ, smul_add, smul_sub, smul_smul, hrinv, hinvr, hrr, hrr', one_smul]
    module

/-- The integer spectrum of the original unbounded operator implies
the reciprocal spectrum of its bounded shifted inverse. -/
theorem spectrum_subset_reciprocal (Q : AngularRawResolventData A (-1))
    (hSpectrum : angularRawSpectrum A ⊆ range (fun n : ℕ => (n : ℝ))) :
    spectrum ℝ Q.operator ⊆ angularReciprocalSpectrum := by
  intro r hr
  by_cases hr0 : r = 0
  · exact Or.inl hr0
  · have hraw : r⁻¹ - 1 ∈ angularRawSpectrum A := by
      by_contra hnot
      obtain ⟨T⟩ := angularRawResolvent_nonempty_of_not_mem hnot
      exact (spectrum.mem_iff.mp hr) (Q.isUnit_scalar_sub_of_raw_resolvent hr0 T)
    obtain ⟨n, hn⟩ := hSpectrum hraw
    refine Or.inr ⟨n, ?_⟩
    have hn1 : (n : ℝ) + 1 = r⁻¹ := by linarith
    rw [angularResolventEigenvalue, hn1, one_div, inv_inv]

end AngularRawResolventData

/-- Canonical bounded angular data constructed from an arbitrary
self-adjoint partial operator with integer real spectrum. -/
def angularResolventDataOfRaw (A : H →ₗ.[𝕜] H) (hA : IsSelfAdjoint A)
    (hSpectrum : angularRawSpectrum A ⊆ range (fun n : ℕ => (n : ℝ))) :
    AngularResolventData 𝕜 H where
  operator := (angularRawShiftedResolvent A hSpectrum).operator
  selfAdjoint := (angularRawShiftedResolvent A hSpectrum).selfAdjoint hA
  injective := (angularRawShiftedResolvent A hSpectrum).injective
  spectrum_subset := (angularRawShiftedResolvent A hSpectrum).spectrum_subset_reciprocal hSpectrum

theorem angularResolventDataOfRaw_frequency_eq [HasAngularSpectralDecomposition 𝕜 H]
    (A : H →ₗ.[𝕜] H) (hA : IsSelfAdjoint A)
    (hSpectrum : angularRawSpectrum A ⊆ range (fun n : ℕ => (n : ℝ))) :
    (angularResolventDataOfRaw A hA hSpectrum).frequency = A :=
  (angularRawShiftedResolvent A hSpectrum).frequency_eq

end ContinuousFlexibility.Analysis
