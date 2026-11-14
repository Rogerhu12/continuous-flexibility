module

public import ContinuousFlexibility.Analysis.AngularResolventApproximation

/-!
# The full discrete angular spectral decomposition

A self-adjoint injective bounded resolvent with the reciprocal integer
spectrum is a Hilbert sum of all its eigenspaces. The proof uses the
operator-norm approximation from `AngularResolventApproximation` and the
density of the range of an injective self-adjoint operator. Eigenspaces
may have arbitrary dimension, and the original Hilbert space may be
nonseparable.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

section General

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The closed eigenspace belonging to the `n`th angular frequency. -/
def angularResolventEigenspace (B : H →L[𝕜] H) (n : ℕ) : Submodule 𝕜 H :=
  (B - (angularResolventEigenvalue n : 𝕜) • ContinuousLinearMap.id 𝕜 H).ker

theorem mem_angularResolventEigenspace (B : H →L[𝕜] H) (n : ℕ) (x : H) :
    x ∈ angularResolventEigenspace B n ↔
      B x = (angularResolventEigenvalue n : 𝕜) • x := by
  simp only [angularResolventEigenspace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, smul_apply, ContinuousLinearMap.id_apply, sub_eq_zero]

instance angularResolventEigenspace_completeSpace (B : H →L[𝕜] H) (n : ℕ) :
    CompleteSpace (angularResolventEigenspace B n) := by
  unfold angularResolventEigenspace
  infer_instance

theorem angularResolventEigenspace_eq (B : H →L[𝕜] H) (n : ℕ) :
    angularResolventEigenspace B n =
      Module.End.eigenspace B.toLinearMap (angularResolventEigenvalue n : 𝕜) := by
  ext x
  rw [mem_angularResolventEigenspace, Module.End.mem_eigenspace_iff]
  rfl

theorem angularResolventEigenspaces_orthogonal {B : H →L[𝕜] H} (hB : IsSelfAdjoint B) :
    OrthogonalFamily 𝕜 (fun n => angularResolventEigenspace B n)
      (fun n => (angularResolventEigenspace B n).subtypeₗᵢ) := by
  have hinj : Function.Injective (fun n => (angularResolventEigenvalue n : 𝕜)) :=
    RCLike.ofReal_injective.comp angularResolventEigenvalue_strictAnti.injective
  have hF : angularResolventEigenspace B = fun n =>
      Module.End.eigenspace B.toLinearMap (angularResolventEigenvalue n : 𝕜) :=
    funext (angularResolventEigenspace_eq B)
  rw [hF]
  exact hB.isSymmetric.orthogonalFamily_eigenspaces.comp hinj

/-- The common density step, for real and complex Hilbert spaces. -/
theorem angularResolventEigenspaces_total_of_range {B : H →L[𝕜] H}
    (hB : IsSelfAdjoint B) (hInjective : Function.Injective B)
    (hRange : B.range ≤ (⨆ n, angularResolventEigenspace B n).topologicalClosure) :
    ⊤ ≤ (⨆ n, angularResolventEigenspace B n).topologicalClosure := by
  have hker : B.ker = ⊥ := LinearMap.ker_eq_bot.mpr hInjective
  have hdense : B.range.topologicalClosure = ⊤ := by
    calc
      B.range.topologicalClosure = B.adjoint.range.topologicalClosure := by
        rw [hB.adjoint_eq]
      _ = B.kerᗮ := B.orthogonal_ker.symm
      _ = ⊤ := by rw [hker, Submodule.bot_orthogonal_eq_top]
  rw [← hdense]
  exact B.range.topologicalClosure_minimal hRange
    (Submodule.isClosed_topologicalClosure _)

end General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem angularResolventProjection_mem {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) (n : ℕ) (x : H) :
    angularResolventProjection B n x ∈ angularResolventEigenspace B n := by
  rw [mem_angularResolventEigenspace]
  have h := congrArg (fun T : H →L[ℂ] H => T x)
    (angularResolventProjection_eigen hB hSpectrum n)
  simpa only [mul_apply_eq_comp, smul_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ)] using h

theorem angularResolventPartial_mem_iSup {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) (N : ℕ) (x : H) :
    angularResolventPartial B N x ∈ ⨆ n, angularResolventEigenspace B n := by
  let S : Submodule ℂ H := ⨆ n, angularResolventEigenspace B n
  have hterm (n : ℕ) : angularResolventEigenvalue n • angularResolventProjection B n x ∈ S := by
    apply S.smul_of_tower_mem
    exact (le_iSup (fun n => angularResolventEigenspace B n) n)
      (angularResolventProjection_mem hB hSpectrum n x)
  simpa only [angularResolventPartial, sum_apply, smul_apply] using
    S.sum_mem (fun n (_ : n ∈ Finset.range N) => hterm n)

/-- The nonzero reciprocal eigenspaces span densely. Injectivity removes
the possible zero spectral subspace. -/
theorem angularResolventEigenspaces_total {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hInjective : Function.Injective B)
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) :
    ⊤ ≤ (⨆ n, angularResolventEigenspace B n).topologicalClosure := by
  let S : Submodule ℂ H := ⨆ n, angularResolventEigenspace B n
  have hRange : B.range ≤ S.topologicalClosure := by
    rintro _ ⟨x, rfl⟩
    have hlim : Tendsto (fun N => angularResolventPartial B N x) atTop (𝓝 (B x)) :=
      angularResolventPartial_apply_tendsto hB hSpectrum x
    apply S.isClosed_topologicalClosure.mem_of_tendsto hlim
    exact Eventually.of_forall (fun N => S.le_topologicalClosure
      (angularResolventPartial_mem_iSup hB hSpectrum N x))
  exact angularResolventEigenspaces_total_of_range hB hInjective hRange

/-- Discrete spectral decomposition for a bounded angular resolvent,
without finite-dimensionality or separability assumptions. -/
theorem angularResolvent_isHilbertSum {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hInjective : Function.Injective B)
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) :
    IsHilbertSum ℂ (fun n => angularResolventEigenspace B n)
      (fun n => (angularResolventEigenspace B n).subtypeₗᵢ) :=
  IsHilbertSum.mkInternal (fun n => angularResolventEigenspace B n)
    (angularResolventEigenspaces_orthogonal hB)
    (angularResolventEigenspaces_total hB hInjective hSpectrum)

end ContinuousFlexibility.Analysis
