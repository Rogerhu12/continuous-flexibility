import ContinuousFlexibility.Analysis.AngularComplexificationSpectrum
import ContinuousFlexibility.Analysis.AngularSpectralDecomposition

/-!
# The angular spectral decomposition over the reals

The eigenspaces, their orthogonality, and the dense-range argument are the
same objects and theorems as in the complex case.  Only the approximation
step is transferred: take the real components of the finite complex
spectral sums.  This proves the full real Hilbert decomposition without
assuming a real continuous functional calculus or a diagonalization.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter AngularComplexification
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The original real action on the complexification agrees with the
canonical restriction of its complex action.  This also identifies the
real algebra structures used by the two spectrum interfaces. -/
private theorem complexification_real_normedSpace_eq :
    (instRealInnerProductSpace (H := H)).toNormedSpace =
      (NormedSpace.complexToReal : NormedSpace ℝ (AngularComplexification H)) := by
  have hmodule : (instRealInnerProductSpace (H := H)).toNormedSpace.toModule =
      (NormedSpace.complexToReal : NormedSpace ℝ (AngularComplexification H)).toModule :=
    Module.ext' _ _ (fun r u => (ofReal_smul r u).symm)
  have hinjective : Function.Injective
      (fun P : NormedSpace ℝ (AngularComplexification H) => P.toModule) := by
    intro P Q h
    cases P
    cases Q
    cases h
    rfl
  exact hinjective hmodule

private theorem spectrum_real_extend_canonical (B : H →L[ℝ] H) :
    (letI : NormedSpace ℝ (AngularComplexification H) := NormedSpace.complexToReal
      spectrum ℝ (extend B)) = spectrum ℝ B := by
  letI : NormedSpace ℝ (AngularComplexification H) := NormedSpace.complexToReal
  change spectrum ℝ (extend B) = spectrum ℝ B
  ext r
  rw [spectrum.mem_iff, spectrum.mem_iff]
  have hscalar : algebraMap ℝ
      (AngularComplexification H →L[ℂ] AngularComplexification H) r =
      extend (algebraMap ℝ (H →L[ℝ] H) r) := by
    apply ContinuousLinearMap.ext
    intro u
    rw [ContinuousLinearMap.algebraMap_apply]
    change (r : ℂ) • u = extend (algebraMap ℝ (H →L[ℝ] H) r) u
    rw [extend_apply]
    apply AngularComplexification.ext <;>
      simp only [re_smul, im_smul, re_mk, im_mk, ContinuousLinearMap.algebraMap_apply,
        Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero, zero_add]
  rw [hscalar, ← extend_sub, isUnit_extend_iff]

/-- The real part of a complexified real eigenvector is a real eigenvector. -/
theorem re_mem_angularResolventEigenspace {B : H →L[ℝ] H} {n : ℕ}
    {u : AngularComplexification H}
    (hu : u ∈ angularResolventEigenspace (extend B) n) :
    u.re ∈ angularResolventEigenspace B n := by
  rw [mem_angularResolventEigenspace] at hu ⊢
  simpa only [re_extend, RCLike.ofReal_eq_complex_ofReal, RCLike.ofReal_real_eq_id,
    id_eq, ofReal_smul, re_real_smul] using congrArg re hu

/-- The real part of each finite complex spectral sum belongs to the
algebraic span of the real eigenspaces. -/
theorem angularResolventPartial_re_mem_iSup {B : H →L[ℝ] H} (hB : IsSelfAdjoint B)
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) (N : ℕ) (x : H) :
    (angularResolventPartial (extend B) N (ofReal x)).re ∈
      ⨆ n, angularResolventEigenspace B n := by
  have hBC : IsSelfAdjoint (extend B) := (isSelfAdjoint_extend_iff B).mpr hB
  have hSpectrumC :
      (letI : NormedSpace ℝ (AngularComplexification H) := NormedSpace.complexToReal
        spectrum ℝ (extend B)) ⊆ angularReciprocalSpectrum := by
    rw [spectrum_real_extend_canonical]
    exact hSpectrum
  let S : Submodule ℝ H := ⨆ n, angularResolventEigenspace B n
  have hterm (n : ℕ) :
      angularResolventEigenvalue n • (angularResolventProjection (extend B) n (ofReal x)).re ∈ S := by
    apply S.smul_mem
    exact (le_iSup (fun n => angularResolventEigenspace B n) n)
      (re_mem_angularResolventEigenspace (angularResolventProjection_mem hBC hSpectrumC n (ofReal x)))
  have heq : (angularResolventPartial (extend B) N (ofReal x)).re =
      ∑ n ∈ Finset.range N,
        angularResolventEigenvalue n • (angularResolventProjection (extend B) n (ofReal x)).re := by
    simpa only [angularResolventPartial, ← complexification_real_normedSpace_eq,
      sum_apply, smul_apply, ContinuousLinearMap.smul_apply, reCLM_apply, re_real_smul] using
      map_sum (reCLM : AngularComplexification H →L[ℝ] H)
        (fun n => angularResolventEigenvalue n • angularResolventProjection (extend B) n (ofReal x))
        (Finset.range N)
  rw [heq]
  exact S.sum_mem (fun n (_ : n ∈ Finset.range N) => hterm n)

/-- The range of a real discrete-spectrum resolvent lies in the closed
span of its real eigenspaces. -/
theorem angularRealResolvent_range_le {B : H →L[ℝ] H} (hB : IsSelfAdjoint B)
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) :
    B.range ≤ (⨆ n, angularResolventEigenspace B n).topologicalClosure := by
  let S : Submodule ℝ H := ⨆ n, angularResolventEigenspace B n
  have hBC : IsSelfAdjoint (extend B) := (isSelfAdjoint_extend_iff B).mpr hB
  have hSpectrumC :
      (letI : NormedSpace ℝ (AngularComplexification H) := NormedSpace.complexToReal
        spectrum ℝ (extend B)) ⊆ angularReciprocalSpectrum := by
    rw [spectrum_real_extend_canonical]
    exact hSpectrum
  rintro _ ⟨x, rfl⟩
  have hlimC : Tendsto (fun N => angularResolventPartial (extend B) N (ofReal x))
      atTop (𝓝 (extend B (ofReal x))) :=
    ((continuous_eval_const (ofReal x)).tendsto (extend B)).comp
      (angularResolventPartial_tendsto hBC hSpectrumC)
  have hlim : Tendsto (fun N => (angularResolventPartial (extend B) N (ofReal x)).re)
      atTop (𝓝 (B x)) := by
    simpa only [Function.comp_def, reCLM_apply, re_extend, re_ofReal] using
      ((reCLM : AngularComplexification H →L[ℝ] H).continuous.tendsto
        (extend B (ofReal x))).comp hlimC
  apply S.isClosed_topologicalClosure.mem_of_tendsto hlim
  exact Eventually.of_forall (fun N => S.le_topologicalClosure
    (angularResolventPartial_re_mem_iSup hB hSpectrum N x))

/-- Totality of the real reciprocal eigenspaces, from the common
self-adjoint dense-range lemma. -/
theorem angularRealResolventEigenspaces_total {B : H →L[ℝ] H} (hB : IsSelfAdjoint B)
    (hInjective : Function.Injective B)
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) :
    ⊤ ≤ (⨆ n, angularResolventEigenspace B n).topologicalClosure :=
  angularResolventEigenspaces_total_of_range hB hInjective
    (angularRealResolvent_range_le hB hSpectrum)

/-- Full discrete spectral decomposition of an arbitrary real Hilbert
space with an injective self-adjoint reciprocal-spectrum resolvent. -/
theorem angularRealResolvent_isHilbertSum {B : H →L[ℝ] H} (hB : IsSelfAdjoint B)
    (hInjective : Function.Injective B)
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) :
    IsHilbertSum ℝ (fun n => angularResolventEigenspace B n)
      (fun n => (angularResolventEigenspace B n).subtypeₗᵢ) :=
  IsHilbertSum.mkInternal (fun n => angularResolventEigenspace B n)
    (angularResolventEigenspaces_orthogonal hB)
    (angularRealResolventEigenspaces_total hB hInjective hSpectrum)

end ContinuousFlexibility.Analysis
