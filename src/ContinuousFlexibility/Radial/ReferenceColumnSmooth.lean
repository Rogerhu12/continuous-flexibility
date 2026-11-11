import ContinuousFlexibility.Radial.R11bRadialTests
import ContinuousFlexibility.Radial.ReferenceModerateCoefficients

/-!
# Smoothness and support of the actual border column

The quotient by r has its apparent singularity in the flat zero region.
The column is genuinely smooth on all of ℝ and its topological support is
contained in that of the actual cutoff. Strict inclusion of the latter in
the open core is not inferred from a mere function-support inclusion.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem reference_contDiff_flat_deriv_div {D : ReferenceData} (ha : 0 < D.a)
    {w : ℝ → ℝ} (hw : EndpointFlat D w) :
    ContDiff ℝ ∞ (fun r => deriv w r / r) := by
  have hdw : ContDiff ℝ ∞ (deriv w) := (contDiff_infty_iff_deriv.mp hw.1).2
  have hz (r : ℝ) (hr : r < D.a) : deriv w r = 0 := by
    have he : w =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hr] with t ht
      exact hw.2 t (Or.inl ht.le)
    rw [he.deriv_eq]
    exact deriv_const r 0
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r = 0
  · subst r
    have he : (fun t : ℝ => deriv w t / t) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds ha] with t ht
      rw [hz t ht, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq he.symm
  · exact hdw.contDiffAt.div contDiffAt_id hr

theorem referenceColumn_contDiff {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D) :
    ContDiff ℝ ∞ (referenceColumn D) := by
  have hA : EndpointFlat D (fun r => D.w r * D.chi r) := by
    refine ⟨hgeom.2.2.1.1.mul hborder.1, fun r hr => ?_⟩
    change D.w r * D.chi r = 0
    rw [hgeom.2.2.1.2 r hr, zero_mul]
  have hφ' : ContDiff ℝ ∞ (deriv D.phi) :=
    (contDiff_infty_iff_deriv.mp hgeom.2.2.2.1.1).2
  have hflux : ContDiff ℝ ∞
      (deriv (fun r => (D.w r * D.chi r) * deriv D.phi r)) :=
    (contDiff_infty_iff_deriv.mp (hA.1.mul hφ')).2
  change ContDiff ℝ ∞ (fun r =>
    deriv (fun t => (D.w t * D.chi t) * deriv D.phi t) r -
      4 * deriv (fun t => D.w t * D.chi t) r / r * D.phi r)
  simp_rw [mul_div_assoc]
  exact hflux.sub ((contDiff_const.mul (reference_contDiff_flat_deriv_div hgeom.1 hA)).mul
    hgeom.2.2.2.1.1)

theorem referenceColumn_tsupport_subset {D : ReferenceData} :
    tsupport (referenceColumn D) ⊆ tsupport D.chi := by
  apply closure_minimal _ (isClosed_tsupport D.chi)
  intro r hr
  by_contra hnot
  have heA : (fun t => D.w t * D.chi t) =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isClosed_tsupport D.chi).isOpen_compl.mem_nhds hnot] with t ht
    rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]
  have heF : (fun t => (D.w t * D.chi t) * deriv D.phi t) =ᶠ[𝓝 r]
      (fun _ => (0 : ℝ)) := heA.mono fun t ht => by rw [ht, zero_mul]
  have hzA : deriv (fun t => D.w t * D.chi t) r = 0 := by
    rw [heA.deriv_eq]
    exact deriv_const r 0
  have hzF : deriv (fun t => (D.w t * D.chi t) * deriv D.phi t) r = 0 := by
    rw [heF.deriv_eq]
    exact deriv_const r 0
  apply hr
  change deriv (fun t => (D.w t * D.chi t) * deriv D.phi t) r -
    4 * deriv (fun t => D.w t * D.chi t) r / r * D.phi r = 0
  rw [hzA, hzF]
  simp only [mul_zero, zero_div, zero_mul, sub_zero]

theorem referenceColumn_hasCompactSupport {D : ReferenceData} (hborder : RadialTrueBorder D) :
    HasCompactSupport (referenceColumn D) :=
  hborder.2.1.of_isClosed_subset (isClosed_tsupport (referenceColumn D))
    referenceColumn_tsupport_subset

end ContinuousFlexibility.Radial
