module

public import ContinuousFlexibility.Analysis.IntervalWeakPrimitive
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Compact radial tests with independent half-interval variations

A continuous weight with distinct endpoint values cannot annihilate the
derivatives of every smooth compactly supported interior test. After
normalization, two disjoint tests produce zero total weighted variation
and a nonzero variation on the left half. This is a scalar fact about the
actual integrals; it does not assert a counterexample to the N04b endpoint.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Distinct endpoint values give a genuine interior derivative test. -/
theorem n04b_exists_nonzero_weighted_derivative_test
    {a b : ℝ} (hab : a < b) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b)) (hne : w a ≠ w b) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo a b ∧ (∫ x, w x * deriv f x) ≠ 0 := by
  classical
  by_contra h
  have hzero : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo a b → (∫ x, w x * deriv f x) = 0 := by
    intro f hf hc hs
    by_contra hn
    exact h ⟨f, hf, hc, hs, hn⟩
  have hloc : LocallyIntegrableOn w (Ioo a b) :=
    (hw.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  obtain ⟨c, hc⟩ := interval_ae_constant_of_integral_deriv_zero hab hloc hzero
  have he : EqOn w (fun _ => c) (Ioo a b) :=
    Measure.eqOn_open_of_ae_eq hc isOpen_Ioo
      (hw.mono Ioo_subset_Icc_self) continuousOn_const
  have hclose : Icc a b ⊆ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
  have he' : EqOn w (fun _ => c) (Icc a b) :=
    he.of_subset_closure hw continuousOn_const Ioo_subset_Icc_self hclose
  exact hne ((he' ⟨le_rfl, hab.le⟩).trans (he' ⟨hab.le, le_rfl⟩).symm)

/-- The same genuine test can be normalized to unit variation. -/
theorem n04b_exists_unit_weighted_derivative_test
    {a b : ℝ} (hab : a < b) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b)) (hne : w a ≠ w b) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo a b ∧ (∫ x, w x * deriv f x) = 1 := by
  obtain ⟨g, hg, hgc, hgs, hJ⟩ :=
    n04b_exists_nonzero_weighted_derivative_test hab hw hne
  let J : ℝ := ∫ x, w x * deriv g x
  let f : ℝ → ℝ := fun x => J⁻¹ * g x
  have hf : ContDiff ℝ ∞ f := contDiff_const.mul hg
  have hfc : HasCompactSupport f := hgc.mul_left (f := fun _ => J⁻¹)
  have hfs : tsupport f ⊆ Ioo a b := tsupport_mul_subset_right.trans hgs
  have hd : deriv f = fun x => J⁻¹ * deriv g x := by
    funext x
    exact ((hg.differentiable (by simp) x).hasDerivAt.const_mul J⁻¹).deriv
  refine ⟨f, hf, hfc, hfs, ?_⟩
  rw [hd]
  calc
    (∫ x, w x * (J⁻¹ * deriv g x)) = J⁻¹ * ∫ x, w x * deriv g x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = 1 := inv_mul_cancel₀ hJ

/-- A weight vanishing at both outer endpoints, but not at the cut,
has a smooth compact perturbation with zero full variation and unit
left-half variation. The two endpoints use the same test theorem. -/
theorem n04b_exists_zero_total_nonzero_half_test
    {a c b : ℝ} (hac : a < c) (hcb : c < b) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b))
    (hwa : w a = 0) (hwb : w b = 0) (hwc : w c ≠ 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo a b ∧ (∫ x, w x * deriv f x) = 0 ∧
      (∫ x in Ioo a c, w x * deriv f x) = 1 := by
  have hLeft : Icc a c ⊆ Icc a b :=
    fun x hx => ⟨hx.1, hx.2.trans hcb.le⟩
  have hRight : Icc c b ⊆ Icc a b :=
    fun x hx => ⟨hac.le.trans hx.1, hx.2⟩
  have hneLeft : w a ≠ w c := by rw [hwa]; exact hwc.symm
  have hneRight : w c ≠ w b := by rw [hwb]; exact hwc
  obtain ⟨f, hf, hfc, hfs, hfI⟩ :=
    n04b_exists_unit_weighted_derivative_test hac (hw.mono hLeft) hneLeft
  obtain ⟨g, hg, hgc, hgs, hgI⟩ :=
    n04b_exists_unit_weighted_derivative_test hcb (hw.mono hRight) hneRight
  have hloc : LocallyIntegrableOn w (Ioo a b) :=
    (hw.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  have hfs' : tsupport f ⊆ Ioo a b :=
    hfs.trans (fun x hx => ⟨hx.1, hx.2.trans hcb⟩)
  have hgs' : tsupport g ⊆ Ioo a b :=
    hgs.trans (fun x hx => ⟨hac.trans hx.1, hx.2⟩)
  have hfder := (contDiff_infty_iff_deriv.mp hf).2
  have hgder := (contDiff_infty_iff_deriv.mp hg).2
  have hfi : Integrable (fun x => w x * deriv f x) :=
    interval_integrable_mul_test hloc hfder.continuous hfc.deriv
      (tsupport_deriv_subset.trans hfs')
  have hgi : Integrable (fun x => w x * deriv g x) :=
    interval_integrable_mul_test hloc hgder.continuous hgc.deriv
      (tsupport_deriv_subset.trans hgs')
  have hd : deriv (fun x => f x - g x) = fun x => deriv f x - deriv g x := by
    funext x
    exact ((hf.differentiable (by simp) x).hasDerivAt.sub
      (hg.differentiable (by simp) x).hasDerivAt).deriv
  have hleftF : (∫ x in Ioo a c, w x * deriv f x) = 1 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hfI
    · intro x hx
      rw [deriv_of_notMem_tsupport (fun hs => hx (hfs hs)), mul_zero]
  have hleftG : (∫ x in Ioo a c, w x * deriv g x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hnot : x ∉ tsupport g := fun hs => (not_lt_of_ge hx.2.le) (hgs hs).1
    simp only [deriv_of_notMem_tsupport hnot, mul_zero, Pi.zero_apply]
  refine ⟨fun x => f x - g x, hf.sub hg, hfc.sub hgc,
    (tsupport_sub f g).trans (union_subset hfs' hgs'), ?_, ?_⟩
  · rw [hd]
    simp_rw [mul_sub]
    rw [integral_sub hfi hgi, hfI, hgI, sub_self]
  · rw [hd]
    simp_rw [mul_sub]
    rw [integral_sub hfi.integrableOn hgi.integrableOn, hleftF, hleftG, sub_zero]

end ContinuousFlexibility.Analysis
