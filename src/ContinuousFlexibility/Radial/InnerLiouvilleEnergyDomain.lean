import ContinuousFlexibility.Radial.InnerLiouvilleEnergyLift
import ContinuousFlexibility.Radial.InnerRadialH1Density

/-!
# The actual model energy closure maps to the physical H1 closure

The proof starts with the original Schrodinger smooth core, constructs
the radial representative smooth at both cuts, identifies its actual
normalized derivative, and uses physical endpoint-cutoff density.
Continuity then carries the entire original model closure into the
same physical zero-endpoint domain used by finite-chain gluing.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)

theorem innerLiouvilleGradientLift_eq_indicator
    (f d : Lp ℝ 2 volume) (p u : ℝ → ℝ)
    (hpp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    (hfp : (f : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] p)
    (hdp : (d : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] deriv p)
    (hureg : ∀ r ∈ Icc (R a) (R b), ContDiffAt ℝ ∞ u r)
    (hnear : ∀ x ∈ Icc a b, (fun y => u (R y)) =ᶠ[𝓝 x]
      (fun y => p y / (Real.sqrt lam * s y))) :
    (innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d) : ℝ → ℝ) =ᵐ[
      radialHilbertMeasure D] (Ioo (R a) (R b)).indicator (innerGapGradientField u) := by
  have hgc := innerGapGradientField_continuousOn_of_contDiffAt hureg
  have hlocal : (innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d) :
      ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict (Ioo (R a) (R b))]
      innerGapGradientField u := by
    apply innerLiouvilleInterval_pushforward_ae D hab hlam hR hs hp hcore hw
      ((Lp.memLp _).restrict (Ioo (R a) (R b))).aestronglyMeasurable
      ((hgc.mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo).aestronglyMeasurable
    filter_upwards [innerLiouvilleGradientLift_pullback_ae D hab hlam hR hs hp hcore hw f d,
      hfp, hdp, ae_restrict_mem measurableSet_Ioo] with x hg hfx hdx hx
    have hx' := Ioo_subset_Icc_self hx
    have hm := (morseCell_strictMonoOn hR (fun y hy => (hp y hy).2.1)).monotoneOn
    have hRx : R x ∈ Icc (R a) (R b) :=
      ⟨hm (left_mem_Icc.mpr hab) hx' hx'.1,
        hm hx' (right_mem_Icc.mpr hab) hx'.2⟩
    have hderiv := innerLiouvilleSmoothRepresentative_deriv hlam
      (hR.differentiable (by simp) x) (hs.differentiable (by simp) x)
      ((hpp x hx').differentiableAt (by simp))
      ((hureg (R x) hRx).differentiableAt (by simp)) (hp x hx').2.2 (hnear x hx')
    rw [hg, hfx, hdx, ← hderiv]
    unfold innerLiouvilleIntervalAmplitude innerGapGradientField
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne',
      (Real.sqrt_pos.mpr hlam).ne', (hp x hx').1.ne',
      (hp x hx').2.1.ne', (hp x hx').2.2.ne']
    <;> ring
  filter_upwards [ae_imp_of_ae_restrict hlocal,
    innerLiouvilleGradientLift_support_ae D hab hlam hR hs hp hcore hw f d] with r hi ho
  by_cases hr : r ∈ Ioo (R a) (R b)
  · rw [indicator_of_mem hr]
    exact hi hr
  · rw [indicator_of_notMem hr]
    exact ho hr

include hab hlam hR hp hw in
theorem innerLiouville_radial_weight_pos :
    ∀ r ∈ Ioo (R a) (R b), 0 < D.w r := by
  have hm := morseCell_strictMonoOn hR (fun x hx => (hp x hx).2.1)
  rw [← hR.continuous.continuousOn.image_Ioo_of_strictMonoOn hab hm]
  rintro _ ⟨x, hx, rfl⟩
  rw [hw x (Ioo_subset_Icc_self hx)]
  exact mul_pos (mul_pos hlam (sq_pos_of_pos (hp x (Ioo_subset_Icc_self hx)).2.2))
    (hp x (Ioo_subset_Icc_self hx)).2.1

omit hab in
theorem innerLiouvilleEnergyLift_core (hab : a < b) (hDw : Continuous D.w)
    (U : ℝ) (hU : 0 ≤ U) (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)
    (V : ℝ → ℝ) (q : Lp ℝ 2 volume × Lp ℝ 2 volume × Lp ℝ 2 volume)
    (hq : q ∈ IntervalEnergyCore V a b) :
    innerLiouvilleEnergyLift D hab.le hlam hR hs hp hcore hw U hU hv q ∈
      innerRadialH1Zero D (R a) (R b) := by
  rcases q with ⟨f, d, q⟩
  rcases hq with ⟨⟨p, hpp, _hpc, hfp, hdp, _hqp⟩, hfout⟩
  have hpout : p =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0) :=
    (ae_restrict_of_ae hfp).symm.trans hfout
  have hpzero := innerDirichlet_representative_zero_outside hab hpp.continuous hpout
  have hpa : p a = 0 := hpzero (by simp : a ∈ (Ioo a b)ᶜ)
  have hpb : p b = 0 := hpzero (by simp : b ∈ (Ioo a b)ᶜ)
  obtain ⟨u, hnear, hureg⟩ := exists_innerLiouvilleSmoothRepresentative hab.le hlam hR hs hp
    (fun x _hx => hpp.contDiffAt)
  have hUa : u (R a) = 0 := by
    rw [(hnear a (left_mem_Icc.mpr hab.le)).eq_of_nhds, hpa, zero_div]
  have hUb : u (R b) = 0 := by
    rw [(hnear b (right_mem_Icc.mpr hab.le)).eq_of_nhds, hpb, zero_div]
  have hvalue := innerLiouvilleFieldLift_eq_indicator D hab.le hlam hR hs hp hcore hw U hU hv
    f p u (ae_restrict_of_ae hfp)
    (fun r hr => (hureg r hr).continuousAt.continuousWithinAt)
    (fun x hx => (hnear x hx).eq_of_nhds)
  have hgradient := innerLiouvilleGradientLift_eq_indicator D hab.le hlam hR hs hp hcore hw
    f d p u (fun x _hx => hpp.contDiffAt) (ae_restrict_of_ae hfp)
      (ae_restrict_of_ae hdp) hureg hnear
  have hm := morseCell_strictMonoOn hR (fun x hx => (hp x hx).2.1)
  have hrange : R a < R b := hm (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  rw [innerLiouvilleEnergyLift_apply]
  exact innerRadialH1Zero_of_smooth_zero_endpoints D hDw hrange
    (hp a (left_mem_Icc.mpr hab.le)).1 hcore
    (fun r hr => (innerLiouville_radial_weight_pos D hab.le hlam hR hp hw r hr).le)
    hureg hUa hUb hvalue hgradient

omit hab in
theorem innerLiouvilleEnergyLift_closure (hab : a < b) (hDw : Continuous D.w)
    (U : ℝ) (hU : 0 ≤ U) (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)
    (V : ℝ → ℝ) (q : Lp ℝ 2 volume × Lp ℝ 2 volume × Lp ℝ 2 volume)
    (hq : q ∈ closure (IntervalEnergyCore V a b)) :
    innerLiouvilleEnergyLift D hab.le hlam hR hs hp hcore hw U hU hv q ∈
      innerRadialH1Zero D (R a) (R b) := by
  have hclosed : IsClosed {v |
      innerLiouvilleEnergyLift D hab.le hlam hR hs hp hcore hw U hU hv v ∈
        innerRadialH1Zero D (R a) (R b)} :=
    (innerRadialH1Zero D (R a) (R b)).isClosed.preimage
      (innerLiouvilleEnergyLift D hab.le hlam hR hs hp hcore hw U hU hv).continuous
  exact closure_minimal
    (fun v hv' => innerLiouvilleEnergyLift_core D hlam hR hs hp hcore hw hab hDw U hU hv V v hv')
    hclosed hq

end ContinuousFlexibility.Radial
