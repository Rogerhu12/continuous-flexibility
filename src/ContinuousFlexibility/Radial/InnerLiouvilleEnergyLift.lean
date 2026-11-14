module

public import ContinuousFlexibility.Radial.InnerLiouvillePoissonTransport
public import ContinuousFlexibility.Radial.InnerRadialEnergyDomain

/-!
# The actual normalized gradient lift

For the normalized model value f and its derivative d, the physical
gradient has model isometric coordinate d-(s'/s)f. This gives a bounded
map on the actual L² spaces. The only drift bound needed to define it
is derived from positivity and smoothness on the compact retained cell.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem exists_innerLiouvilleDriftBound {s : ℝ → ℝ} {a b : ℝ}
    (hs : ContDiff ℝ ∞ s) (hsp : ∀ x ∈ Icc a b, 0 < s x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b, |deriv s x / s x| ≤ C := by
  have hc : ContinuousOn (fun x => deriv s x / s x) (Icc a b) :=
    (contDiff_infty_iff_deriv.mp hs).2.continuous.continuousOn.div
      hs.continuous.continuousOn (fun x hx => (hsp x hx).ne')
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hc
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro x hx
  simpa only [Real.norm_eq_abs] using (hC x hx).trans (le_max_right 0 C)

def innerLiouvilleDriftMultiplier (s : ℝ → ℝ) (a b : ℝ)
    (hs : ContDiff ℝ ∞ s) (hsp : ∀ x ∈ Icc a b, 0 < s x) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  innerLiouvilleVelocityMultiplier s a b hs
    (Classical.choose (exists_innerLiouvilleDriftBound hs hsp))
    (Classical.choose_spec (exists_innerLiouvilleDriftBound hs hsp)).1
    (Classical.choose_spec (exists_innerLiouvilleDriftBound hs hsp)).2

theorem innerLiouvilleDriftMultiplier_ae (s : ℝ → ℝ) (a b : ℝ)
    (hs : ContDiff ℝ ∞ s) (hsp : ∀ x ∈ Icc a b, 0 < s x) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (innerLiouvilleDriftMultiplier s a b hs hsp f : ℝ → ℝ) =ᵐ[volume]
      (fun x => innerLiouvilleModelVelocity s a b x * f x) := by
  unfold innerLiouvilleDriftMultiplier
  exact innerLiouvilleVelocityMultiplier_ae _ _ _ _ _ _ _ f

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)

/-- The normalized physical gradient of the same model field. -/
def innerLiouvilleGradientLift :
    (Lp ℝ 2 (volume : Measure ℝ) × Lp ℝ 2 (volume : Measure ℝ)) →L[ℝ] Lp ℝ 2 (radialHilbertMeasure D) :=
  (innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b))).comp
    (((innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm :
      Lp ℝ 2 (volume.restrict (Ioo a b)) →L[ℝ]
        Lp ℝ 2 ((radialHilbertMeasure D).restrict (Ioo (R a) (R b)))).comp
      ((LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b)).comp
        (ContinuousLinearMap.snd ℝ (Lp ℝ 2 (volume : Measure ℝ)) (Lp ℝ 2 (volume : Measure ℝ)) -
          (innerLiouvilleDriftMultiplier s a b hs (fun x hx => (hp x hx).2.2)).comp
            (ContinuousLinearMap.fst ℝ (Lp ℝ 2 (volume : Measure ℝ)) (Lp ℝ 2 (volume : Measure ℝ))))))

theorem innerLiouvilleGradientLift_apply (f d : Lp ℝ 2 (volume : Measure ℝ)) :
    innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d) =
      innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b))
        ((innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm
          (LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b)
            (d - innerLiouvilleDriftMultiplier s a b hs (fun x hx => (hp x hx).2.2) f))) := by
  unfold innerLiouvilleGradientLift
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    LinearIsometryEquiv.coe_coe'']

theorem innerLiouvilleGradientLift_pullback_ae (f d : Lp ℝ 2 (volume : Measure ℝ)) :
    (fun x => innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d) (R x)) =ᵐ[
      volume.restrict (Ioo a b)]
      (fun x => (d x - (deriv s x / s x) * f x) /
        innerLiouvilleIntervalAmplitude R s lam x) := by
  let M := innerLiouvilleDriftMultiplier s a b hs (fun x hx => (hp x hx).2.2)
  let g := LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b) (d - M f)
  let u := (innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm g
  have hext := innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw
    (ae_restrict_of_ae (innerL2ZeroExtension_ae (radialHilbertMeasure D)
      (Ioo (R a) (R b)) measurableSet_Ioo u))
  have he := innerLiouvilleIntervalEquiv_symm_pullback_ae D hab hlam hR hs hp hcore hw g
  have hg := LpToLpRestrictCLM_coeFn ℝ (Ioo a b) (d - M f)
  have hsub := ae_restrict_of_ae (s := Ioo a b) (Lp.coeFn_sub d (M f))
  have hM := ae_restrict_of_ae (s := Ioo a b)
    (innerLiouvilleDriftMultiplier_ae s a b hs (fun x hx => (hp x hx).2.2) f)
  rw [innerLiouvilleGradientLift_apply]
  change (fun x => innerL2ZeroExtension (radialHilbertMeasure D)
    (Ioo (R a) (R b)) u (R x)) =ᵐ[volume.restrict (Ioo a b)] _
  filter_upwards [hext, he, hg, hsub, hM, ae_restrict_mem measurableSet_Ioo] with
    x hxt he' hg' hsub' hM' hx
  have hx' := Ioo_subset_Icc_self hx
  have hm := morseCell_strictMonoOn hR (fun y hy => (hp y hy).2.1)
  have hRx : R x ∈ Ioo (R a) (R b) :=
    ⟨hm (left_mem_Icc.mpr hab) hx' hx.1,
      hm hx' (right_mem_Icc.mpr hab) hx.2⟩
  simp only [Pi.sub_apply] at hsub'
  rw [hxt, indicator_of_mem hRx, he', hg', hsub', hM',
    innerLiouvilleModelVelocity, indicator_of_mem hx]

theorem innerLiouvilleGradientLift_support_ae (f d : Lp ℝ 2 (volume : Measure ℝ)) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo (R a) (R b) →
      innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d) r = 0 := by
  rw [innerLiouvilleGradientLift_apply]
  filter_upwards [innerL2ZeroExtension_ae (radialHilbertMeasure D)
    (Ioo (R a) (R b)) measurableSet_Ioo
      ((innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm
        (LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b)
          (d - innerLiouvilleDriftMultiplier s a b hs (fun x hx => (hp x hx).2.2) f)))] with r hr
  intro hout
  rw [hr, indicator_of_notMem hout]

variable (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)

def innerLiouvilleH1Lift :
    (Lp ℝ 2 (volume : Measure ℝ) × Lp ℝ 2 (volume : Measure ℝ)) →L[ℝ] InnerRadialH1Pair D :=
  ((innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv).comp
    (ContinuousLinearMap.fst ℝ (Lp ℝ 2 (volume : Measure ℝ)) (Lp ℝ 2 (volume : Measure ℝ)))).prod
      (innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw)

theorem innerLiouvilleH1Lift_apply (f d : Lp ℝ 2 (volume : Measure ℝ)) :
    innerLiouvilleH1Lift D hab hlam hR hs hp hcore hw U hU hv (f, d) =
      (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f,
        innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d)) := by
  unfold innerLiouvilleH1Lift
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst']

/-- The potential coordinate of the model energy triple is retained by
the model domain, while the actual physical H1 map needs its first two
coordinates only. -/
def innerLiouvilleEnergyLift :
    (Lp ℝ 2 (volume : Measure ℝ) × Lp ℝ 2 (volume : Measure ℝ) × Lp ℝ 2 (volume : Measure ℝ)) →L[ℝ] InnerRadialH1Pair D :=
  (innerLiouvilleH1Lift D hab hlam hR hs hp hcore hw U hU hv).comp
    ((ContinuousLinearMap.fst ℝ (Lp ℝ 2 (volume : Measure ℝ)) (Lp ℝ 2 (volume : Measure ℝ) × Lp ℝ 2 (volume : Measure ℝ))).prod
      ((ContinuousLinearMap.fst ℝ (Lp ℝ 2 (volume : Measure ℝ)) (Lp ℝ 2 (volume : Measure ℝ))).comp
        (ContinuousLinearMap.snd ℝ (Lp ℝ 2 (volume : Measure ℝ)) (Lp ℝ 2 (volume : Measure ℝ) × Lp ℝ 2 (volume : Measure ℝ)))))

theorem innerLiouvilleEnergyLift_apply (f d q : Lp ℝ 2 (volume : Measure ℝ)) :
    innerLiouvilleEnergyLift D hab hlam hR hs hp hcore hw U hU hv (f, d, q) =
      (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f,
        innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d)) := by
  unfold innerLiouvilleEnergyLift
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', innerLiouvilleH1Lift_apply]

end ContinuousFlexibility.Radial
