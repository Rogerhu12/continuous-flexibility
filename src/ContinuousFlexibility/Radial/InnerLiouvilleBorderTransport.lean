import ContinuousFlexibility.Radial.InnerLiouvillePoissonTransport

/-!
# The actual temporary physical border

The physical column is the inverse-adjoint image of the model column,
not its field lift. Its local value is
g_model/(12*sqrt(lam)*s*(R'/R)^2). Hence the same scalar row is preserved
exactly. Reciprocal velocity is bounded on this finite positive cell
by compactness, with no additional analytic hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

def innerLiouvilleInverseVelocity (R : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  (Ioo a b).indicator (fun x => R x / deriv R x)

theorem innerLiouvilleInverseVelocity_measurable {R : ℝ → ℝ}
    (hR : ContDiff ℝ ∞ R) (a b : ℝ) :
    Measurable (innerLiouvilleInverseVelocity R a b) :=
  (hR.continuous.measurable.div
    (contDiff_infty_iff_deriv.mp hR).2.continuous.measurable).indicator measurableSet_Ioo

theorem exists_innerLiouvilleInverseVelocity_bound {R : ℝ → ℝ} {a b : ℝ}
    (hR : ContDiff ℝ ∞ R) (hv : ∀ x ∈ Icc a b, 0 < deriv R x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |innerLiouvilleInverseVelocity R a b x| ≤ C := by
  have hc : ContinuousOn (fun x => R x / deriv R x) (Icc a b) :=
    hR.continuous.continuousOn.div
      (contDiff_infty_iff_deriv.mp hR).2.continuous.continuousOn
      (fun x hx => (hv x hx).ne')
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hc
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro x
  unfold innerLiouvilleInverseVelocity
  by_cases hx : x ∈ Ioo a b
  · rw [indicator_of_mem hx]
    simpa only [Real.norm_eq_abs] using
      (hC x (Ioo_subset_Icc_self hx)).trans (le_max_right 0 C)
  · rw [indicator_of_notMem hx, abs_zero]
    exact le_max_left _ _

def innerLiouvilleInverseVelocityMultiplier (R : ℝ → ℝ) (a b : ℝ)
    (hR : ContDiff ℝ ∞ R) (hv : ∀ x ∈ Icc a b, 0 < deriv R x) :
    Lp ℝ 2 volume →L[ℝ] Lp ℝ 2 volume :=
  innerWeightMultiplier volume (innerLiouvilleInverseVelocity R a b)
    (innerLiouvilleInverseVelocity_measurable hR a b)
    (Classical.choose (exists_innerLiouvilleInverseVelocity_bound hR hv))
    (Classical.choose_spec (exists_innerLiouvilleInverseVelocity_bound hR hv)).2

theorem innerLiouvilleInverseVelocityMultiplier_ae (R : ℝ → ℝ) (a b : ℝ)
    (hR : ContDiff ℝ ∞ R) (hv : ∀ x ∈ Icc a b, 0 < deriv R x) (f : Lp ℝ 2 volume) :
    (innerLiouvilleInverseVelocityMultiplier R a b hR hv f : ℝ → ℝ) =ᵐ[volume]
      (fun x => innerLiouvilleInverseVelocity R a b x * f x) := by
  unfold innerLiouvilleInverseVelocityMultiplier
  exact innerWeightMultiplier_ae volume _ _ _ _ f

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)

/-- The inverse-adjoint lift of the actual model border. -/
def innerLiouvilleColumnLift :
    Lp ℝ 2 volume →L[ℝ] Lp ℝ 2 (radialHilbertMeasure D) :=
  (1 / Real.sqrt 12) •
    (innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b))).comp
      (((innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm :
        Lp ℝ 2 (volume.restrict (Ioo a b)) →L[ℝ]
          Lp ℝ 2 ((radialHilbertMeasure D).restrict (Ioo (R a) (R b)))).comp
        ((LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b)).comp
          (innerLiouvilleInverseVelocityMultiplier R a b hR (fun x hx => (hp x hx).2.1))))

theorem innerLiouvilleColumnLift_apply (g : Lp ℝ 2 volume) :
    innerLiouvilleColumnLift D hab hlam hR hs hp hcore hw g =
      (1 / Real.sqrt 12) •
        innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b))
          ((innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm
            (LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b)
              (innerLiouvilleInverseVelocityMultiplier R a b hR
                (fun x hx => (hp x hx).2.1) g))) := by
  unfold innerLiouvilleColumnLift
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_coe'']

theorem innerLiouvilleColumnLift_pullback_ae (g : Lp ℝ 2 volume) :
    (fun x => innerLiouvilleColumnLift D hab hlam hR hs hp hcore hw g (R x)) =ᵐ[
      volume.restrict (Ioo a b)]
      (fun x => g x / (12 * Real.sqrt lam * s x * (deriv R x / R x) ^ 2)) := by
  let M := innerLiouvilleInverseVelocityMultiplier R a b hR (fun x hx => (hp x hx).2.1)
  let f := LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b) (M g)
  let u := (innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm f
  have hsmul := innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw
    (ae_restrict_of_ae (Lp.coeFn_smul (1 / Real.sqrt 12)
      (innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b)) u)))
  have hext := innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw
    (ae_restrict_of_ae (innerL2ZeroExtension_ae (radialHilbertMeasure D)
      (Ioo (R a) (R b)) measurableSet_Ioo u))
  have he := innerLiouvilleIntervalEquiv_symm_pullback_ae D hab hlam hR hs hp hcore hw f
  have hf := LpToLpRestrictCLM_coeFn ℝ (Ioo a b) (M g)
  have hM := ae_restrict_of_ae
    (innerLiouvilleInverseVelocityMultiplier_ae R a b hR (fun x hx => (hp x hx).2.1) g)
  rw [innerLiouvilleColumnLift_apply]
  change (fun x => ((1 / Real.sqrt 12) •
    innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b)) u) (R x)) =ᵐ[
      volume.restrict (Ioo a b)] _
  filter_upwards [hsmul, hext, he, hf, hM, ae_restrict_mem measurableSet_Ioo] with
    x hsm hxt he' hf' hM' hx
  have hx' := Ioo_subset_Icc_self hx
  have hm := morseCell_strictMonoOn hR (fun y hy => (hp y hy).2.1)
  have hRx : R x ∈ Ioo (R a) (R b) :=
    ⟨hm (left_mem_Icc.mpr hab) hx' hx.1,
      hm hx' (right_mem_Icc.mpr hab) hx.2⟩
  simp only [Pi.smul_apply, smul_eq_mul] at hsm
  rw [hsm, hxt, indicator_of_mem hRx, he', hf', hM',
    innerLiouvilleInverseVelocity, indicator_of_mem hx, innerLiouvilleIntervalAmplitude,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
  calc
    _ = g x / ((Real.sqrt 12) ^ 2 * Real.sqrt lam * s x *
        (deriv R x / R x) ^ 2) := by
      field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne',
        (Real.sqrt_pos.mpr hlam).ne', (hp x hx').1.ne',
        (hp x hx').2.1.ne', (hp x hx').2.2.ne']
      <;> ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]

variable (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)

theorem innerLiouvilleSource_columnLift (g : Lp ℝ 2 volume) :
    innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv
      (innerLiouvilleColumnLift D hab hlam hR hs hp hcore hw g) =
      innerL2ZeroExtension volume (Ioo a b) (LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b) g) := by
  apply Lp.ext
  filter_upwards
    [innerLiouvilleSource_ae D hab hlam hR hs hp hcore hw U hU hv
      (innerLiouvilleColumnLift D hab hlam hR hs hp hcore hw g),
      ae_imp_of_ae_restrict
        (innerLiouvilleColumnLift_pullback_ae D hab hlam hR hs hp hcore hw g),
      innerL2ZeroExtension_restriction_ae volume (Ioo a b) measurableSet_Ioo g] with
        x hs' hc hx
  rw [hs', hx]
  by_cases hi : x ∈ Ioo a b
  · rw [indicator_of_mem hi, indicator_of_mem hi, hc hi]
    have hp' := hp x (Ioo_subset_Icc_self hi)
    field_simp [(Real.sqrt_pos.mpr hlam).ne', hp'.1.ne', hp'.2.1.ne', hp'.2.2.ne']
  · rw [indicator_of_notMem hi, indicator_of_notMem hi]

theorem innerLiouvilleSource_columnLift_of_support (g : Lp ℝ 2 volume)
    (hg : (g : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0)) :
    innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv
      (innerLiouvilleColumnLift D hab hlam hR hs hp hcore hw g) = g := by
  rw [innerLiouvilleSource_columnLift]
  apply Lp.ext
  filter_upwards [innerL2ZeroExtension_restriction_ae volume (Ioo a b) measurableSet_Ioo g,
    ae_imp_of_ae_restrict hg] with x hx hg'
  rw [hx]
  by_cases hi : x ∈ Ioo a b
  · rw [indicator_of_mem hi]
  · rw [indicator_of_notMem hi]
    exact (hg' hi).symm

/-- The single physical scalar row equals the original model scalar
row, for every model vector, including the true Poisson columns. -/
theorem innerLiouvilleColumnLift_field_pairing (g f : Lp ℝ 2 volume)
    (hg : (g : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0)) :
    ⟪innerLiouvilleColumnLift D hab hlam hR hs hp hcore hw g,
      innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f⟫_ℝ = ⟪g, f⟫_ℝ := by
  rw [← innerLiouvilleSource_inner,
    innerLiouvilleSource_columnLift_of_support D hab hlam hR hs hp hcore hw U hU hv g hg]

end ContinuousFlexibility.Radial
