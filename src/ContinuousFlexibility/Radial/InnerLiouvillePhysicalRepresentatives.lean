module

public import ContinuousFlexibility.Radial.InnerLiouvillePhysicalOperators

/-!
# Representatives of the actual Liouville lift and source

These formulas identify the previously constructed continuous linear
maps on their genuine Lp quotients. The source coefficient is exactly
12*sqrt(lam)*s*(R'/R)^2; the field coefficient is its energy-dual
normalization 1/(sqrt(lam)*s).
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

private theorem real_adjoint_smul {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (c : ℝ) (A : E →L[ℝ] F) :
    (c • A).adjoint = c • A.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_left]

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)

theorem innerLiouvilleSource_apply (F : Lp ℝ 2 (radialHilbertMeasure D)) :
    innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv F =
      Real.sqrt 12 • innerLiouvilleVelocityMultiplier R a b hR U hU hv
        (innerL2ZeroExtension volume (Ioo a b)
          (innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw
            (LpToLpRestrictCLM ℝ ℝ ℝ (radialHilbertMeasure D) 2 (Ioo (R a) (R b)) F))) := by
  unfold innerLiouvilleSource innerLiouvilleFieldLift
  simp only [real_adjoint_smul, ContinuousLinearMap.adjoint_comp,
    innerL2ZeroExtension_adjoint, innerLiouvilleVelocityMultiplier_adjoint,
    LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_coe'', innerL2ZeroExtension, ContinuousLinearMap.adjoint_adjoint]

theorem innerLiouvilleFieldLift_pullback_ae (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (fun x => innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f (R x)) =ᵐ[
      volume.restrict (Ioo a b)] (fun x => f x / (Real.sqrt lam * s x)) := by
  let V := innerLiouvilleVelocityMultiplier R a b hR U hU hv
  let g := LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b) (V f)
  let u := (innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm g
  have hsmul := innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw
    (ae_restrict_of_ae (Lp.coeFn_smul (Real.sqrt 12)
      (innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b)) u)))
  have hext := innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw
    (ae_restrict_of_ae (innerL2ZeroExtension_ae (radialHilbertMeasure D)
      (Ioo (R a) (R b)) measurableSet_Ioo u))
  have he := innerLiouvilleIntervalEquiv_symm_pullback_ae D hab hlam hR hs hp hcore hw g
  have hg := LpToLpRestrictCLM_coeFn ℝ (Ioo a b) (V f)
  have hV := ae_restrict_of_ae (s := Ioo a b)
    (innerLiouvilleVelocityMultiplier_ae R a b hR U hU hv f)
  rw [innerLiouvilleFieldLift_apply]
  change (fun x => (Real.sqrt 12 •
    innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b)) u) (R x)) =ᵐ[
      volume.restrict (Ioo a b)] (fun x => f x / (Real.sqrt lam * s x))
  filter_upwards [hsmul, hext, he, hg, hV, ae_restrict_mem measurableSet_Ioo] with
    x hsm hxt he' hg' hV' hx
  have hx' := Ioo_subset_Icc_self hx
  have hm := morseCell_strictMonoOn hR (fun y hy => (hp y hy).2.1)
  have hRx : R x ∈ Ioo (R a) (R b) :=
    ⟨hm (left_mem_Icc.mpr hab) hx' hx.1,
      hm hx' (right_mem_Icc.mpr hab) hx.2⟩
  simp only [Pi.smul_apply, smul_eq_mul] at hsm
  rw [hsm, hxt, indicator_of_mem hRx, he', hg', hV']
  rw [innerLiouvilleModelVelocity, indicator_of_mem hx, innerLiouvilleIntervalAmplitude,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
  have h12 : Real.sqrt (12 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hlam' : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.mpr hlam).ne'
  field_simp [h12, hlam', (hp x hx').1.ne', (hp x hx').2.1.ne', (hp x hx').2.2.ne']
  <;> ring

theorem innerLiouvilleFieldLift_support_ae (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo (R a) (R b) →
      innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f r = 0 := by
  let u := (innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm
    (LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b)
      (innerLiouvilleVelocityMultiplier R a b hR U hU hv f))
  have hsmul := Lp.coeFn_smul (Real.sqrt 12)
    (innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b)) u)
  have hext := innerL2ZeroExtension_ae (radialHilbertMeasure D)
    (Ioo (R a) (R b)) measurableSet_Ioo u
  rw [innerLiouvilleFieldLift_apply]
  filter_upwards [hsmul, hext] with r hsm hxt
  intro hr
  simp only [Pi.smul_apply, smul_eq_mul] at hsm
  rw [hsm, hxt, indicator_of_notMem hr, mul_zero]

theorem innerLiouvilleSource_ae (F : Lp ℝ 2 (radialHilbertMeasure D)) :
    (innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv F : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator
        (fun x => 12 * Real.sqrt lam * s x * (deriv R x / R x) ^ 2 * F (R x)) := by
  let FJ := LpToLpRestrictCLM ℝ ℝ ℝ (radialHilbertMeasure D) 2 (Ioo (R a) (R b)) F
  let z := innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw FJ
  let zext := innerL2ZeroExtension volume (Ioo a b) z
  have hsmul := Lp.coeFn_smul (Real.sqrt 12)
    (innerLiouvilleVelocityMultiplier R a b hR U hU hv zext)
  have hV := innerLiouvilleVelocityMultiplier_ae R a b hR U hU hv zext
  have hext := innerL2ZeroExtension_ae volume (Ioo a b) measurableSet_Ioo z
  have he := ae_imp_of_ae_restrict
    (innerLiouvilleIntervalEquiv_ae D hab hlam hR hs hp hcore hw FJ)
  have hF := ae_imp_of_ae_restrict
    (innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw
      (LpToLpRestrictCLM_coeFn ℝ (Ioo (R a) (R b)) F))
  rw [innerLiouvilleSource_apply]
  change ((Real.sqrt 12 • innerLiouvilleVelocityMultiplier R a b hR U hU hv zext :
    RadialL2) : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator
      (fun x => 12 * Real.sqrt lam * s x * (deriv R x / R x) ^ 2 * F (R x))
  filter_upwards [hsmul, hV, hext, he, hF] with x hsm hV' hext' he' hF'
  simp only [Pi.smul_apply, smul_eq_mul] at hsm
  rw [hsm, hV']
  by_cases hx : x ∈ Ioo a b
  · rw [innerLiouvilleModelVelocity, indicator_of_mem hx, hext', indicator_of_mem hx,
      he' hx, hF' hx, indicator_of_mem hx, innerLiouvilleIntervalAmplitude,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    calc
      _ = (Real.sqrt 12) ^ 2 * Real.sqrt lam * s x *
          (deriv R x / R x) ^ 2 * F (R x) := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
  · rw [innerLiouvilleModelVelocity, indicator_of_notMem hx, indicator_of_notMem hx,
      zero_mul, mul_zero]

end ContinuousFlexibility.Radial
