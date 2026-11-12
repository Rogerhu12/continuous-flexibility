import ContinuousFlexibility.Radial.InnerLiouvilleBorderTransport
import ContinuousFlexibility.Radial.InnerLiouvillePotentialTransport
import ContinuousFlexibility.Radial.InnerRadialSmoothGreen
import ContinuousFlexibility.Radial.Liouville

/-!
# The actual physical equation of a normalized model Poisson field

The source term is the same inverse-adjoint column used in the scalar
row. The pointwise Liouville identity and the actual change of measure
identify its physical L² class with the classical radial differential
expression, including the unit-boundary normalization.
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

theorem innerLiouvilleColumnLift_support_ae (g : RadialL2) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo (R a) (R b) →
      innerLiouvilleColumnLift D hab hlam hR hs hp hcore hw g r = 0 := by
  let v := (innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm
    (LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b)
      (innerLiouvilleInverseVelocityMultiplier R a b hR (fun x hx => (hp x hx).2.1) g))
  rw [innerLiouvilleColumnLift_apply]
  filter_upwards [Lp.coeFn_smul (1 / Real.sqrt 12)
      (innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b)) v),
    innerL2ZeroExtension_ae (radialHilbertMeasure D) (Ioo (R a) (R b))
      measurableSet_Ioo v] with r hsm he
  intro hr
  rw [hsm, Pi.smul_apply, smul_eq_mul, he, indicator_of_notMem hr, mul_zero]

variable (hDw : ContDiff ℝ ∞ D.w) (j : ℝ)

include hab hR hs hp hw hDw in
theorem innerLiouvilleUnitPoisson_radialJacobi
    {V p column u : ℝ → ℝ} (t scalar : ℝ)
    (hpp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    (hureg : ∀ r ∈ Icc (R a) (R b), ContDiffAt ℝ ∞ u r)
    (hnear : ∀ x ∈ Icc a b, (fun y => u (R y)) =ᶠ[𝓝 x]
      (fun y => s t * p y / s y))
    (hcoeff : ∀ x ∈ Ioo a b, V x = liouvilleV0 s x - j ^ 2 * liouvilleRho R s x)
    (heq : ∀ x ∈ Ioo a b,
      -deriv (deriv p) x + V x * p x + scalar * column x = 0)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    radialJacobi (j ^ 2) D.w u (R x) =
      (lam * s x / deriv R x) * (s t * scalar * column x) := by
  let ψ : ℝ → ℝ := fun y => s t * p y
  have hx' := Ioo_subset_Icc_self hx
  have hm := (morseCell_strictMonoOn hR (fun y hy => (hp y hy).2.1)).monotoneOn
  have hRx (y : ℝ) (hy : y ∈ Icc a b) : R y ∈ Icc (R a) (R b) :=
    ⟨hm (left_mem_Icc.mpr hab) hy hy.1, hm hy (right_mem_Icc.mpr hab) hy.2⟩
  have hψreg (y : ℝ) (hy : y ∈ Icc a b) : ContDiffAt ℝ ∞ ψ y :=
    contDiffAt_const.mul (hpp y hy)
  have hψd : deriv ψ =ᶠ[𝓝 x] (fun y => s t * deriv p y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (((hpp y (Ioo_subset_Icc_self hy)).differentiableAt (by simp)).hasDerivAt.const_mul
      (s t)).deriv
  have hψdd : deriv (deriv ψ) x = s t * deriv (deriv p) x := by
    rw [hψd.deriv_eq]
    exact ((((hpp x hx').derivWithin (m := ∞) (by simp)).differentiableAt
      (by simp)).hasDerivAt.const_mul (s t)).deriv
  have hsch : liouvilleSchrodinger (j ^ 2) R s ψ x = -(s t * scalar * column x) := by
    unfold liouvilleSchrodinger
    rw [hψdd, ← hcoeff x hx]
    dsimp only [ψ]
    have he := heq x hx
    calc
      _ = s t * (-deriv (deriv p) x + V x * p x) := by ring
      _ = s t * (-scalar * column x) := by congr 1; linarith only [he]
      _ = _ := by ring
  have hweight : (fun y => D.w (R y)) =ᶠ[𝓝 x]
      (fun y => lam * s y ^ 2 * deriv R y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hw y (Ioo_subset_Icc_self hy)
  have hjac := radialJacobi_liouville
    (Eventually.of_forall (hR.differentiable (by simp)))
    (Eventually.of_forall (hs.differentiable (by simp)))
    (show ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ψ y from by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact (hψreg y (Ioo_subset_Icc_self hy)).differentiableAt (by simp))
    (show ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u (R y) from by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact (hureg (R y) (hRx y (Ioo_subset_Icc_self hy))).differentiableAt (by simp))
    ((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp) x)
    ((contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp) x)
    (((hψreg x hx').derivWithin (m := ∞) (by simp)).differentiableAt (by simp))
    (hDw.differentiable (by simp) (R x))
    ((hDw.contDiffAt.mul
      ((hureg (R x) (hRx x hx')).derivWithin (m := ∞) (by simp))).differentiableAt (by simp))
    (hp x hx').1.ne' (hp x hx').2.1.ne' (hp x hx').2.2.ne' hweight (hnear x hx')
    (a := j ^ 2)
  rw [hsch] at hjac
  exact hjac.trans (by ring)

include hDw in
theorem innerLiouvilleUnitPoisson_effectiveSource_ae
    {V p column u : ℝ → ℝ} (t scalar : ℝ) (g : RadialL2)
    (hpp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    (hureg : ∀ r ∈ Icc (R a) (R b), ContDiffAt ℝ ∞ u r)
    (hnear : ∀ x ∈ Icc a b, (fun y => u (R y)) =ᶠ[𝓝 x]
      (fun y => s t * p y / s y))
    (hcoeff : ∀ x ∈ Ioo a b, V x = liouvilleV0 s x - j ^ 2 * liouvilleRho R s x)
    (heq : ∀ x ∈ Ioo a b,
      -deriv (deriv p) x + V x * p x + scalar * column x = 0)
    (hg : (g : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator column) :
    ((0 - (Real.sqrt lam * s t * scalar) •
        innerLiouvilleColumnLift D hab hlam hR hs hp hcore hw g : RadialModeL2 D) : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D] (Ioo (R a) (R b)).indicator
        (fun r => -radialJacobi (j ^ 2) D.w u r / (12 * D.w r / r ^ 2)) := by
  let G := innerLiouvilleColumnLift D hab hlam hR hs hp hcore hw g
  let c : ℝ := Real.sqrt lam * s t * scalar
  let E : RadialModeL2 D := 0 - c • G
  have hE : (E : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (fun r => -(c * G r)) := by
    filter_upwards [Lp.coeFn_sub (0 : RadialModeL2 D) (c • G),
      Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D), Lp.coeFn_smul c G] with r hsub hz hsm
    dsimp only [E]
    rw [hsub, Pi.sub_apply, hz, Pi.zero_apply, hsm,
      Pi.smul_apply, smul_eq_mul, zero_sub]
  have hpos := innerLiouville_radial_weight_pos_closed D hab hlam hR hp hw
  have hleft : 0 < R a := (hp a (left_mem_Icc.mpr hab)).1
  have hden : ContinuousOn (fun r : ℝ => 12 * D.w r / r ^ 2) (Icc (R a) (R b)) :=
    (continuousOn_const.mul hDw.continuous.continuousOn).div (continuousOn_id.pow 2)
      (fun r hr => pow_ne_zero _ (hleft.trans_le hr.1).ne')
  have htarget : ContinuousOn
      (fun r => -radialJacobi (j ^ 2) D.w u r / (12 * D.w r / r ^ 2))
        (Icc (R a) (R b)) :=
    (innerRadialJacobi_continuousOn_local hleft hDw hureg).neg.div hden
      (fun r hr => (div_pos (mul_pos (by norm_num) (hpos r hr))
        (sq_pos_of_pos (hleft.trans_le hr.1))).ne')
  have hlocal : (E : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict (Ioo (R a) (R b))]
      (fun r => -radialJacobi (j ^ 2) D.w u r / (12 * D.w r / r ^ 2)) := by
    apply innerLiouvilleInterval_pushforward_ae D hab hlam hR hs hp hcore hw
      ((Lp.memLp E).restrict (Ioo (R a) (R b))).aestronglyMeasurable
      ((htarget.mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo).aestronglyMeasurable
    have hEp := innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw
      (ae_restrict_of_ae hE)
    filter_upwards [hEp, innerLiouvilleColumnLift_pullback_ae D hab hlam hR hs hp hcore hw g,
      ae_restrict_of_ae hg, ae_restrict_mem measurableSet_Ioo] with x hEx hGx hgx hx
    have hx' := Ioo_subset_Icc_self hx
    rw [hEx, hGx, hgx, indicator_of_mem hx,
      innerLiouvilleUnitPoisson_radialJacobi D hab hR hs hp hw hDw j t scalar
        hpp hureg hnear hcoeff heq hx, hw x hx']
    dsimp only [c]
    field_simp [(Real.sqrt_pos.mpr hlam).ne', hlam.ne', (hp x hx').1.ne',
      (hp x hx').2.1.ne', (hp x hx').2.2.ne']
    <;> ring
  filter_upwards [ae_imp_of_ae_restrict hlocal, hE,
    innerLiouvilleColumnLift_support_ae D hab hlam hR hs hp hcore hw g] with r hi he ho
  by_cases hr : r ∈ Ioo (R a) (R b)
  · rw [indicator_of_mem hr]
    exact hi hr
  · rw [indicator_of_notMem hr, he, ho hr, mul_zero, neg_zero]

end ContinuousFlexibility.Radial
