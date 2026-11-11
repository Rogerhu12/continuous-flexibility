import ContinuousFlexibility.Statements.Scalar
import ContinuousFlexibility.Scalar.RectangleParameterIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smooth finite-parameter scalar jets

The parameter and the physical point vary jointly.  In particular, the
partial derivatives below are derivatives of the actual sliced functions,
not independently chosen jet fields.  Local smoothness suffices throughout;
the only coordinate restriction is that the radius be nonzero.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility

open Filter
open scoped ContDiff Topology

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Taking a physical radial partial preserves joint smoothness. -/
theorem contDiffAt_parameter_radialPartial
    {Z : P × PolarPoint → ℝ} {p : P} {x : PolarPoint}
    (hZ : ContDiffAt ℝ ∞ Z (p, x)) :
    ContDiffAt ℝ ∞
      (fun s : P × PolarPoint => radialPartial (fun y => Z (s.1, y)) s.2) (p, x) := by
  have hf : ContDiffAt ℝ ∞
      (fun s : (P × PolarPoint) × PolarPoint => Z (s.1.1, s.2)) ((p, x), x) :=
    hZ.comp ((p, x), x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (hf.fderiv contDiffAt_snd (by simp)).clm_apply contDiffAt_const

/-- Taking a physical angular partial preserves joint smoothness. -/
theorem contDiffAt_parameter_angularPartial
    {Z : P × PolarPoint → ℝ} {p : P} {x : PolarPoint}
    (hZ : ContDiffAt ℝ ∞ Z (p, x)) :
    ContDiffAt ℝ ∞
      (fun s : P × PolarPoint => angularPartial (fun y => Z (s.1, y)) s.2) (p, x) := by
  have hf : ContDiffAt ℝ ∞
      (fun s : (P × PolarPoint) × PolarPoint => Z (s.1.1, s.2)) ((p, x), x) :=
    hZ.comp ((p, x), x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (hf.fderiv contDiffAt_snd (by simp)).clm_apply contDiffAt_const

theorem contDiffAt_parameter_heightRadial
    {Z : P × PolarPoint → ℝ} {p : P} {x : PolarPoint}
    (hZ : ContDiffAt ℝ ∞ Z (p, x)) :
    ContDiffAt ℝ ∞
      (fun s : P × PolarPoint => heightRadial (fun y => Z (s.1, y)) s.2) (p, x) :=
  contDiffAt_parameter_radialPartial hZ

theorem contDiffAt_parameter_heightAngular
    {Z : P × PolarPoint → ℝ} {p : P} {x : PolarPoint}
    (hZ : ContDiffAt ℝ ∞ Z (p, x)) (hr : x.1 ≠ 0) :
    ContDiffAt ℝ ∞
      (fun s : P × PolarPoint => heightAngular (fun y => Z (s.1, y)) s.2) (p, x) :=
  (contDiffAt_parameter_angularPartial hZ).div contDiffAt_snd.fst hr

theorem contDiffAt_parameter_profileEnergy
    {W : P × ℝ → ℝ} {p : P} {x : PolarPoint}
    (hW : ContDiffAt ℝ ∞ W (p, x.1)) :
    ContDiffAt ℝ ∞
      (fun s : P × PolarPoint => profileEnergy (fun r => W (s.1, r)) s.2) (p, x) := by
  exact contDiffAt_const.add ((hW.comp (p, x)
    (contDiffAt_fst.prodMk contDiffAt_snd.fst)).pow 2)

theorem contDiffAt_parameter_polarDiscriminant
    {W : P × ℝ → ℝ} {Z : P × PolarPoint → ℝ} {p : P} {x : PolarPoint}
    (hW : ContDiffAt ℝ ∞ W (p, x.1))
    (hZ : ContDiffAt ℝ ∞ Z (p, x)) (hr : x.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      polarDiscriminant (fun r => W (s.1, r)) (fun y => Z (s.1, y)) s.2) (p, x) := by
  exact ((contDiffAt_parameter_profileEnergy (x := x) hW).mul
    (contDiffAt_const.sub ((contDiffAt_parameter_heightAngular hZ hr).pow 2))).sub
      ((contDiffAt_parameter_heightRadial hZ).pow 2)

theorem contDiffAt_parameter_polarCurvatureNumerator
    {W : P × ℝ → ℝ} {Z : P × PolarPoint → ℝ} {p : P} {x : PolarPoint}
    (hW : ContDiffAt ℝ ∞ W (p, x.1))
    (hZ : ContDiffAt ℝ ∞ Z (p, x)) (hr : x.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      polarCurvatureNumerator (fun r => W (s.1, r)) (fun y => Z (s.1, y)) s.2)
      (p, x) := by
  have hE := contDiffAt_parameter_profileEnergy (x := x) hW
  have hEr := contDiffAt_parameter_radialPartial hE
  have hk := contDiffAt_parameter_heightRadial hZ
  have hp := contDiffAt_parameter_heightAngular hZ hr
  have hkr := contDiffAt_parameter_radialPartial hk
  have hpr := contDiffAt_parameter_radialPartial hp
  have hpt := contDiffAt_parameter_angularPartial hp
  exact (((hk.add (hE.mul hpt)).mul hkr).sub
    ((hE.mul contDiffAt_snd.fst).mul (hpr.pow 2))).sub
      ((hEr.div_const 2).mul ((contDiffAt_const.sub (hp.pow 2)).add (hk.mul hpt)))

theorem contDiffAt_parameter_polarCoordinateResidual
    {W : P × ℝ → ℝ} {Z : P × PolarPoint → ℝ} {p : P} {x : PolarPoint}
    (hW : ContDiffAt ℝ ∞ W (p, x.1))
    (hZ : ContDiffAt ℝ ∞ Z (p, x)) (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant (fun r => W (p, r)) (fun y => Z (p, y)) x) :
    ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      polarCoordinateResidual (fun r => W (s.1, r)) (fun y => Z (s.1, y)) s.2)
      (p, x) := by
  have hd := contDiffAt_parameter_polarDiscriminant hW hZ hr
  have ht : ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      inverseDThreeHalves (polarDiscriminant (fun r => W (s.1, r))
        (fun y => Z (s.1, y)) s.2)) (p, x) :=
    contDiffAt_const.div (hd.mul (hd.sqrt hD.ne'))
      (mul_ne_zero hD.ne' (Real.sqrt_pos.mpr hD).ne')
  exact ((contDiffAt_parameter_polarCurvatureNumerator hW hZ hr).mul ht).div
    contDiffAt_snd.fst hr

theorem contDiffAt_parameter_polarCurvatureNumeratorVariation
    {W : P × ℝ → ℝ} {Z V : P × PolarPoint → ℝ} {p : P} {x : PolarPoint}
    (hW : ContDiffAt ℝ ∞ W (p, x.1))
    (hZ : ContDiffAt ℝ ∞ Z (p, x)) (hV : ContDiffAt ℝ ∞ V (p, x))
    (hr : x.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      polarCurvatureNumeratorVariation (fun r => W (s.1, r))
        (fun y => Z (s.1, y)) (fun y => V (s.1, y)) s.2) (p, x) := by
  have hE := contDiffAt_parameter_profileEnergy (x := x) hW
  have hEr := contDiffAt_parameter_radialPartial hE
  have hk := contDiffAt_parameter_heightRadial hZ
  have hp := contDiffAt_parameter_heightAngular hZ hr
  have hkr := contDiffAt_parameter_radialPartial hk
  have hpr := contDiffAt_parameter_radialPartial hp
  have hpt := contDiffAt_parameter_angularPartial hp
  have hdk := contDiffAt_parameter_heightRadial hV
  have hdp := contDiffAt_parameter_heightAngular hV hr
  have hdkr := contDiffAt_parameter_radialPartial hdk
  have hdpr := contDiffAt_parameter_radialPartial hdp
  have hdpt := contDiffAt_parameter_angularPartial hdp
  exact (((((hdk.add (hE.mul hdpt)).mul hkr).add
    ((hk.add (hE.mul hpt)).mul hdkr)).sub
      (((((contDiffAt_const.mul hE).mul contDiffAt_snd.fst).mul hpr).mul hdpr))).add
        ((hEr.mul hp).mul hdp)).sub
          ((hEr.div_const 2).mul ((hdk.mul hpt).add (hk.mul hdpt)))

theorem contDiffAt_parameter_polarCurvatureNumeratorQuadratic
    {W : P × ℝ → ℝ} {V : P × PolarPoint → ℝ} {p : P} {x : PolarPoint}
    (hW : ContDiffAt ℝ ∞ W (p, x.1))
    (hV : ContDiffAt ℝ ∞ V (p, x)) (hr : x.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      polarCurvatureNumeratorQuadratic (fun r => W (s.1, r))
        (fun y => V (s.1, y)) s.2) (p, x) :=
  (contDiffAt_parameter_polarCurvatureNumerator hW hV hr).add
    ((contDiffAt_parameter_radialPartial (contDiffAt_parameter_profileEnergy (x := x) hW)).div_const 2)

/-- The factored expression is smooth jointly in an arbitrary family of
metrics, base heights, increments and parameters.  Its only base-height
condition is the actual vanishing of the curvature numerator. -/
theorem contDiffAt_parameter_normalizedHeightResidual
    {W : P × ℝ → ℝ} {Z V : P × PolarPoint → ℝ} {q : P → ℝ}
    (hW : ContDiff ℝ ∞ W) (hZ : ContDiff ℝ ∞ Z)
    (hV : ContDiff ℝ ∞ V) (hq : ContDiff ℝ ∞ q)
    {p : P} {x : PolarPoint}
    (hzero : ∀ᶠ p' in 𝓝 p, ∀ y : PolarPoint, y.1 ≠ 0 →
      polarCurvatureNumerator (fun r => W (p', r)) (fun z => Z (p', z)) y = 0)
    (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant (fun r => W (p, r))
      (heightFamily (fun y => Z (p, y)) (fun y => V (p, y)) (q p)) x) :
    ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      normalizedHeightResidual (fun r => W (s.1, r))
        (fun y => Z (s.1, y)) (fun y => V (s.1, y)) (q s.1) s.2) (p, x) := by
  have htrial : ContDiff ℝ ∞ (fun s : P × PolarPoint =>
      heightFamily (fun y => Z (s.1, y)) (fun y => V (s.1, y)) (q s.1) s.2) :=
    hZ.add ((hq.comp contDiff_fst).mul hV)
  have hd := contDiffAt_parameter_polarDiscriminant (p := p) (x := x) hW.contDiffAt htrial.contDiffAt hr
  have ht : ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      inverseDThreeHalves (polarDiscriminant (fun r => W (s.1, r))
        (heightFamily (fun y => Z (s.1, y)) (fun y => V (s.1, y)) (q s.1)) s.2))
      (p, x) :=
    contDiffAt_const.div (hd.mul (hd.sqrt hD.ne'))
      (mul_ne_zero hD.ne' (Real.sqrt_pos.mpr hD).ne')
  have hf := ((contDiffAt_parameter_polarCurvatureNumeratorVariation (p := p) (x := x)
    hW.contDiffAt hZ.contDiffAt hV.contDiffAt hr).add
      (((hq.comp contDiff_fst).contDiffAt).mul
        (contDiffAt_parameter_polarCurvatureNumeratorQuadratic (p := p) (x := x)
          hW.contDiffAt hV.contDiffAt hr))).mul ht
  apply hf.congr_of_eventuallyEq
  have hrad : ∀ᶠ s : P × PolarPoint in 𝓝 (p, x), s.2.1 ≠ 0 :=
    (continuousAt_snd.fst).eventually_ne hr
  have hbase : ∀ᶠ s : P × PolarPoint in 𝓝 (p, x), ∀ y : PolarPoint, y.1 ≠ 0 →
      polarCurvatureNumerator (fun r => W (s.1, r)) (fun z => Z (s.1, z)) y = 0 :=
    continuousAt_fst.eventually hzero
  filter_upwards [hrad, hbase] with s hs hbase
  exact normalizedHeightResidual_eq_factored (fun r => W (s.1, r))
    (hZ.comp (contDiff_const.prodMk contDiff_id))
    (hV.comp (contDiff_const.prodMk contDiff_id)) hs (hbase s.2 hs) (q s.1)

/-- Joint smoothness of the removable source, including variations of the
metric and height and including the construction parameter zero. -/
theorem contDiffAt_parameter_normalizedResidual_radialHeight
    {W H : P × ℝ → ℝ} {U : P × PolarPoint → ℝ}
    (hW : ContDiff ℝ ∞ W) (hH : ContDiff ℝ ∞ H) (hU : ContDiff ℝ ∞ U)
    (hHW : ∀ p r, HasDerivAt (fun s => H (p, s)) (W (p, r)) r)
    {p : P} {q : ℝ} {x : PolarPoint} (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant (fun r => W (p, r))
      (heightFamily (Radial.radialHeightField (fun r => H (p, r)))
        (fun y => U (p, y)) q) x) :
    ContDiffAt ℝ ∞ (fun s : P × ℝ × PolarPoint =>
      normalizedHeightResidual (fun r => W (s.1, r))
        (Radial.radialHeightField (fun r => H (s.1, r)))
        (fun y => U (s.1, y)) s.2.1 s.2.2) (p, q, x) := by
  have hW' : ContDiff ℝ ∞ (fun s : (P × ℝ) × ℝ => W (s.1.1, s.2)) :=
    hW.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hZ' : ContDiff ℝ ∞ (fun s : (P × ℝ) × PolarPoint => H (s.1.1, s.2.1)) :=
    hH.comp (contDiff_fst.fst.prodMk contDiff_snd.fst)
  have hV' : ContDiff ℝ ∞ (fun s : (P × ℝ) × PolarPoint => U (s.1.1, s.2)) :=
    hU.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hzero : ∀ (s : P × ℝ) (y : PolarPoint), y.1 ≠ 0 →
      polarCurvatureNumerator (fun r => W (s.1, r))
        (fun y => H (s.1, y.1)) y = 0 := by
    intro s y _
    exact Radial.polarCurvatureNumerator_radialHeightField (hHW s.1)
      ((hW.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y.1)
  have hf := contDiffAt_parameter_normalizedHeightResidual (p := (p, q)) (x := x) hW' hZ' hV'
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : P × ℝ → ℝ))
      (Filter.Eventually.of_forall hzero) hr hD
  exact hf.comp (p, q, x)
    ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)

end ContinuousFlexibility

/-!
# Integral formula for the removable scalar residual

The fundamental theorem of calculus is applied along the actual affine
height family.  The zero-parameter case uses its genuine derivative; no
division by the construction parameter is made at zero.
-/



namespace ContinuousFlexibility

open Set MeasureTheory
open scoped ContDiff Topology

/-- The affine height derivative at any parameter, obtained by translating
the already established derivative at parameter zero. -/
theorem hasDerivAt_radialScaledResidual_divergence_parameter
    {w : ℝ → ℝ} {z u : PolarPoint → ℝ} {x : PolarPoint} {q : ℝ}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hu : ContDiff ℝ ∞ u)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w (heightFamily z u q) x) :
    HasDerivAt (fun t => x.1 * polarCoordinateResidual w (heightFamily z u t) x)
      (heightLinearizedDivergence w (heightFamily z u q) u x) q := by
  have hd := hasDerivAt_radialScaledResidual_divergence hw
    (contDiff_heightFamily hz hu q) hu hr hD
  have hs : HasDerivAt (fun t : ℝ => t - q) 1 q :=
    (hasDerivAt_id q).sub_const q
  have hd' : HasDerivAt
      (fun t => x.1 * polarCoordinateResidual w (heightFamily (heightFamily z u q) u t) x)
      (heightLinearizedDivergence w (heightFamily z u q) u x) (q - q) := by
    simpa using hd
  have ht := hd'.comp q hs
  have heq (t : ℝ) : heightFamily (heightFamily z u q) u (t - q) =
      heightFamily z u t := by
    funext y
    unfold heightFamily
    ring
  simpa only [Function.comp_def, heq, mul_one] using ht

theorem contDiffAt_radialScaledResidual_parameter
    {w : ℝ → ℝ} {z u : PolarPoint → ℝ} {x : PolarPoint} {q : ℝ}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hu : ContDiff ℝ ∞ u)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w (heightFamily z u q) x) :
    ContDiffAt ℝ ∞
      (fun t => x.1 * polarCoordinateResidual w (heightFamily z u t) x) q := by
  have hW : ContDiff ℝ ∞ (fun s : ℝ × ℝ => w s.2) := hw.comp contDiff_snd
  have hZ : ContDiff ℝ ∞ (fun s : ℝ × PolarPoint => heightFamily z u s.1 s.2) :=
    (hz.comp contDiff_snd).add (contDiff_fst.mul (hu.comp contDiff_snd))
  exact contDiffAt_const.mul
    ((contDiffAt_parameter_polarCoordinateResidual (p := q) (x := x) hW.contDiffAt hZ.contDiffAt hr hD).comp q
      (contDiffAt_id.prodMk contDiffAt_const))

/-- Exact FTC representation of the actual removable residual.  Positivity
is required on the whole segment, exactly as in the manuscript's formula. -/
theorem normalizedHeightResidual_eq_integral_linearization
    {w : ℝ → ℝ} {z u : PolarPoint → ℝ} {x : PolarPoint} {q : ℝ}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hu : ContDiff ℝ ∞ u)
    (hr : x.1 ≠ 0) (hzero : polarCurvatureNumerator w z x = 0)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1,
      0 < polarDiscriminant w (heightFamily z u (t * q)) x) :
    normalizedHeightResidual w z u q x =
      ∫ t in (0 : ℝ)..1,
        heightLinearizedDivergence w (heightFamily z u (t * q)) u x := by
  by_cases hq : q = 0
  · subst q
    have hbase : 0 < polarDiscriminant w z x := by
      simpa using hD 0 (by constructor <;> norm_num)
    simp only [mul_zero, heightFamily_zero, normalizedHeightResidual_zero,
      intervalIntegral.integral_const, sub_zero, one_smul]
    exact (heightLinearizedDivergence_eq_variation hw hz hu hr hbase).symm
  · let F : ℝ → ℝ := fun t => x.1 * polarCoordinateResidual w (heightFamily z u t) x
    let L : ℝ → ℝ := fun t => heightLinearizedDivergence w (heightFamily z u (t * q)) u x
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt F (L t) (t * q) := by
      intro t ht
      exact hasDerivAt_radialScaledResidual_divergence_parameter hw hz hu hr
        (hD t (by simpa [uIcc_of_le zero_le_one] using ht))
    have hc : ContinuousOn (fun t => deriv F (t * q)) (uIcc (0 : ℝ) 1) := by
      intro t ht
      have hs := contDiffAt_radialScaledResidual_parameter hw hz hu hr
        (hD t (by simpa [uIcc_of_le zero_le_one] using ht))
      exact (((hs.derivWithin (m := 0) (by simp)).continuousAt).comp
        (continuousAt_id.mul continuousAt_const)).continuousWithinAt
    have hL : ContinuousOn L (uIcc (0 : ℝ) 1) := by
      apply hc.congr
      intro t ht
      exact (hder t ht).deriv.symm
    have hpath : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s => F (s * q)) (L t * q) t := by
      intro t ht
      simpa using (hder t ht).comp t ((hasDerivAt_id t).mul_const q)
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hpath
      (hL.mul_const q).intervalIntegrable
    have hFzero : F 0 = 0 := by
      simp only [F, heightFamily_zero, polarCoordinateResidual, hzero, zero_mul, zero_div, mul_zero]
    simp only [one_mul, zero_mul, hFzero, sub_zero,
      intervalIntegral.integral_mul_const] at hi
    rw [normalizedHeightResidual_of_ne_zero w z u x hq]
    exact (div_eq_iff hq).mpr hi.symm

end ContinuousFlexibility

/-!
# The finite-annulus normalization and conservation statement

This assembles the scalar normalization, the genuine boundary connection
periods and parameter-dependent conservation.  The endpoint argument is
one lemma applied to each boundary, with no identification of the two
endpoint height values.
-/



namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem normalizedResidual_eq_integral_linearization
    {w h : ℝ → ℝ} {u : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h) (hu : ContDiff ℝ ∞ u)
    (hhw : ∀ r, HasDerivAt h (w r) r) {q : ℝ} {x : PolarPoint} (hr : 0 < x.1)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1,
      0 < polarDiscriminant w (heightFamily (Radial.radialHeightField h) u (t * q)) x) :
    normalizedResidual w h u q x =
      ∫ t in (0 : ℝ)..1,
        heightLinearizedDivergence w (heightFamily (Radial.radialHeightField h) u (t * q)) u x :=
  normalizedHeightResidual_eq_integral_linearization hw
    (Radial.contDiff_radialHeightField hh) hu hr.ne'
    (Radial.polarCurvatureNumerator_radialHeightField hhw
      (hw.differentiable (by simp) x.1)) hD

/-- Either flat boundary has connection period equal to its angular length. -/
theorem connectionPeriod_at_scalar_boundary
    {w h : ℝ → ℝ} {u : PolarPoint → ℝ} {r q T : ℝ}
    (hh : ContDiff ℝ ∞ h) (hu : ContDiff ℝ ∞ u)
    (hhw : ∀ r, HasDerivAt h (w r) r) (hw : w r = 0)
    (hk : ∀ θ, heightRadial u (r, θ) = 0)
    (hp : ∀ θ, heightAngular u (r, θ) = 0) :
    (∫ θ in (0 : ℝ)..T,
      (heightConnectionForm w (heightFamily (Radial.radialHeightField h) u q)).angular
        (r, θ)) = T := by
  have hd := (Radial.contDiff_radialHeightField hh).differentiable (by simp)
  have hud := hu.differentiable (by simp)
  have hangular : ∀ θ,
      (heightConnectionForm w (heightFamily (Radial.radialHeightField h) u q)).angular
        (r, θ) = 1 := by
    intro θ
    apply (heightConnection_of_boundary_jets hw ?_ ?_).2
    · rw [heightRadial_heightFamily hd hud, Radial.heightRadial_radialHeightField hhw]
      simp [heightFamily, Radial.radialHeightField, hw, hk θ]
    · rw [heightAngular_heightFamily hd hud, Radial.heightAngular_radialHeightField hhw]
      simp [heightFamily, hp θ]
  simp_rw [hangular]
  simp

/-- The actual admissibility hypotheses imply conservation, together with
the two separately computed connection periods. -/
theorem admissibleScalarData_conservation
    {a b q : ℝ} {w h : ℝ → ℝ} {u : PolarPoint → ℝ}
    (hadm : AdmissibleScalarData a b w h u q) :
    normalizedSourceIntegral w h u q a b = 0 ∧
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (heightConnectionForm w (heightFamily (Radial.radialHeightField h) u q)).angular
        (a, θ)) = 2 * Real.pi ∧
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (heightConnectionForm w (heightFamily (Radial.radialHeightField h) u q)).angular
        (b, θ)) = 2 * Real.pi := by
  rcases hadm with ⟨ha, hab, hw, hh, hu, hhw, hperiod, hwa, hwb, hjets, hD⟩
  have hr : ∀ r ∈ uIcc a b, r ≠ 0 := by
    intro r hrr
    rw [uIcc_of_le hab.le] at hrr
    exact (lt_of_lt_of_le ha hrr.1).ne'
  refine ⟨?_, ?_, ?_⟩
  · exact integral_mean_normalizedHeightResidual_radialHeight_eq_zero hh hhw
      (fun _ _ => hw.contDiffAt) hu hr
      (fun x hx => hD x.1 (by simpa [uIcc_of_le hab.le] using hx.1) x.2)
      hperiod hwa hwb
      (fun θ _ => (hjets θ).1) (fun θ _ => (hjets θ).2.1)
      (fun θ _ => (hjets θ).2.2.1) (fun θ _ => (hjets θ).2.2.2)
  · exact connectionPeriod_at_scalar_boundary hh hu hhw hwa
      (fun θ => (hjets θ).1) (fun θ => (hjets θ).2.1)
  · exact connectionPeriod_at_scalar_boundary hh hu hhw hwb
      (fun θ => (hjets θ).2.2.1) (fun θ => (hjets θ).2.2.2)

/-- In an admissible parameter family, smoothness is local in the parameter
set.  The primitive identity is needed only on that open set. -/
theorem contDiffAt_normalizedResidual_admissible_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {W H : P × ℝ → ℝ} {U : P × PolarPoint → ℝ} {q : P → ℝ}
    {O : Set P} {a b : ℝ} (hO : IsOpen O)
    (hW : ContDiff ℝ ∞ W) (hH : ContDiff ℝ ∞ H)
    (hU : ContDiff ℝ ∞ U) (hq : ContDiff ℝ ∞ q)
    (hadm : ∀ p ∈ O, AdmissibleScalarData a b
      (fun r => W (p, r)) (fun r => H (p, r)) (fun x => U (p, x)) (q p))
    {p : P} {x : PolarPoint} (hp : p ∈ O) (hx : x.1 ∈ Icc a b) :
    ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      normalizedResidual (fun r => W (s.1, r)) (fun r => H (s.1, r))
        (fun y => U (s.1, y)) (q s.1) s.2) (p, x) := by
  have hZ : ContDiff ℝ ∞ (fun s : P × PolarPoint => H (s.1, s.2.1)) :=
    hH.comp (contDiff_fst.prodMk contDiff_snd.fst)
  have hzero : ∀ᶠ p' in 𝓝 p, ∀ y : PolarPoint, y.1 ≠ 0 →
      polarCurvatureNumerator (fun r => W (p', r)) (fun z => H (p', z.1)) y = 0 := by
    filter_upwards [hO.mem_nhds hp] with p' hp'
    rcases hadm p' hp' with ⟨_, _, hw, _, _, hhw, _⟩
    intro y _
    exact Radial.polarCurvatureNumerator_radialHeightField hhw
      (hw.differentiable (by simp) y.1)
  rcases hadm p hp with ⟨ha, _, _, _, _, _, _, _, _, _, hD⟩
  exact contDiffAt_parameter_normalizedHeightResidual hW hZ hU hq hzero
    (lt_of_lt_of_le ha hx.1).ne' (hD x.1 hx x.2)

/-- Conservation on an open parameter set makes every actual parameter
derivative of the total source vanish, including the order-zero value. -/
theorem iteratedFDeriv_normalizedSourceIntegral_eq_zero
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {W H : P × ℝ → ℝ} {U : P × PolarPoint → ℝ} {q : P → ℝ}
    {O : Set P} {a b : ℝ} (hO : IsOpen O)
    (hadm : ∀ p ∈ O, AdmissibleScalarData a b
      (fun r => W (p, r)) (fun r => H (p, r)) (fun x => U (p, x)) (q p))
    {p : P} (hp : p ∈ O) (s : ℕ) :
    iteratedFDeriv ℝ s (fun p => normalizedSourceIntegral
      (fun r => W (p, r)) (fun r => H (p, r)) (fun x => U (p, x)) (q p) a b) p = 0 := by
  have heq : (fun p => normalizedSourceIntegral
      (fun r => W (p, r)) (fun r => H (p, r)) (fun x => U (p, x)) (q p) a b) =ᶠ[𝓝 p]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hO.mem_nhds hp] with p' hp'
    exact (admissibleScalarData_conservation (hadm p' hp')).1
  rw [(heq.iteratedFDeriv ℝ s).eq_of_nhds]
  simp only [iteratedFDeriv_fun_zero, Pi.zero_apply]

/-- The frozen S04 statement, with the parameter-derivative clause proved
by compact-rectangle differentiation of the actual scalar source. -/
theorem s04CalculusStatement : S04CalculusStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w h u hw hh hu hhw q x hr hD
    exact normalizedResidual_eq_integral_linearization hw hh hu hhw hr hD
  · intro w h u hw hh hu hhw x hr
    exact ⟨contDiffAt_normalizedHeightResidual_radialHeight_zero hh hhw hu hr.ne',
      Radial.normalizedHeightResidual_radialHeightField_zero hhw
        (hw.differentiable (by simp) x.1) hu hr.ne'⟩
  · intro a b q w h u hadm
    exact admissibleScalarData_conservation hadm
  · intro n W H U hW hH hU hHW p q x hr hD
    exact contDiffAt_parameter_normalizedResidual_radialHeight hW hH hU hHW hr.ne' hD
  · intro n W H U q O a b hO hW hH hU hq hadm p hp s
    have hz := iteratedFDeriv_normalizedSourceIntegral_eq_zero hO hadm hp s
    refine ⟨hz, ?_⟩
    intro directions
    have hf : ∀ p' ∈ O, ∀ x ∈ Icc a b ×ˢ Icc (0 : ℝ) (2 * Real.pi),
        ContDiffAt ℝ ∞ (fun z : (Fin n → ℝ) × PolarPoint =>
          normalizedResidual (fun r => W (z.1, r)) (fun r => H (z.1, r))
            (fun y => U (z.1, y)) (q z.1) z.2) (p', x) := by
      intro p' hp' x hx
      exact contDiffAt_normalizedResidual_admissible_family hO hW hH hU hq hadm hp' hx.1
    have hdiff := iteratedFDeriv_rectangleIntegral_parameter hO (hadm p hp).2.1.le
      ((mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).le) hf
      (1 / (2 * Real.pi)) s hp directions
    calc
      _ = (iteratedFDeriv ℝ s (fun p' => normalizedSourceIntegral
          (fun r => W (p', r)) (fun r => H (p', r)) (fun x => U (p', x))
            (q p') a b) p) directions := hdiff.symm
      _ = 0 := by simp only [hz, zero_apply]

end ContinuousFlexibility.Statements
