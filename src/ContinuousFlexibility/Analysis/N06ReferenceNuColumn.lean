module

public import ContinuousFlexibility.Analysis.N06ReferencePhysicalCoefficients
public import ContinuousFlexibility.Radial.ReferenceCosineTests

/-!
# The actual nu column at the reference state

At construction parameter zero the normalized scalar residual is the radial
Jacobi PDE. Varying the actual logarithmic profile by nu chi differentiates
it to w chi. Consequently the frozen nu column is exactly the reference
border, with its original cosine normalization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n06_radialJacobi_logProfile_hasDerivAt
    {w χ u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hu : ContDiff ℝ ∞ u) (a r : ℝ) :
    HasDerivAt (fun ν : ℝ => radialJacobi a (fun t => w t * Real.exp (ν * χ t)) u r)
      (radialJacobi a (fun t => w t * χ t) u r) 0 := by
  let E : ℝ → ℝ := fun ν => Real.exp (ν * χ r)
  let W : ℝ → ℝ := fun ν => w r * E ν
  let Wr : ℝ → ℝ := fun ν => deriv w r * E ν + w r * E ν * (ν * deriv χ r)
  have he : HasDerivAt E (χ r) 0 := by
    simpa only [E, id_eq, zero_mul, Real.exp_zero, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (χ r)).exp
  have he0 : E 0 = 1 := by simp only [E, zero_mul, Real.exp_zero]
  have hv : HasDerivAt W (w r * χ r) 0 := he.const_mul (w r)
  have hrv : HasDerivAt Wr (deriv w r * χ r + w r * deriv χ r) 0 := by
    have h := (he.const_mul (deriv w r)).fun_add
      ((he.const_mul (w r)).fun_mul ((hasDerivAt_id (0 : ℝ)).mul_const (deriv χ r)))
    simpa only [Wr, Pi.add_apply, Pi.mul_apply, id_eq, he0, zero_mul, mul_zero,
      one_mul, mul_one, zero_add, add_zero] using h
  have hu' := (contDiff_infty_iff_deriv.mp hu).2
  have hformula (ν : ℝ) :
      radialJacobi a (fun t => w t * Real.exp (ν * χ t)) u r =
        Wr ν * deriv u r + W ν * deriv (deriv u) r - a * Wr ν / r * u r := by
    have hwν : ContDiff ℝ ∞ (fun t => w t * Real.exp (ν * χ t)) :=
      hw.mul (contDiff_const.mul hχ).exp
    have hwr : deriv (fun t => w t * Real.exp (ν * χ t)) r = Wr ν := by
      have h := ((hw.differentiable (by simp) r).hasDerivAt.fun_mul
        (((hχ.differentiable (by simp) r).hasDerivAt.const_mul ν).exp)).deriv
      simpa only [Wr, E, mul_assoc] using h
    have hflux := ((hwν.differentiable (by simp) r).hasDerivAt.fun_mul
      (hu'.differentiable (by simp) r).hasDerivAt).deriv
    rw [radialJacobi, hflux, hwr]
  have hactual : HasDerivAt
      (fun ν => Wr ν * deriv u r + W ν * deriv (deriv u) r - a * Wr ν / r * u r)
      ((deriv w r * χ r + w r * deriv χ r) * deriv u r +
        (w r * χ r) * deriv (deriv u) r -
          a * (deriv w r * χ r + w r * deriv χ r) / r * u r) 0 :=
    ((hrv.mul_const _).add (hv.mul_const _)).sub
      (((hrv.const_mul a).div_const r).mul_const (u r))
  have hprofile : deriv (fun t => w t * χ t) r =
      deriv w r * χ r + w r * deriv χ r :=
    ((hw.differentiable (by simp) r).hasDerivAt.fun_mul
      (hχ.differentiable (by simp) r).hasDerivAt).deriv
  have htarget : radialJacobi a (fun t => w t * χ t) u r =
      (deriv w r * χ r + w r * deriv χ r) * deriv u r +
        (w r * χ r) * deriv (deriv u) r -
          a * (deriv w r * χ r + w r * deriv χ r) / r * u r := by
    have hflux := (((hw.mul hχ).differentiable (by simp) r).hasDerivAt.fun_mul
      (hu'.differentiable (by simp) r).hasDerivAt).deriv
    rw [radialJacobi, hflux, hprofile]
  rw [htarget]
  exact hactual.congr_of_eventuallyEq (Eventually.of_forall hformula)

theorem n06_stateProfile_reference_nu
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) (ν : ℝ) :
    stateProfile D S C (C.referenceState.1, (ν, C.referenceState.2.2)) =
      fun r => D.w r * Real.exp (ν * D.chi r) := by
  funext r
  simp only [stateProfile, stateKappa, href.2.2.2.1, map_zero, Pi.zero_apply,
    angularMean, intervalIntegral.integral_zero, mul_zero, zero_mul, tsum_zero, add_zero]

/-- The reference parameter derivative is the actual border column, not
an independently selected representative of it. -/
theorem n06_nuColumn_reference
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hw : ContDiff ℝ ∞ D.w) (hχ : ContDiff ℝ ∞ D.chi)
    (hφ : ContDiff ℝ ∞ D.phi) (href : referenceStateConditions D S C)
    {p : PolarPoint} (hr : p.1 ≠ 0) :
    nuColumnField D S C (C.referenceState, 0) p =
      referenceColumn D p.1 * cosineMode 2 p.2 := by
  have hU : ContDiff ℝ ∞ (stateU S C.referenceState) := by
    have heq : stateU S C.referenceState =
        fun x : PolarPoint => D.phi x.1 * cosineMode 2 x.2 := funext href.1
    rw [heq]
    have hcos : ContDiff ℝ ∞ (cosineMode 2) := by
      unfold cosineMode
      exact contDiff_const.mul (contDiff_const.mul contDiff_id).cos
    exact (hφ.comp contDiff_fst).mul (hcos.comp contDiff_snd)
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hformula (ν : ℝ) :
      scalarResidualField D S C ((C.referenceState.1, (ν, C.referenceState.2.2)), 0) p =
        radialJacobi 4 (fun r => D.w r * Real.exp (ν * D.chi r)) D.phi p.1 *
          cosineMode 2 p.2 := by
    let x : AnnularState S := (C.referenceState.1, (ν, C.referenceState.2.2))
    have hprofile : stateProfile D S C x =
        fun r => D.w r * Real.exp (ν * D.chi r) := n06_stateProfile_reference_nu href ν
    have hws : ContDiff ℝ ∞ (stateProfile D S C x) := by
      rw [hprofile]
      exact hw.mul (contDiff_const.mul hχ).exp
    have hu : stateU S x = stateU S C.referenceState := rfl
    have hnorm := normalizedHeightResidual_radialHeightField_zero
      (fun r => stateRadialHeight_hasDerivAt_of_contDiff hws r)
      (hws.differentiable (by simp) p.1) (hu ▸ hU) hr
    change scalarResidualField D S C (x, 0) p = _
    change normalizedHeightResidual (stateProfile D S C x)
      (radialHeightField (stateRadialHeight D S C x)) (stateU S x) 0 p = _
    rw [hu, hnorm, hprofile]
    have heq : (fun r θ => stateU S C.referenceState (r, θ)) =
        fun r θ => D.phi r * cosineMode 2 θ := by
      funext r θ
      exact href.1 (r, θ)
    rw [heq]
    have hc := radialPDE_cosine_lift (r := p.1) (θ := p.2)
      (w := fun r => D.w r * Real.exp (ν * D.chi r)) 2
      (Eventually.of_forall (hφ.differentiable (by simp)))
      (((hw.mul (contDiff_const.mul hχ).exp).mul hφ').differentiable (by simp) p.1)
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at hc
    exact hc
  have hderiv := (n06_radialJacobi_logProfile_hasDerivAt hw hχ hφ 4 p.1).mul_const
    (cosineMode 2 p.2)
  have hactual := hderiv.congr_of_eventuallyEq (Eventually.of_forall hformula)
  change deriv (fun ν => scalarResidualField D S C
    ((C.referenceState.1, (ν, C.referenceState.2.2)), 0) p) C.referenceState.2.1 = _
  rw [href.2.2.1]
  exact hactual.deriv

end ContinuousFlexibility.Analysis
