import ContinuousFlexibility.Analysis.N07aReferenceReturn
import ContinuousFlexibility.Radial.ReferenceCosineTests

/-!
# The genuine reference ν column

At zero amplitude the normalized residual is the radial Jacobi operator.
Varying only ν changes the reference profile to w exp(ν χ). Differentiating
that explicit operator at zero gives L'₂[w χ] φ, exactly the fixed border
column in the reference graph, with its physical cosine mode.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

theorem n07a_radialJacobi_exp_parameter_deriv
    {w χ u : ℝ → ℝ} {r : ℝ} (J : ℝ)
    (hw : DifferentiableAt ℝ w r) (hχ : DifferentiableAt ℝ χ r)
    (hdu : DifferentiableAt ℝ (deriv u) r) :
    HasDerivAt (fun ν => radialJacobi J (fun t => w t * Real.exp (ν * χ t)) u r)
      (radialJacobi J (fun t => w t * χ t) u r) 0 := by
  have hd (ν : ℝ) : HasDerivAt (fun t => w t * Real.exp (ν * χ t))
      (deriv w r * Real.exp (ν * χ r) +
        w r * (Real.exp (ν * χ r) * (ν * deriv χ r))) r :=
    hw.hasDerivAt.mul ((hχ.hasDerivAt.const_mul ν).exp)
  have hform (ν : ℝ) : radialJacobi J (fun t => w t * Real.exp (ν * χ t)) u r =
      Real.exp (ν * χ r) * (w r * deriv (deriv u) r +
        (deriv w r + ν * (w r * deriv χ r)) * (deriv u r - J / r * u r)) := by
    unfold radialJacobi
    rw [deriv_fun_mul (hd ν).differentiableAt hdu, (hd ν).deriv]
    ring
  have he := ((hasDerivAt_id (0 : ℝ)).mul_const (χ r)).exp
  have hlin := (((hasDerivAt_id (0 : ℝ)).mul_const (w r * deriv χ r)).const_add
    (deriv w r)).mul_const (deriv u r - J / r * u r)
  have hp := he.mul (hlin.const_add (w r * deriv (deriv u) r))
  convert hp using 1
  · funext ν
    exact hform ν
  · simp only [id_eq, zero_mul, Real.exp_zero, one_mul, add_zero]
    unfold radialJacobi
    have hwχ : DifferentiableAt ℝ (fun t => w t * χ t) r := hw.mul hχ
    rw [deriv_fun_mul hwχ hdu, deriv_fun_mul hw hχ]
    ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n07aReferenceNuState (C : NonlinearGeometryData S) (ν : ℝ) : AnnularState S :=
  (C.referenceState.1, (ν, C.referenceState.2.2))

theorem n07aReferenceNuState_profile (href : referenceStateConditions D S C) (ν : ℝ) :
    stateProfile D S C (n07aReferenceNuState C ν) =
      fun r => D.w r * Real.exp (ν * D.chi r) := by
  funext r
  simp only [stateProfile, n07aReferenceNuState, stateKappa, href.2.2.2.1,
    map_zero, Pi.zero_apply, angularMean, intervalIntegral.integral_zero,
    mul_zero, zero_mul, tsum_zero, add_zero]

theorem n07a_referenceNu_residual
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (ν : ℝ)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    scalarResidualField D S C (n07aReferenceNuState C ν, 0) p =
      radialJacobi 4 (fun r => D.w r * Real.exp (ν * D.chi r)) D.phi p.1 *
        cosineMode 2 p.2 := by
  have hgeom := h01.1.1.choose_spec.1
  have hφ : ContDiff ℝ ∞ D.phi := hgeom.2.2.2.1.1
  have hw := contDiff_stateProfile_of_n01 hS hT h01 (n07aReferenceNuState C ν)
  have hU : stateU S (n07aReferenceNuState C ν) =
      fun q => D.phi q.1 * cosineMode 2 q.2 := funext fun q => h01.2.2.1.1 q
  have hcos : ContDiff ℝ ∞ (cosineMode 2) := by
    unfold cosineMode
    fun_prop
  have hUs : ContDiff ℝ ∞ (fun q : PolarPoint => D.phi q.1 * cosineMode 2 q.2) :=
    (hφ.comp contDiff_fst).mul (hcos.comp contDiff_snd)
  unfold scalarResidualField
  rw [hU, normalizedHeightResidual_radialHeightField_zero
    (n07a_stateRadialHeight_hasDerivAt hS hT h01 (n07aReferenceNuState C ν))
    (hw.differentiable (by simp) p.1) hUs (hgeom.1.trans hp.1.1).ne']
  have he := radialPDE_cosine_lift (r := p.1) (θ := p.2) 2
    (Eventually.of_forall (hφ.differentiable (by simp)))
    ((hw.differentiable (by simp) p.1).mul
      ((contDiff_infty_iff_deriv.mp hφ).2.differentiable (by simp) p.1))
  rw [n07aReferenceNuState_profile h01.2.2.1 ν] at he ⊢
  simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 from by norm_num] using he

theorem n07a_nuColumnField_reference
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    nuColumnField D S C (C.referenceState, 0) p =
      referenceColumn D p.1 * cosineMode 2 p.2 := by
  have hgeom := h01.1.1.choose_spec.1
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hφ : ContDiff ℝ ∞ D.phi := hgeom.2.2.2.1.1
  have hχ : ContDiff ℝ ∞ D.chi := h01.1.2.2.2.1.1
  have he : (fun ν => scalarResidualField D S C (n07aReferenceNuState C ν, 0) p) =
      fun ν => radialJacobi 4 (fun r => D.w r * Real.exp (ν * D.chi r)) D.phi p.1 *
        cosineMode 2 p.2 := funext fun ν => n07a_referenceNu_residual hS hT h01 ν hp
  unfold nuColumnField
  rw [h01.2.2.1.2.2.1]
  change deriv (fun ν => scalarResidualField D S C (n07aReferenceNuState C ν, 0) p) 0 = _
  rw [he]
  exact ((n07a_radialJacobi_exp_parameter_deriv 4
    (hw.differentiable (by simp) p.1) (hχ.differentiable (by simp) p.1)
    ((contDiff_infty_iff_deriv.mp hφ).2.differentiable (by simp) p.1)).mul_const
      (cosineMode 2 p.2)).deriv

end ContinuousFlexibility.Analysis
