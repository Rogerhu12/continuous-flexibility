import ContinuousFlexibility.Analysis.N06ActualNuSupport
import ContinuousFlexibility.Scalar.WeightedResidualFormulas
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Finite spatial jets for the actual nu column

The border cutoff is supported in the positive-type region, whereas all
ordinary-flow controls are supported in the negative-type region. On the
entire support of the nu column the actual profile germ is therefore
`w exp (nu chi)`. This removes all control and angle-chart coordinates from
the physical nu formula. The only state inputs left are nu, the independent
construction parameter, and five actual first/second spatial height jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The factored scalar residual as an ordinary finite-dimensional function.
The five height coordinates are `u_r`, `u_rr`, `u_theta/r`, its radial
derivative, and its angular derivative. -/
def n06ResidualFiniteJetValue (r w w' a b c d e q : ℝ) : ℝ :=
  (w' * (a + e) + w * b +
    q * ((a + (1 + w ^ 2) * e) * b - (1 + w ^ 2) * r * d ^ 2 +
      w * w' * (c ^ 2 - a * e))) *
    inverseDThreeHalves ((1 + w ^ 2) * (1 - (q * c) ^ 2) - (w + q * a) ^ 2)

/-- This formula uses actual derivatives of the radial primitive and the
height increment. It holds also when the construction parameter is zero. -/
theorem n06_normalizedRadialResidual_eq_finiteJets
    {h w : ℝ → ℝ} {u : PolarPoint → ℝ} {p : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hprim : ∀ r, HasDerivAt h (w r) r)
    (hw : DifferentiableAt ℝ w p.1) (hu : ContDiff ℝ ∞ u)
    (hr : p.1 ≠ 0) (q : ℝ) :
    normalizedHeightResidual w (radialHeightField h) u q p =
      n06ResidualFiniteJetValue p.1 (w p.1) (deriv w p.1)
        (radialPartial u p) (radialPartial (radialPartial u) p)
        (heightAngular u p) (radialPartial (heightAngular u) p)
        (angularPartial (heightAngular u) p) q := by
  have hc := contDiff_radialHeightField hh
  have hdisc : polarDiscriminant w (heightFamily (radialHeightField h) u q) p =
      (1 + w p.1 ^ 2) * (1 - (q * heightAngular u p) ^ 2) -
        (w p.1 + q * radialPartial u p) ^ 2 := by
    unfold polarDiscriminant
    rw [heightRadial_heightFamily (hc.differentiable (by simp))
        (hu.differentiable (by simp)),
      heightAngular_heightFamily (hc.differentiable (by simp))
        (hu.differentiable (by simp)),
      heightRadial_radialHeightField hprim, heightAngular_radialHeightField hprim]
    simp only [heightFamily, radialHeightField, profileEnergy, radialEnergy,
      heightDiscriminant, heightRadial, zero_add]
  rw [normalizedHeightResidual_eq_factored w hc hu hr
      (polarCurvatureNumerator_radialHeightField hprim hw) q,
    polarCurvatureNumeratorVariation_radialHeightField hprim hw hu hr,
    radialPDE_eq_polar_jets hw hu, polarCurvatureNumeratorQuadratic_eq_jets u hw, hdisc]
  simp only [n06ResidualFiniteJetValue, angularPartial_heightAngular_eq hu hr]
  ring

/-- The true nu derivative of the finite residual. This is an ordinary real
derivative of an explicit function, not an independent coefficient field. -/
def n06NuFiniteJetValue (r w w' χ χ' a b c d e q ν : ℝ) : ℝ :=
  deriv (fun t : ℝ => n06ResidualFiniteJetValue r
    (w * Real.exp (t * χ)) ((w' + w * (t * χ')) * Real.exp (t * χ))
      a b c d e q) ν

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The entire family of controls vanishes in the open positive-type region.
This germ statement is simultaneous in all state coordinates. -/
theorem n06_stateProfile_germ_on_positive
    (hw : ContDiff ℝ ∞ D.w) (hC : controlGeometryConditions D S C)
    (x : AnnularState S) {r : ℝ} (hr : 0 < deriv D.w r) :
    stateProfile D S C x =ᶠ[𝓝 r] (fun s => D.w s * Real.exp (x.2.1 * D.chi s)) := by
  have hnear : ∀ᶠ s in 𝓝 r, 0 < deriv D.w s :=
    (isOpen_lt continuous_const (contDiff_infty_iff_deriv.mp hw).2.continuous).mem_nhds hr
  filter_upwards [hnear] with s hs
  have hzero (m : ℕ) : C.control m s = 0 := by
    by_contra hne
    have hmem : s ∈ Ioo (C.left m) (C.right m) := by
      first
      | exact (hC.2.2.2.2.2.1 m).2.2 hne
      | exact (hC.2.2.2.2.2.1 m).2.2 (subset_tsupport (C.control m) hne)
    have hneg := hC.2.2.2.1 m s hmem
    exact (not_lt_of_ge hs.le) hneg
  simp only [stateProfile, hzero, mul_zero, tsum_zero, add_zero]

theorem n06_stateProfile_jets_on_positive
    (hw : ContDiff ℝ ∞ D.w) (hχ : ContDiff ℝ ∞ D.chi)
    (hC : controlGeometryConditions D S C)
    (x : AnnularState S) {r : ℝ} (hr : 0 < deriv D.w r) :
    stateProfile D S C x r = D.w r * Real.exp (x.2.1 * D.chi r) ∧
      deriv (stateProfile D S C x) r =
        (deriv D.w r + D.w r * (x.2.1 * deriv D.chi r)) *
          Real.exp (x.2.1 * D.chi r) := by
  have hg := n06_stateProfile_germ_on_positive hw hC x hr
  refine ⟨hg.self_of_nhds, hg.deriv_eq.trans ?_⟩
  rw [((hw.differentiable (by simp) r).hasDerivAt.fun_mul
    (((hχ.differentiable (by simp) r).hasDerivAt.const_mul x.2.1).exp)).deriv]
  ring

/-- The frozen residual in its original AnnularState variables has the same
finite-jet expression as the ordinary radial-base residual. -/
theorem n06_scalarResidual_eq_finiteJets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hr : p.1 ≠ 0) :
    scalarResidualField D S C z p =
      n06ResidualFiniteJetValue p.1 (stateProfile D S C z.1 p.1)
        (deriv (stateProfile D S C z.1) p.1)
        (radialPartial (stateU S z.1) p)
        (radialPartial (radialPartial (stateU S z.1)) p)
        (heightAngular (stateU S z.1) p)
        (radialPartial (heightAngular (stateU S z.1)) p)
        (angularPartial (heightAngular (stateU S z.1)) p) z.2 := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 z.1
  exact n06_normalizedRadialResidual_eq_finiteJets
    (stateRadialHeight_contDiff_of_contDiff hw)
    (stateRadialHeight_hasDerivAt_of_contDiff hw)
    (hw.differentiable (by simp) p.1) (neighborhood_stateU_contDiff hT hS z.1) hr z.2

/-- On the support of the border, the scalar profile parameter has an exact
two-jet formula independent of every ordinary-flow control amplitude. -/
theorem n06_scalarResidual_nu_eq_finiteJets_on_positive
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint}
    (hr : p.1 ≠ 0) (hpos : 0 < deriv D.w p.1) (ν : ℝ) :
    scalarResidualField D S C ((z.1.1, (ν, z.1.2.2)), z.2) p =
      n06ResidualFiniteJetValue p.1 (D.w p.1 * Real.exp (ν * D.chi p.1))
        ((deriv D.w p.1 + D.w p.1 * (ν * deriv D.chi p.1)) *
          Real.exp (ν * D.chi p.1))
        (radialPartial (stateU S z.1) p)
        (radialPartial (radialPartial (stateU S z.1)) p)
        (heightAngular (stateU S z.1) p)
        (radialPartial (heightAngular (stateU S z.1)) p)
        (angularPartial (heightAngular (stateU S z.1)) p) z.2 := by
  have hj := n06_stateProfile_jets_on_positive
    hN01.1.1.choose_spec.1.2.2.1.1 hN01.1.2.2.2.1.1 hN01.2.2.2.1
    (z.1.1, (ν, z.1.2.2)) hpos
  have hformula := n06_scalarResidual_eq_finiteJets hT hS hN01
    ((z.1.1, (ν, z.1.2.2)), z.2) hr
  change scalarResidualField D S C ((z.1.1, (ν, z.1.2.2)), z.2) p =
    n06ResidualFiniteJetValue p.1
      (stateProfile D S C (z.1.1, (ν, z.1.2.2)) p.1)
      (deriv (stateProfile D S C (z.1.1, (ν, z.1.2.2))) p.1)
      (radialPartial (stateU S z.1) p)
      (radialPartial (radialPartial (stateU S z.1)) p)
      (heightAngular (stateU S z.1) p)
      (radialPartial (heightAngular (stateU S z.1)) p)
      (angularPartial (heightAngular (stateU S z.1)) p) z.2 at hformula
  exact hformula.trans (congrArg₂
    (fun w w' => n06ResidualFiniteJetValue p.1 w w'
      (radialPartial (stateU S z.1) p)
      (radialPartial (radialPartial (stateU S z.1)) p)
      (heightAngular (stateU S z.1) p)
      (radialPartial (heightAngular (stateU S z.1)) p)
      (angularPartial (heightAngular (stateU S z.1)) p) z.2) hj.1 hj.2)

/-- The actual nuColumnField everywhere in the physical annulus is an
explicit finite-dimensional function of nu, q, and the five real height
jets. All remaining state coordinates have disappeared from the formula. -/
theorem n06_nuColumn_eq_finiteJets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    nuColumnField D S C z p =
      n06NuFiniteJetValue p.1 (D.w p.1) (deriv D.w p.1)
        (D.chi p.1) (deriv D.chi p.1)
        (radialPartial (stateU S z.1) p)
        (radialPartial (radialPartial (stateU S z.1)) p)
        (heightAngular (stateU S z.1) p)
        (radialPartial (heightAngular (stateU S z.1)) p)
        (angularPartial (heightAngular (stateU S z.1)) p) z.2 z.1.2.1 := by
  by_cases hmem : p.1 ∈ tsupport D.chi
  · have hb : RadialTrueBorder D := hN01.1.2.2.2.1
    have hr : p.1 ≠ 0 := (hN01.1.1.choose_spec.1.1.trans hp.1.1).ne'
    have heq := funext
      (n06_scalarResidual_nu_eq_finiteJets_on_positive hT hS hN01 z hr
        (hb.2.2.1 hmem).2)
    unfold nuColumnField n06NuFiniteJetValue
    rw [heq]
  · have hχ := image_eq_zero_of_notMem_tsupport hmem
    have hχ' : deriv D.chi p.1 = 0 :=
      (HasDerivAt.of_notMem_tsupport hmem).deriv
    rw [n06_nuColumn_zero_off_tsupport hT hS hN01 z hmem]
    simp only [n06NuFiniteJetValue, hχ, hχ', mul_zero, Real.exp_zero,
      mul_one, add_zero, deriv_const]

end ContinuousFlexibility.Statements
