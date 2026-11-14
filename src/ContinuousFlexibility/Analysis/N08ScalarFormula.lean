module

public import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
public import ContinuousFlexibility.Scalar.WeightedResidualFormulas

/-!
# Finite spatial jets of the actual controlled scalar residual

The nonlinear state uses the primitive based at the right endpoint, whereas
the weighted scalar calculus uses the left endpoint. The actual normalized
residual depends only on the profile and the first two spatial jets of the
height increment. This identifies the two normalizations, including `q = 0`,
without adding a condition on the primitive's value.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_stateU_contDiff (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    ContDiff ℝ ∞ (stateU S x) :=
  physical_height_with_cutoff_contDiff hT hS (by norm_num) x.1.1 x.1.2

theorem n08_stateRadialHeight_hasDerivAt (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (r : ℝ) :
    HasDerivAt (stateRadialHeight D S C x) (stateProfile D S C x r) r := by
  have hw := (contDiff_stateProfile_of_n01 hS hT hN x).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable D.b r)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt

theorem n08_stateRadialHeight_contDiff (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) : ContDiff ℝ ∞ (stateRadialHeight D S C x) := by
  refine contDiff_infty_iff_deriv.mpr
    ⟨fun r => (n08_stateRadialHeight_hasDerivAt hT hS hN x r).differentiableAt, ?_⟩
  have hd : deriv (stateRadialHeight D S C x) = stateProfile D S C x :=
    funext fun r => (n08_stateRadialHeight_hasDerivAt hT hS hN x r).deriv
  rw [hd]
  exact contDiff_stateProfile_of_n01 hS hT hN x

/-- This is the actual removable scalar expression, with no division by q. -/
def n08ScalarFiniteFormula (w : ℝ → ℝ) (u : PolarPoint → ℝ)
    (q : ℝ) (p : PolarPoint) : ℝ :=
  let a := radialPartial u p
  let b := radialPartial (radialPartial u) p
  let c := heightAngular u p
  let d := radialPartial (heightAngular u) p
  let e := angularPartial (heightAngular u) p
  (deriv w p.1 * (a + e) + w p.1 * b +
    q * ((a + (1 + w p.1 ^ 2) * e) * b - (1 + w p.1 ^ 2) * p.1 * d ^ 2 +
      w p.1 * deriv w p.1 * (c ^ 2 - a * e))) *
    inverseDThreeHalves ((1 + w p.1 ^ 2) * (1 - (q * c) ^ 2) - (w p.1 + q * a) ^ 2)

theorem n08_polarDiscriminant_radialFamily {w h : ℝ → ℝ}
    {u : PolarPoint → ℝ} (hh : ContDiff ℝ ∞ h)
    (hhw : ∀ r, HasDerivAt h (w r) r) (hu : ContDiff ℝ ∞ u)
    (q : ℝ) (p : PolarPoint) :
    polarDiscriminant w (heightFamily (Radial.radialHeightField h) u q) p =
      (1 + w p.1 ^ 2) * (1 - (q * heightAngular u p) ^ 2) -
        (w p.1 + q * radialPartial u p) ^ 2 := by
  unfold polarDiscriminant
  rw [heightRadial_heightFamily
      ((Radial.contDiff_radialHeightField hh).differentiable (by simp))
      (hu.differentiable (by simp)),
    heightAngular_heightFamily
      ((Radial.contDiff_radialHeightField hh).differentiable (by simp))
      (hu.differentiable (by simp)),
    Radial.heightRadial_radialHeightField hhw,
    Radial.heightAngular_radialHeightField hhw]
  simp only [heightFamily, Radial.radialHeightField, heightDiscriminant, profileEnergy,
    radialEnergy, heightRadial, zero_add]

theorem n08_normalizedHeightResidual_eq_finiteFormula {w h : ℝ → ℝ}
    {u : PolarPoint → ℝ} (hh : ContDiff ℝ ∞ h) (hw : ContDiff ℝ ∞ w)
    (hhw : ∀ r, HasDerivAt h (w r) r) (hu : ContDiff ℝ ∞ u)
    (q : ℝ) {p : PolarPoint} (hr : p.1 ≠ 0) :
    normalizedHeightResidual w (Radial.radialHeightField h) u q p =
      n08ScalarFiniteFormula w u q p := by
  have hwd := hw.differentiable (by simp) p.1
  rw [normalizedHeightResidual_eq_factored w (Radial.contDiff_radialHeightField hh)
      hu hr (Radial.polarCurvatureNumerator_radialHeightField hhw hwd),
    Radial.polarCurvatureNumeratorVariation_radialHeightField hhw hwd hu hr,
    polarCurvatureNumeratorQuadratic_eq_jets u hwd,
    Radial.radialPDE_eq_polar_jets hwd hu,
    n08_polarDiscriminant_radialFamily hh hhw hu]
  unfold n08ScalarFiniteFormula
  rw [Radial.angularPartial_heightAngular_eq hu hr]
  ring

/-- Changing the radial primitive's additive constant leaves the actual
residual unchanged at every point and at every parameter, including zero. -/
theorem n08_normalizedHeightResidual_primitive_independent {w h₁ h₂ : ℝ → ℝ}
    {u : PolarPoint → ℝ} (hh₁ : ContDiff ℝ ∞ h₁) (hh₂ : ContDiff ℝ ∞ h₂)
    (hw : ContDiff ℝ ∞ w) (hhw₁ : ∀ r, HasDerivAt h₁ (w r) r)
    (hhw₂ : ∀ r, HasDerivAt h₂ (w r) r) (hu : ContDiff ℝ ∞ u)
    (q : ℝ) :
    normalizedHeightResidual w (Radial.radialHeightField h₁) u q =
      normalizedHeightResidual w (Radial.radialHeightField h₂) u q := by
  funext p
  by_cases hr : p.1 = 0
  · unfold normalizedHeightResidual
    split_ifs <;> simp only [hr, zero_mul, zero_div]
  · rw [n08_normalizedHeightResidual_eq_finiteFormula hh₁ hw hhw₁ hu q hr,
      n08_normalizedHeightResidual_eq_finiteFormula hh₂ hw hhw₂ hu q hr]

theorem n08_scalarResidualField_eq_finiteFormula (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hr : p.1 ≠ 0) :
    scalarResidualField D S C z p =
      n08ScalarFiniteFormula (stateProfile D S C z.1) (stateU S z.1) z.2 p :=
  n08_normalizedHeightResidual_eq_finiteFormula
    (n08_stateRadialHeight_contDiff hT hS hN z.1)
    (contDiff_stateProfile_of_n01 hS hT hN z.1)
    (n08_stateRadialHeight_hasDerivAt hT hS hN z.1)
    (n08_stateU_contDiff hT hS z.1) z.2 hr

end ContinuousFlexibility.Statements
