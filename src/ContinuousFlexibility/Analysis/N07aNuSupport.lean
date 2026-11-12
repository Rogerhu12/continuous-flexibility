import ContinuousFlexibility.Analysis.NeighborhoodStateBounds
import ContinuousFlexibility.Analysis.StateProfileRegularity
import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
import ContinuousFlexibility.Scalar.WeightedResidualFormulas
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The actual distinguished column has fixed radial support

Outside the closed support of the border function, changing the distinguished
scalar preserves the local profile and its first derivative.  The genuine
normalized residual depends only on these profile jets, even though its
radial height primitive itself may change by a constant.  Thus its actual
parameter derivative vanishes there, uniformly in every other parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- The actual removable residual is independent of the additive constant
in the radial primitive and depends on only two profile jets. -/
theorem n07a_normalizedResidual_radialProfile_congr
    {h w h' w' : ℝ → ℝ} {η : PolarPoint → ℝ} {p : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hh' : ContDiff ℝ ∞ h')
    (hhw : ∀ r, HasDerivAt h (w r) r) (hhw' : ∀ r, HasDerivAt h' (w' r) r)
    (hw : DifferentiableAt ℝ w p.1) (hw' : DifferentiableAt ℝ w' p.1)
    (hη : ContDiff ℝ ∞ η) (hv : w p.1 = w' p.1)
    (hd : deriv w p.1 = deriv w' p.1) (q : ℝ) :
    normalizedHeightResidual w (Radial.radialHeightField h) η q p =
      normalizedHeightResidual w' (Radial.radialHeightField h') η q p := by
  by_cases hr : p.1 = 0
  · unfold normalizedHeightResidual
    split_ifs <;> simp only [hr, zero_mul, zero_div]
  have hz := Radial.contDiff_radialHeightField hh
  have hz' := Radial.contDiff_radialHeightField hh'
  have hdisc : polarDiscriminant w (heightFamily (Radial.radialHeightField h) η q) p =
      polarDiscriminant w' (heightFamily (Radial.radialHeightField h') η q) p := by
    unfold polarDiscriminant
    rw [heightRadial_heightFamily (hz.differentiable (by simp))
        (hη.differentiable (by simp)),
      heightAngular_heightFamily (hz.differentiable (by simp))
        (hη.differentiable (by simp)),
      heightRadial_heightFamily (hz'.differentiable (by simp))
        (hη.differentiable (by simp)),
      heightAngular_heightFamily (hz'.differentiable (by simp))
        (hη.differentiable (by simp)),
      Radial.heightRadial_radialHeightField hhw,
      Radial.heightAngular_radialHeightField hhw,
      Radial.heightRadial_radialHeightField hhw',
      Radial.heightAngular_radialHeightField hhw']
    simp only [heightFamily, Radial.radialHeightField, profileEnergy, hv]
  rw [normalizedHeightResidual_eq_factored w hz hη hr
      (Radial.polarCurvatureNumerator_radialHeightField hhw hw),
    normalizedHeightResidual_eq_factored w' hz' hη hr
      (Radial.polarCurvatureNumerator_radialHeightField hhw' hw'),
    Radial.polarCurvatureNumeratorVariation_radialHeightField hhw hw hη hr,
    Radial.polarCurvatureNumeratorVariation_radialHeightField hhw' hw' hη hr,
    polarCurvatureNumeratorQuadratic_eq_jets η hw,
    polarCurvatureNumeratorQuadratic_eq_jets η hw',
    Radial.radialPDE_eq_polar_jets hw hη,
    Radial.radialPDE_eq_polar_jets hw' hη, hdisc, hv, hd]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The profile germ is unchanged by the distinguished parameter off the
fixed closed support of the border function. -/
theorem n07a_stateProfile_nu_germ_outside
    (x : AnnularState S) (ν : ℝ) {r : ℝ} (hr : r ∉ tsupport D.chi) :
    stateProfile D S C (x.1, (ν, x.2.2)) =ᶠ[𝓝 r] stateProfile D S C x := by
  have hχ : D.chi =ᶠ[𝓝 r] 0 := notMem_tsupport_iff_eventuallyEq.mp hr
  filter_upwards [hχ] with t ht
  simp only [Pi.zero_apply] at ht
  simp only [stateProfile, stateKappa, ht, mul_zero, zero_add]

/-- This is an equality of the actual residual, for all values of ν; it
does not require differentiating a separately introduced model. -/
theorem n07a_scalarResidual_nu_eq_outside
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) (ν : ℝ) {p : PolarPoint}
    (hp : p.1 ∉ tsupport D.chi) :
    scalarResidualField D S C ((z.1.1, (ν, z.1.2.2)), z.2) p =
      scalarResidualField D S C z p := by
  have hw := contDiff_stateProfile_of_n01 hS hT h01 (z.1.1, (ν, z.1.2.2))
  have hw' := contDiff_stateProfile_of_n01 hS hT h01 z.1
  have he := n07a_stateProfile_nu_germ_outside (C := C) z.1 ν hp
  exact n07a_normalizedResidual_radialProfile_congr
    (stateRadialHeight_contDiff_of_contDiff hw)
    (stateRadialHeight_contDiff_of_contDiff hw')
    (stateRadialHeight_hasDerivAt_of_contDiff hw)
    (stateRadialHeight_hasDerivAt_of_contDiff hw')
    (hw.differentiable (by simp) p.1) (hw'.differentiable (by simp) p.1)
    (neighborhood_stateU_contDiff hT hS z.1) he.eq_of_nhds he.deriv_eq z.2

theorem n07a_nuColumnField_eq_zero_outside
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hp : p.1 ∉ tsupport D.chi) :
    nuColumnField D S C z p = 0 := by
  have he : (fun ν => scalarResidualField D S C ((z.1.1, (ν, z.1.2.2)), z.2) p) =
      fun _ => scalarResidualField D S C z p :=
    funext fun ν => n07a_scalarResidual_nu_eq_outside hS hT h01 z ν hp
  unfold nuColumnField
  rw [he, deriv_const]

theorem n07a_nuColumnField_support_subset
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ) :
    Function.support (nuColumnField D S C z) ⊆ {p | p.1 ∈ tsupport D.chi} := by
  intro p hp
  by_contra hnot
  exact hp (n07a_nuColumnField_eq_zero_outside hS hT h01 z hnot)

theorem n07a_nuColumnField_compactRadialSupport
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ) :
    HasCompactRadialSupport D (nuColumnField D S C z) := by
  have hb : RadialTrueBorder D := h01.1.2.2.2.1
  refine ⟨tsupport D.chi, hb.2.1, fun r hr => (hb.2.2.1 hr).1, ?_⟩
  intro r hr θ
  exact n07a_nuColumnField_eq_zero_outside hS hT h01 z hr

end ContinuousFlexibility.Analysis
