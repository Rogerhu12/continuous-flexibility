module

public import ContinuousFlexibility.Analysis.NeighborhoodStateBounds
public import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
public import ContinuousFlexibility.Analysis.N06ReferenceRemainderFields
public import ContinuousFlexibility.Radial.ReferenceColumnSmooth

/-!
# The fixed physical support of the actual nu column

The radial primitive itself may change by a constant when the logarithmic
profile parameter changes. The actual normalized residual does not depend
on that primitive value: its factored expression uses only the value and
first derivative of the profile, and actual spatial derivatives of the
same height increment. Consequently the real nu derivative vanishes off
the fixed topological support of the border cutoff at every state and
construction parameter.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Changing the radial primitive by any amount is immaterial to the
normalized residual when the two actual profile jets agree at the point. -/
theorem n06_normalizedRadialResidual_eq_of_profile_jets
    {h₀ h₁ w₀ w₁ : ℝ → ℝ} {u : PolarPoint → ℝ} {p : PolarPoint}
    (hh₀ : ContDiff ℝ ∞ h₀) (hh₁ : ContDiff ℝ ∞ h₁)
    (hprim₀ : ∀ r, HasDerivAt h₀ (w₀ r) r)
    (hprim₁ : ∀ r, HasDerivAt h₁ (w₁ r) r)
    (hw₀ : DifferentiableAt ℝ w₀ p.1) (hw₁ : DifferentiableAt ℝ w₁ p.1)
    (hu : ContDiff ℝ ∞ u) (hr : p.1 ≠ 0)
    (hv : w₀ p.1 = w₁ p.1) (hd : deriv w₀ p.1 = deriv w₁ p.1) (q : ℝ) :
    normalizedHeightResidual w₀ (radialHeightField h₀) u q p =
      normalizedHeightResidual w₁ (radialHeightField h₁) u q p := by
  have hc₀ := contDiff_radialHeightField hh₀
  have hc₁ := contDiff_radialHeightField hh₁
  have hpde : radialPDE w₀ (fun r θ => u (r, θ)) p.1 p.2 =
      radialPDE w₁ (fun r θ => u (r, θ)) p.1 p.2 := by
    rw [radialPDE_eq_polar_jets hw₀ hu, radialPDE_eq_polar_jets hw₁ hu, hv, hd]
  have hquad : polarCurvatureNumeratorQuadratic w₀ u p =
      polarCurvatureNumeratorQuadratic w₁ u p := by
    simp only [polarCurvatureNumeratorQuadratic, polarCurvatureNumerator,
      radialPartial_profileEnergy hw₀, radialPartial_profileEnergy hw₁, profileEnergy, hv, hd]
  have hdisc : polarDiscriminant w₀ (heightFamily (radialHeightField h₀) u q) p =
      polarDiscriminant w₁ (heightFamily (radialHeightField h₁) u q) p := by
    unfold polarDiscriminant
    rw [heightRadial_heightFamily (hc₀.differentiable (by simp))
        (hu.differentiable (by simp)),
      heightRadial_heightFamily (hc₁.differentiable (by simp))
        (hu.differentiable (by simp)),
      heightAngular_heightFamily (hc₀.differentiable (by simp))
        (hu.differentiable (by simp)),
      heightAngular_heightFamily (hc₁.differentiable (by simp))
        (hu.differentiable (by simp)),
      heightRadial_radialHeightField hprim₀, heightRadial_radialHeightField hprim₁,
      heightAngular_radialHeightField hprim₀, heightAngular_radialHeightField hprim₁]
    simp only [heightFamily, radialHeightField, profileEnergy, hv]
  rw [normalizedHeightResidual_eq_factored w₀ hc₀ hu hr
      (polarCurvatureNumerator_radialHeightField hprim₀ hw₀) q,
    normalizedHeightResidual_eq_factored w₁ hc₁ hu hr
      (polarCurvatureNumerator_radialHeightField hprim₁ hw₁) q,
    polarCurvatureNumeratorVariation_radialHeightField hprim₀ hw₀ hu hr,
    polarCurvatureNumeratorVariation_radialHeightField hprim₁ hw₁ hu hr,
    hpde, hquad, hdisc]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- Off the border cutoff, changing only the real nu coordinate preserves
the actual profile germ. The control amplitudes and the height pair are
literally unchanged. -/
theorem n06_stateProfile_nu_germ_off_tsupport (x : AnnularState S)
    {r : ℝ} (hr : r ∉ tsupport D.chi) (ν : ℝ) :
    stateProfile D S C (x.1, (ν, x.2.2)) =ᶠ[𝓝 r] stateProfile D S C x := by
  have hχ : D.chi =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) :=
    notMem_tsupport_iff_eventuallyEq.mp hr
  filter_upwards [hχ] with s hs
  simp only [stateProfile, stateKappa, hs, mul_zero, zero_add]

/-- The original scalar residual is exactly constant in nu away from
the fixed physical support of the cutoff, including at parameter zero. -/
theorem n06_scalarResidual_nu_eq_off_tsupport
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint}
    (hp : p.1 ∉ tsupport D.chi) (ν : ℝ) :
    scalarResidualField D S C ((z.1.1, (ν, z.1.2.2)), z.2) p =
      scalarResidualField D S C z p := by
  by_cases hr : p.1 = 0
  · simp only [scalarResidualField, normalizedHeightResidual, hr, zero_mul, zero_div,
      ite_self]
  · have hws := contDiff_stateProfile_of_n01 hS hT hN01 z.1
    have hwν := contDiff_stateProfile_of_n01 hS hT hN01 (z.1.1, (ν, z.1.2.2))
    have hg := n06_stateProfile_nu_germ_off_tsupport (C := C) z.1 hp ν
    change normalizedHeightResidual (stateProfile D S C (z.1.1, (ν, z.1.2.2)))
        (radialHeightField (stateRadialHeight D S C (z.1.1, (ν, z.1.2.2))))
        (stateU S z.1) z.2 p =
      normalizedHeightResidual (stateProfile D S C z.1)
        (radialHeightField (stateRadialHeight D S C z.1)) (stateU S z.1) z.2 p
    exact n06_normalizedRadialResidual_eq_of_profile_jets
      (stateRadialHeight_contDiff_of_contDiff hwν)
      (stateRadialHeight_contDiff_of_contDiff hws)
      (stateRadialHeight_hasDerivAt_of_contDiff hwν)
      (stateRadialHeight_hasDerivAt_of_contDiff hws)
      (hwν.differentiable (by simp) p.1) (hws.differentiable (by simp) p.1)
      (neighborhood_stateU_contDiff hT hS z.1) hr hg.self_of_nhds hg.deriv_eq z.2

/-- This is the actual frozen nuColumnField, with its real derivative in
the nu coordinate; no separately chosen representative is used. -/
theorem n06_nuColumn_zero_off_tsupport
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hp : p.1 ∉ tsupport D.chi) :
    nuColumnField D S C z p = 0 := by
  have heq : (fun ν : ℝ => scalarResidualField D S C
      ((z.1.1, (ν, z.1.2.2)), z.2) p) =
      (fun _ : ℝ => scalarResidualField D S C z p) :=
    funext (n06_scalarResidual_nu_eq_off_tsupport hT hS hN01 z hp)
  change deriv (fun ν : ℝ => scalarResidualField D S C
    ((z.1.1, (ν, z.1.2.2)), z.2) p) z.1.2.1 = 0
  rw [heq]
  exact deriv_const _ _

/-- Every current column has one common actual compact radial support. -/
theorem n06_nuColumns_common_radialSupport
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) :
    IsCompact (tsupport D.chi) ∧ tsupport D.chi ⊆ radialCore D ∧
      ∀ (z : AnnularState S × ℝ) r, r ∉ tsupport D.chi →
        ∀ θ, nuColumnField D S C z (r, θ) = 0 := by
  have hb : RadialTrueBorder D := hN01.1.2.2.2.1
  refine ⟨hb.2.1, fun r hr => (hb.2.2.1 hr).1, ?_⟩
  intro z r hr θ
  exact n06_nuColumn_zero_off_tsupport hT hS hN01 z hr

/-- Subtracting the true reference nu field preserves the same fixed
physical compact support, before any canonical chart is applied. -/
theorem n06_nuDifference_zero_off_tsupport
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hp : p.1 ∉ tsupport D.chi) :
    nuColumnField D S C z p - n06ReferenceNuField D p = 0 := by
  have href : referenceColumn D p.1 = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hp (referenceColumn_tsupport_subset h)
  simp only [n06_nuColumn_zero_off_tsupport hT hS hN01 z hp,
    n06ReferenceNuField, href, zero_mul, sub_zero]

end ContinuousFlexibility.Statements
