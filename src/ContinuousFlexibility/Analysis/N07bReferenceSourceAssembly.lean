module

public import ContinuousFlexibility.Analysis.N07bCanonicalSourceLinear
public import ContinuousFlexibility.Analysis.N07bTransportReferenceGraph

/-!
# The complete reference source from its bulk and compact corrections

Only the bulk forcing is supplied as an actual element of the prescribed
volume level. The cutoff flux and reference column are genuine physical
sources, so the same reference source encoder supplies their volume
representatives. Linearity and the actual radial PDE identity assemble the
complete forcing without assuming that it is globally smooth.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- A represented bulk term and the reference encoder for physical sources
give a representative of the full reference forcing in the same volume
level. No norm estimate or graph-membership premise is used here. -/
theorem n07b_exists_referenceSource_of_bulk
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {β : ℝ} {b : ℕ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hborder : RadialTrueBorder D)
    (hlift : ∀ f : S.Source, ∃ F : V.level β 0 b,
      ∀ m, (V.forget β 0 b F m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          canonicalSource S K (C.referenceState, 0) m
            ((S.height (3 / 4 : ℝ)).decode f.val))
    {R : PolarPoint → ℝ} (hR : ContDiff ℝ 2 R) (a μ : ℝ)
    (Fbulk : V.level β 0 b)
    (hbulk : ∀ m, (V.forget β 0 b Fbulk m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m
          (fun p : PolarPoint =>
            radialPDE D.w (fun r θ => R (r, θ)) p.1 p.2)) :
    ∃ Ffull : V.level β 0 b,
      ∀ m, (V.forget β 0 b Ffull m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          canonicalSource S K (C.referenceState, 0) m
            (n07bReferenceForcing D μ (fun p : PolarPoint => R p + a * S.chiLeft p.1)) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  obtain ⟨fcut, hfcut, _⟩ := n07b_exists_spacesCutoffFlux_source hgeom hT hS
  obtain ⟨fcol, hfcol, _⟩ := n07b_exists_referenceColumn_source hgeom hborder hT hS μ
  obtain ⟨Fcut, hFcut⟩ := hlift fcut
  obtain ⟨Fcol, hFcol⟩ := hlift fcol
  rw [hfcut] at hFcut
  rw [hfcol] at hFcol
  have hsum : ∀ m,
      (V.forget β 0 b ((Fbulk + a • Fcut) + Fcol) m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          canonicalSource S K (C.referenceState, 0) m
            (fun p : PolarPoint =>
              (radialPDE D.w (fun r θ => R (r, θ)) p.1 p.2 +
                a * deriv (fun r => D.w r * deriv S.chiLeft r) p.1) +
              μ * referenceColumn D p.1 * cosineMode 2 p.2) :=
    n07b_canonicalSourceLift_add_ae
      (n07b_canonicalSourceLift_add_ae hbulk
        (n07b_canonicalSourceLift_smul_ae hFcut a)) hFcol
  have hfield :
      (fun p : PolarPoint =>
        (radialPDE D.w (fun r θ => R (r, θ)) p.1 p.2 +
          a * deriv (fun r => D.w r * deriv S.chiLeft r) p.1) +
        μ * referenceColumn D p.1 * cosineMode 2 p.2) =
      n07bReferenceForcing D μ (fun p : PolarPoint => R p + a * S.chiLeft p.1) := by
    funext p
    change
      (radialPDE D.w (fun r θ => R (r, θ)) p.1 p.2 +
        a * deriv (fun r => D.w r * deriv S.chiLeft r) p.1) +
          μ * referenceColumn D p.1 * cosineMode 2 p.2 =
      radialPDE D.w (fun r θ => R (r, θ) + a * S.chiLeft r) p.1 p.2 +
        μ * referenceColumn D p.1 * cosineMode 2 p.2
    exact congrArg (fun v : ℝ => v + μ * referenceColumn D p.1 * cosineMode 2 p.2)
      (n07b_referencePDE_add_radial_cutoff hgeom hS.2.2.1.1 hR a p).symm
  refine ⟨(Fbulk + a • Fcut) + Fcol, ?_⟩
  rw [← hfield]
  exact hsum

end ContinuousFlexibility.Analysis
