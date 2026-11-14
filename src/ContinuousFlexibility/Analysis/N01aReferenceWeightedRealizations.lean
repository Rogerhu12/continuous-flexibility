module

public import ContinuousFlexibility.Analysis.N01aReferenceNormalWeighted

/-!
# The reference eigenfunction and its actual first derivative at the spare exponent

Both weighted realizations follow from the one inverse at the pure row and
its frozen first-normal estimate.  They use the original physical cells,
the same coefficient weight, and zero free-left constants.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem exists_reference_eigenfield_weighted_realizations {D : ReferenceData}
    (hD : IsRadialReference D) :
    ∃ ε M : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      OutputRealization D (referenceBeta + ε) M 0
        ((fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2), 0) ∧
      OutputRealization D (referenceBeta + ε) M 0
        ((fun p : PolarPoint => deriv D.phi p.1 * Radial.cosineMode 2 p.2), 0) := by
  obtain ⟨Cprofile, hprofile⟩ := hD.1
  have hgeo : RadialProfileGeometry D := hprofile.1
  have hpart : RadialPartition D := hprofile.2.1
  have hkernel : RadialNaturalKernels D := hD.2.1
  have hborder : RadialTrueBorder D := hD.2.2.2.1
  obtain ⟨ε, M₀, M₁, hε, hεsmall, G, hG⟩ := hD.2.2.2.2
  have hplus := hG (referenceBeta + ε) (Or.inr (Or.inr rfl))
  have hγ : 0 < referenceBeta + ε := by unfold referenceBeta; linarith
  let F : RadialSource := ((0 : PolarPoint → ℝ), 1)
  have hF : SourceMember D (referenceBeta + ε) M₀ F :=
    sourceMember_pure_row D (referenceBeta + ε) M₀ 1
  have hgraph : ReferenceGraph D (referenceBeta + ε) M₀ M₁ (G F) F :=
    hplus.1.1 F hF
  have hcore : ReferenceSmoothCoreClosure D (referenceBeta + ε) M₀ M₁ :=
    hplus.2.2.1
  have hvalue : OutputRealization D (referenceBeta + ε) M₁ 0
      ((fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2), 0) :=
    referenceGraph_pure_row_eigenfield_output hgeo hpart hkernel hborder hγ hcore hgraph
  have hmode : referenceMode (G F).1 2 =ᵐ[volume.restrict (radialCore D)] D.phi := by
    simpa only [one_mul] using
      referenceGraph_pure_row_mode_eq hgeo hpart hkernel hborder hγ hcore hgraph
  obtain ⟨Cnormal, hCnormal, hnormal⟩ := hplus.2.2.2.2
  obtain ⟨ur, hur, hreal, _⟩ := hnormal F 0 hF (weakAngularDerivative_zero D)
    (n01a_sourceDerivativeMember_zero D (referenceBeta + ε) M₀)
  refine ⟨ε, M₁, hε, hεsmall, hvalue, ?_⟩
  exact weakNormalDerivative_reference_output hgeo.2.1.le hpart hgeo.2.2.2.1
    hur hmode hreal

end ContinuousFlexibility.Statements
