module

public import ContinuousFlexibility.Analysis.N07aReferencePhysicalEquation
public import ContinuousFlexibility.Analysis.N07aReferenceOpenCoefficients
public import ContinuousFlexibility.Analysis.N07aCanonicalEquationPairing

/-!
# The actual reference canonical equation on even tests

This is derived from the N05 physical graph, the zero reference return
residual and the actual ν derivative. The coefficients and three columns
are precisely the reference primitive functions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base loss : ℕ} {ε : ℝ} {m : ℕ}

theorem n07a_referenceCanonical_distribution_even
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    {γ M₀ M₁ l : ℝ} {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    (hrel : ReferenceCanonicalRelation D T S C K V γ M₀ M₁ l U F)
    (hm : K.left m < K.right m)
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W)
    (hWeven : ∀ r θ, W (r, -θ) = W (r, θ)) :
    (∫ p, U.1 m p * divergenceOperator (K.coefficients (C.referenceState, 0) m) W p
      ∂canonicalMeasure S K m) =
      ∫ p, n07aReferenceCanonicalRhs hJ m hm U F p * W p ∂canonicalMeasure S K m := by
  obtain ⟨_, η, f, hrep, hgraph⟩ := hrel
  obtain ⟨aL, hη⟩ := hgraph.1
  have hψp : Function.Periodic ((S.height (3 / 4 : ℝ)).decode S.psi) (0, Real.pi) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).2.2.1
  have hfp : Function.Periodic f (0, Real.pi) := by
    intro p
    have hg := hgraph.2.1.2.2.1 p
    change f (p + (0, Real.pi)) - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi
        (p + (0, Real.pi)) = f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p at hg
    rw [hψp p] at hg
    linarith only [hg]
  exact n07a_canonical_distribution_test_pairing hab h04
    (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector hS.2.2.1.1
    hrep hη.2.2.1 hfp
    (n07aReferenceOpenCoefficient hJ m hm 0)
    (n07aReferenceOpenCoefficient hJ m hm 1)
    (n07aReferenceOpenCoefficient hJ m hm 2)
    (N07aCanonicalOpenCoefficient.constMul (if K.positive m then -1 else (1 : ℝ))
      (n07aReferenceOpenCoefficient hJ m hm 4))
    (n07aReferenceScalarOpenCoefficient hJ m hm)
    rfl rfl rfl rfl (fun _ => rfl) hW
    (n07a_referenceGraph_pulledTest_equation hab hS hT h01 h02 h03 h04 hJ
      hrep hgraph hW hWeven)

end ContinuousFlexibility.Analysis
