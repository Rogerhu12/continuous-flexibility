import ContinuousFlexibility.Analysis.N06PrincipalJetAlgebra
import ContinuousFlexibility.Analysis.N07aOpenDivergenceExpansion
import ContinuousFlexibility.Analysis.N07aRelativeCanonicalPairing
import ContinuousFlexibility.Analysis.N07aReferenceSecondNormal

/-!
# The original relative operator is the actual weak jet expression

This identifies the local L² representative of `P.relative` using its
already proved physical/canonical pairing. The same reference inverse
and its original weak jets occur in every term.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

variable {D : ReferenceData} {T : MaterialData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {V : VolumeModelData S K}
  {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B}

theorem n07a_relativeCanonical_expanded
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.left m < K.right m)
    (ur uθ urr urθ uθθ : CanonicalL2 S K m)
    (hr : N07aWeakCanonicalMixedDerivative S K m (n07aReferenceInverseField (B := B) F m) ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m (n07aReferenceInverseField (B := B) F m) uθ 0 1)
    (hrr : N07aWeakCanonicalMixedDerivative S K m ur urr 1 0)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1) :
    V.forget (3 / 4 : ℝ) 0 b (P.relative (liftSectorParameter S C z) F) m =
      n07aRelativePrincipalJet href hcur z hz m hm ur uθ urr urθ uθθ +
        n07aRelativeCanonicalLower href hcur z hz m hm (B.inverse F).val.1 := by
  let a := n07aCurrentOpenCoefficient href hcur z hz m hm 0
  let d := n07aCurrentOpenCoefficient href hcur z hz m hm 1
  let c := n07aCurrentOpenCoefficient href hcur z hz m hm 2
  let a₀ := n07aReferenceOpenCoefficient href m hm 0
  let d₀ := n07aReferenceOpenCoefficient href m hm 1
  let c₀ := n07aReferenceOpenCoefficient href m hm 2
  let U := n07aReferenceInverseField (B := B) F m
  apply n07aAngularWeak_unique m hm (k := 0)
    (f := V.forget (3 / 4 : ℝ) 0 b (P.relative (liftSectorParameter S C z) F) m)
  · intro W hW
    simp only [pow_zero, one_mul, spaces_mixedDerivative_zero]
  · intro W hW
    have h := n07a_relativeCanonical_pairing hab hS hT h01 h02 h03 h04 href hcur
      h05 h06 z hz F m hm hW
    have hi := (Lp.memLp U).integrable_mul (n07a_canonicalTest_memLp
      (n07a_canonicalTest_divergence _ a.smooth d.smooth c.smooth a.periodic d.periodic c.periodic hW))
    have hi₀ := (Lp.memLp U).integrable_mul (n07a_canonicalTest_memLp
      (n07a_canonicalTest_divergence _ a₀.smooth d₀.smooth c₀.smooth a₀.periodic d₀.periodic c₀.periodic hW))
    change Integrable (fun p => U p * divergenceOperator
      (K.coefficients (liftSectorParameter S C z) m) W p) (canonicalMeasure S K m) at hi
    change Integrable (fun p => U p * divergenceOperator
      (K.coefficients (C.referenceState, 0) m) W p) (canonicalMeasure S K m) at hi₀
    simp_rw [mul_sub] at h
    change (∫ p, V.forget (3 / 4 : ℝ) 0 b (P.relative (liftSectorParameter S C z) F) m p * W p
      ∂canonicalMeasure S K m) =
        (∫ p, U p * divergenceOperator (K.coefficients (liftSectorParameter S C z) m) W p -
          U p * divergenceOperator (K.coefficients (C.referenceState, 0) m) W p
            ∂canonicalMeasure S K m) + _ at h
    have hcurr : (∫ p, U p * divergenceOperator (K.coefficients (liftSectorParameter S C z) m) W p
        ∂canonicalMeasure S K m) =
        ∫ p, n07aOpenDivergence a d c ur uθ urr urθ uθθ p * W p ∂canonicalMeasure S K m :=
      n07aOpenDivergence_distribution a d c hr hθ hrr hrθ hθθ W hW
    have href₀ : (∫ p, U p * divergenceOperator (K.coefficients (C.referenceState, 0) m) W p
        ∂canonicalMeasure S K m) =
        ∫ p, n07aOpenDivergence a₀ d₀ c₀ ur uθ urr urθ uθθ p * W p ∂canonicalMeasure S K m :=
      n07aOpenDivergence_distribution a₀ d₀ c₀ hr hθ hrr hrθ hθθ W hW
    have hsplit := (integral_sub hi hi₀).trans (congrArg₂ (fun x y : ℝ => x - y) hcurr href₀)
    have hfinal := h.trans (congrArg (fun x : ℝ => x +
      ∫ p, n07aRelativeCanonicalLower href hcur z hz m hm (B.inverse F).val.1 p * W p
        ∂canonicalMeasure S K m) hsplit)
    simp only [pow_zero, one_mul, spaces_mixedDerivative_zero]
    exact (n07aOpenDivergence_sub_pairing a d c a₀ d₀ c₀ ur uθ urr urθ uθθ
      (n07aRelativeCanonicalLower href hcur z hz m hm (B.inverse F).val.1) hW).trans hfinal.symm

end ContinuousFlexibility.Analysis
