import ContinuousFlexibility.Radial.InnerSelectedPhysicalInverse
import ContinuousFlexibility.Radial.InnerMorseInnerSupportedWeights
import ContinuousFlexibility.Radial.InnerActualReferenceBlocks

/-!
# The complete inner inverse assertion on one selected physical geometry

The quantifiers place the constant before every band and mode, and the
inverse before every allowed weight exponent. All matrices, weights,
operators and weak equations are the actual ones constructed from the
same model-gap dictionary. The two inverse identities are expressed by
the exact graph equivalence, not by an abstract surrogate operator.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

/-- The assertions of the inner inverse lemma for a fixed raw physical
geometry and the local families obtained from the ordered R09 choices.
The output loss is the fixed exponent thirty-seven. -/
def InnerSelectedInverseStatement
    {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
    (P : InnerSelectedPhysicalGeometry S D X₀)
    {a CC KC CM KM η : ℝ}
    (hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η)
    (hMorseFamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
    (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀) (C : ℝ) : Prop :=
  ∀ (K q : ℕ) (hq : 1 ≤ q)
    (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q)),
    let A := P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
    ∃ G : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) →L[ℝ]
        InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)),
      IsUnit A.fluxMatrix ∧
      A.referenceMatrix = Matrix.diagonal A.kappa + A.gapMatrix ∧
      A.referenceMatrix.PosDef ∧ Matrix.diagonal A.kappa ≤ A.referenceMatrix ∧
      (∀ i k : Fin (2 * (2 * K + 1)),
        innerModelChainGapOfCut i ≠ innerModelChainGapOfCut k →
          A.referenceMatrix i k = 0) ∧
      (∀ g : Fin (2 * K + 2),
        (Finset.univ.filter (fun i : Fin (2 * (2 * K + 1)) =>
          innerModelChainGapOfCut i = g)).card ≤ 2) ∧
      G = A.dirichlet P.geometry.2.2.1.1 +
        A.poisson P.geometry.2.2.1.1 ∘L
          Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ) A.fluxMatrix⁻¹ ∘L
            (A.poisson P.geometry.2.2.1.1).adjoint ∧
      (∀ u F : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)),
        InnerRadialPhysicalWeakGraph D P.geometry.2.2.1.1.continuous
          (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
          (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport) u F ↔
            G F = u) ∧
      IsSelfAdjoint G ∧
      ∀ γ : ℝ, |γ| ≤ 1 →
        let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
        let Ω := innerMorseInnerInterfaceEquiv S.chain.index K a γ
        Commute (Matrix.diagonal (innerMorseInnerInterfaceWeight S.chain.index K a γ))
          A.referenceMatrix ∧
        (∀ sign : Bool,
          ‖innerInterfaceWeightedError A.referenceMatrix
              (innerInterfaceWeight
                (Matrix.diagonal (innerMorseInnerInterfaceWeight S.chain.index K a γ)) sign)
              A.errorMatrix‖ < 1 / 2 ∧
          ‖innerWeightedPoisson W Ω (A.poisson P.geometry.2.2.1.1)
              (Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ)
                (innerInterfaceInverseSqrt A.referenceMatrix)) sign‖ ≤ C / ((2 : ℝ) * q) ∧
          ‖(innerHilbertWeight W sign :
                InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) →L[ℝ]
                  InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))) ∘L G ∘L
              (innerHilbertWeight W (!sign) :
                InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) →L[ℝ]
                  InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)))‖ ≤
            radialE (S.chain.index + K) ^ C) ∧
        ‖innerMorseInnerSupportedLocalizedWeight S.chain.index K a γ (P.chain K) A 37
              (by norm_num : (0 : ℝ) ≤ 37) ∘L G ∘L
            (W.symm :
              InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) →L[ℝ]
                InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)))‖ ≤ C

end ContinuousFlexibility.Radial
