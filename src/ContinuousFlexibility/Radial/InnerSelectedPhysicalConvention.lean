module

public import ContinuousFlexibility.Radial.InnerSelectedInverseStatement
public import ContinuousFlexibility.Radial.InnerRadialScalarSign

/-!
# The complete inner inverse in the manuscript sign convention

The single supported scalar reflection turns the positive Riesz column
of the local models into the manuscript column `-varpi⁻¹ g₀`, and turns
its row into the negative row. The same interface matrices and spatial
weights are retained. One inverse is chosen before every allowed gamma
and both signs; the physical output loss is still exactly thirty-seven.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

/-- The assertions of the inner inverse lemma for a fixed raw physical
geometry and the local families obtained from the ordered R09 choices.
The output loss is the fixed exponent thirty-seven. -/
def InnerSelectedPhysicalConventionStatement
    {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
    (P : InnerSelectedPhysicalGeometry S D X₀)
    {a CC KC CM KM η : ℝ}
    (hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η)
    (hMorseFamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
    (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀) (C : ℝ) : Prop :=
  ∀ (K q : ℕ) (hq : 1 ≤ q)
    (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q)),
    let A := P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
    let J := innerSupportedScalarSign (radialHilbertMeasure D)
      (innerRadialChainRegion D (P.chain K)) (decide (q = 1))
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
      G = innerRadialScalarSignInverse D (P.chain K) (decide (q = 1))
          (A.dirichlet P.geometry.2.2.1.1) +
        ((J : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) →L[ℝ]
          InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))) ∘L A.poisson P.geometry.2.2.1.1) ∘L
          Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ) A.fluxMatrix⁻¹ ∘L
            ((J : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) →L[ℝ]
          InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))) ∘L A.poisson P.geometry.2.2.1.1).adjoint ∧
      (∀ u F : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)),
        InnerRadialPhysicalWeakGraph D P.geometry.2.2.1.1.continuous
          (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
          (innerModelChainPiece (innerMorseInnerCenter K)) (-(P.centralColumn q hsupport)) u F ↔
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
          ‖innerWeightedPoisson W Ω ((J : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) →L[ℝ]
          InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))) ∘L A.poisson P.geometry.2.2.1.1)
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

/-- The normalized local-model convention implies the complete
manuscript convention with the identical constant. The inverse is
reflected once before any choice of gamma or of the weight sign. -/
theorem innerSelectedInverseStatement_physicalConvention
    {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
    (P : InnerSelectedPhysicalGeometry S D X₀)
    {a CC KC CM KM η : ℝ}
    (hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η)
    (hMorseFamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
    (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀) {C : ℝ}
    (h : InnerSelectedInverseStatement P hCentralFamily hMorseFamily hX hsupport C) :
    InnerSelectedPhysicalConventionStatement P hCentralFamily hMorseFamily hX hsupport C := by
  intro K q hq hband
  let A := P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
  let H := InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))
  let J := innerSupportedScalarSign (radialHilbertMeasure D)
    (innerRadialChainRegion D (P.chain K)) (decide (q = 1))
  let Jc : H →L[ℝ] H := J
  have hdata := h K q hq hband
  rcases hdata with
    ⟨G0, hunit, href, hpos, hdiag, hblocks, hcard, hschur, hgraph, _hself, hweights⟩
  let Gminus := innerRadialScalarSignInverse D (P.chain K) (decide (q = 1)) G0
  refine ⟨Gminus, hunit, href, hpos, hdiag, hblocks, hcard, ?_, ?_, ?_, ?_⟩
  · exact innerRadialScalarSignInverse_schur D (P.chain K) (decide (q = 1))
      G0 (A.dirichlet P.geometry.2.2.1.1) (A.poisson P.geometry.2.2.1.1)
      (Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ) A.fluxMatrix⁻¹) hschur
  · exact innerRadialScalarSignInverse_graph_iff D P.geometry.2.2.1.1.continuous
      (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
      (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport) G0 hgraph
  · exact innerRadialScalarSignInverse_selfAdjoint D P.geometry.2.2.1.1.continuous
      (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
      (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport) G0 hgraph
  · intro γ hγ
    let W := innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A
    let Ω := innerMorseInnerInterfaceEquiv S.chain.index K a γ
    have hw := hweights γ hγ
    rcases hw with ⟨hcommute, hsigns, hlocalized⟩
    have hWcomm (sign : Bool) :
        Jc ∘L (innerHilbertWeight W sign : H →L[ℝ] H) =
          (innerHilbertWeight W sign : H →L[ℝ] H) ∘L Jc := by
      dsimp only [W]
      simp only [innerMorseInnerSupportedWeightEquiv_signed_toCLM]
      exact innerSupportedScalarSign_commute_multiplier (radialHilbertMeasure D)
        (innerRadialChainRegion D (P.chain K)) (innerRadialChainRegion_measurable D (P.chain K))
        (decide (q = 1))
        (innerSignedWeight
          (innerMorseInnerWeight S.chain.index K a γ (P.chain K) A.leftWall A.rightWall) sign)
        (innerSignedWeight_measurable
          (innerMorseInnerWeight S.chain.index K a γ (P.chain K) A.leftWall A.rightWall)
          (innerMorseInnerWeight_measurable S.chain.index K a γ
            (P.chain K) A.leftWall A.rightWall) sign)
        (innerMorseInnerWeightBound S.chain.index K a γ (P.chain K) A)
        (innerMorseInnerSignedWeight_abs_le S.chain.index K a γ (P.chain K) A sign)
    refine ⟨hcommute, ?_, ?_⟩
    · intro sign
      have hsign := hsigns sign
      refine ⟨hsign.1, ?_, ?_⟩
      · have hnorm :
            ‖innerWeightedPoisson W Ω (Jc ∘L A.poisson P.geometry.2.2.1.1)
                (Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ)
                  (innerInterfaceInverseSqrt A.referenceMatrix)) sign‖ =
              ‖innerWeightedPoisson W Ω (A.poisson P.geometry.2.2.1.1)
                (Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ)
                  (innerInterfaceInverseSqrt A.referenceMatrix)) sign‖ := by
          simpa only [innerWeightedPoisson, ContinuousLinearMap.comp_assoc] using
            innerSupportedScalarSign_weighted_comp_norm (radialHilbertMeasure D)
              (innerRadialChainRegion D (P.chain K)) (decide (q = 1))
              (A.poisson P.geometry.2.2.1.1 ∘L
                (innerHilbertWeight Ω (!sign) :
                  EuclideanSpace ℝ (Fin (2 * (2 * K + 1))) →L[ℝ]
                    EuclideanSpace ℝ (Fin (2 * (2 * K + 1)))) ∘L
                Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ)
                  (innerInterfaceInverseSqrt A.referenceMatrix))
              (innerHilbertWeight W sign : H →L[ℝ] H) (hWcomm sign)
        exact hnorm.le.trans hsign.2.1
      · have hnorm :
            ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L Gminus ∘L
                (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ =
              ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L G0 ∘L
                (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ := by
          simpa only [Gminus, innerRadialScalarSignInverse] using
            innerSupportedScalarSign_weighted_conjugate_norm (radialHilbertMeasure D)
              (innerRadialChainRegion D (P.chain K)) (decide (q = 1)) G0
              (innerHilbertWeight W sign : H →L[ℝ] H)
              (innerHilbertWeight W (!sign) : H →L[ℝ] H) (hWcomm sign) (hWcomm (!sign))
        exact hnorm.le.trans hsign.2.2
    · let L := innerMorseInnerSupportedLocalizedWeight S.chain.index K a γ
        (P.chain K) A 37 (by norm_num : (0 : ℝ) ≤ 37)
      have hLcomm : Jc ∘L L = L ∘L Jc := by
        dsimp only [L, innerMorseInnerSupportedLocalizedWeight]
        exact innerSupportedScalarSign_commute_multiplier (radialHilbertMeasure D)
          (innerRadialChainRegion D (P.chain K))
          (innerRadialChainRegion_measurable D (P.chain K)) (decide (q = 1))
          (innerMorseInnerLocalizedWeight S.chain.index K a γ (P.chain K) A 37)
          (innerMorseInnerLocalizedWeight_measurable S.chain.index K a γ (P.chain K) A 37)
          (innerMorseInnerWeightBound S.chain.index K a γ (P.chain K) A)
          (innerMorseInnerLocalizedWeight_abs_le S.chain.index K a γ (P.chain K) A
            (by norm_num : (0 : ℝ) ≤ 37))
      have hWinv : Jc ∘L (W.symm : H →L[ℝ] H) = (W.symm : H →L[ℝ] H) ∘L Jc := by
        simpa only [innerHilbertWeight] using hWcomm false
      have hnorm :
          ‖L ∘L Gminus ∘L (W.symm : H →L[ℝ] H)‖ =
            ‖L ∘L G0 ∘L (W.symm : H →L[ℝ] H)‖ := by
        simpa only [Gminus, innerRadialScalarSignInverse] using
          innerSupportedScalarSign_weighted_conjugate_norm (radialHilbertMeasure D)
            (innerRadialChainRegion D (P.chain K)) (decide (q = 1))
            G0 L (W.symm : H →L[ℝ] H) hLcomm hWinv
      exact hnorm.le.trans hlocalized

end ContinuousFlexibility.Radial
