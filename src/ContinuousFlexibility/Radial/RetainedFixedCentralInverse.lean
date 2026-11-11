import ContinuousFlexibility.Radial.RetainedMorseChainInverse
import ContinuousFlexibility.Radial.FixedCentralPolynomialColumn
import ContinuousFlexibility.Radial.InnerPhysicalFrozenInverse
import ContinuousFlexibility.Radial.InnerLaterPolynomialBudget

/-!
# The same fixed central model in the retained finite-chain inverse

The constants are chosen before the retained geometry.  The central
piece uses the original fixed column and its actual Liouville density;
all Morse pieces and positive gaps belong to the same retained pair.
The final conversion to the frozen radial pair norm costs only sqrt 2.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

def fixedCentralLaterDirichletCoefficient (T B₀ C₀ CM : ℝ) : ℝ :=
  retainedMorseDirichletCoefficient (fixedCentralModelDirichletCost T B₀ C₀) CM

def fixedCentralLaterPoissonCoefficient (T B₀ C₀ K₀ : ℝ) : ℝ :=
  retainedMorsePoissonCoefficient (fixedCentralPolynomialColumnConstant T B₀ C₀ K₀)

def fixedCentralLaterEndpointCoefficient (C₀ CM : ℝ) : ℝ :=
  retainedMorseEndpointCoefficient (16 * C₀ * centralRadiusWeightConstant) CM

theorem fixedCentralModelDirichletCost_nonneg (T B₀ : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ fixedCentralModelDirichletCost T B₀ C := by
  unfold fixedCentralModelDirichletCost
  positivity

namespace SeedRetainedPair

theorem retainedMorse_central_weight_identity {Γ : ConnectedReferenceGeometry} {T : ℝ}
    (hTL : Γ.centralLeft < centralRadius (-T))
    (hTR : centralRadius T < Γ.centralRight)
    (hmodel : EqOn Γ.reference.w (centralRadialProfile 1)
      (Ioo Γ.centralLeft Γ.centralRight)) :
    ∀ x ∈ Icc (-T) T,
      Γ.reference.w (centralRadius x) =
        1 * centralDensityRoot x ^ 2 * deriv centralRadius x := by
  intro x hx
  have hr : centralRadius x ∈ Ioo Γ.centralLeft Γ.centralRight :=
    ⟨hTL.trans_le (strictMono_centralRadius.monotone hx.1),
      (strictMono_centralRadius.monotone hx.2).trans_lt hTR⟩
  rw [hmodel hr, centralRadialProfile_pullback]

/-- The fixed central localized inverse and the raw Morse witnesses
produce an actual physical inverse, with the same column and scalar.
No graph identity, global realization of the old chain, or uniform
positive lower bound on the first connecting slope is an input. -/
theorem exists_retainedFixedCentralInverse
    {S : SelectedTailData} {K : SeedCentralCutoff} {headLength length T B₀ C₀ K₀ CM KM : ℝ}
    (P : SeedRetainedPair S K headLength length) {Γ : ConnectedReferenceGeometry}
    (hD : RadialProfileGeometry Γ.reference) (hAcc : IsAccumulatingProfile Γ.reference)
    (hb : RadialTrueBorder Γ.reference) (hw : Γ.reference.w = P.pair.profile)
    (hS : IsSelectedTail S) (G₀ : MorseChainGeometryWitness S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hhead : 0 < headLength) (hT : 8 ≤ T)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
    (k : ℕ) (hk : 0 < k)
    (hbridge : ∀ side r, r ∈ uIcc (S.cut side S.chain.index)
      (S.entry side S.chain.index) → 0 < deriv (S.family S.sigma).w r)
    (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
    (hwindow : ∀ r, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
      (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r)
    (B : FixedCentralBorder) (qf : ℕ) (hqf : 1 ≤ qf)
    (hcap : sqrt centralOscillatorA + 2 ≤ T)
    (hcolumn : referenceColumn Γ.reference = fixedCentralColumn B.chi)
    (hB₀ : BufferHypotheses (B.modelBuffer qf T B₀))
    (M₀ : InnerBufferLocalizedData (B.modelBuffer qf T B₀) C₀ K₀)
    (hB : ∀ side p, BufferHypotheses
      (innerMorseBufferData
        (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
        (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
        (2 * (qf : ℝ))
        (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)))
    (models : ∀ side p, InnerBufferLocalizedData
      (innerMorseBufferData
        (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
        (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
        (2 * (qf : ℝ))
        (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)) CM KM)
    (hN : 4096 ≤ S.chain.index) (hC₀ : 0 < C₀) (hK₀ : 0 ≤ K₀) (hCM : 0 < CM)
    (henergy : ∀ i, 0 < fixedCentralModelCutEnergy M₀ i ∧
      (M₀.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M₀ i)
    (herror₀ : ∀ sign : Bool,
      ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa M₀) (fun _ => 1)
        (M₀.physicalFluxError 1
          (fun i => centralDensityRoot (bufferCut (B.modelBuffer qf T B₀) i))) sign‖ ≤
          (1 : ℝ) / 8)
    (hrem : ∀ side p i, innerMorseModelNormalizedRemainder (models side p) i ≤
      1 / (2 * (qf : ℝ)))
    (herror : ∀ side p height, 0 < height → ∀ sign : Bool,
      ‖innerTwoCutWeightedError
        (innerPhysicalCutKappa height (fun _ => 1)
          (fun i => ((models side p).column i).inwardEnergy))
        (innerMorseCutWeight S.chain.index 0 0 side
          (innerMorseInnerTailIndex S.chain.index k side p))
        ((models side p).physicalFluxError height (fun _ => 1)) sign‖ ≤ (1 : ℝ) / 8) :
    let H := P.retainedMorseInnerGeometry hD hw hS G₀ hfirst hhead
      ((by norm_num : (0 : ℝ) < 8).trans_le hT) hleft hright hTL hTR k hk
    ∃ inverse : InnerRadialPhysicalSource Γ.reference H (centralModelBordered qf) →L[ℝ]
        InnerRadialPhysicalSource Γ.reference H (centralModelBordered qf),
      (∀ u F, InnerRadialPhysicalWeakGraph Γ.reference hD.2.2.1.1.continuous H
        (centralModelBordered qf) (2 * (qf : ℝ))
        (innerModelChainPiece (innerMorseInnerCenter k))
        (matchingBorderVector Γ.reference hAcc hb) u F ↔ inverse F = u) ∧
      IsSelfAdjoint inverse ∧
      ‖InnerRadialPhysicalInverse.pairInverse inverse hAcc‖ ≤
        sqrt 2 * (fixedCentralLaterDirichletCoefficient T B₀ C₀ CM *
          radialE (S.chain.index + k) ^ (37 : ℝ) +
          8 * (fixedCentralLaterPoissonCoefficient T B₀ C₀ K₀) ^ 2 *
            (1 + 2 * (qf : ℝ)) ^ 4 +
          96 + 48 * fixedCentralLaterEndpointCoefficient C₀ CM) := by
  have hTpos : 0 < T := (by norm_num : (0 : ℝ) < 8).trans_le hT
  let H := P.retainedMorseInnerGeometry hD hw hS G₀ hfirst hhead hTpos
    hleft hright hTL hTR k hk
  let center := innerModelChainPiece (innerMorseInnerCenter k)
  have hends := P.retainedMorseInnerGeometry_center hD hw hS G₀ hfirst hhead hTpos
    hleft hright hTL hTR k hk
  have hcore : Ioo (centralRadius (-T)) (centralRadius T) ⊆ radialCore Γ.reference := by
    intro r hr
    apply radialCore_mem_of_profile_pos hD
    apply H.weight_pos center r
    change r ∈ Icc (H.left center) (H.right center)
    rw [hends.1, hends.2]
    exact Ioo_subset_Icc_self hr
  have hweight := retainedMorse_central_weight_identity hTL hTR hmodel
  let centralModel := fixedCentralPhysicalModelChart B Γ.reference hAcc hb H center qf
    hT hcap hcolumn hcore hweight hends.1 hends.2 hB₀ M₀
  have hkappa : centralModel.kappa = fixedCentralModelPhysicalKappa M₀ := by
    funext i
    exact fixedCentralPhysicalModelChart_kappa B Γ.reference hAcc hb H center qf
      hT hcap hcolumn hcore hweight hends.1 hends.2 hB₀ M₀ i
  have hmatrix : centralModel.errorMatrix =
      M₀.physicalFluxError 1
        (fun i => centralDensityRoot (bufferCut (B.modelBuffer qf T B₀) i)) :=
    fixedCentralPhysicalModelChart_errorMatrix B Γ.reference hAcc hb H center qf
      hT hcap hcolumn hcore hweight hends.1 hends.2 hB₀ M₀
  have hcentral : ∀ i, 0 < centralModel.kappa i := by
    rw [hkappa]
    exact fixedCentralModelPhysicalKappa_pos M₀ (fun i => (henergy i).1)
  have hdir : ‖centralModel.dirichlet‖ ≤ fixedCentralModelDirichletCost T B₀ C₀ :=
    fixedCentralPhysicalModelChart_dirichlet_bound B Γ.reference hAcc hb H center qf
      hT hcap hcolumn hcore hweight hends.1 hends.2 hB₀ M₀ hqf hC₀.le
  have hcols : ∀ i, ‖(sqrt (centralModel.kappa i))⁻¹ • centralModel.column i‖ ≤
      fixedCentralPolynomialColumnConstant T B₀ C₀ K₀ * (1 + 2 * (qf : ℝ)) ^ 2 :=
    fixedCentralPhysicalModelChart_polynomial_column_bound B Γ.reference hAcc hb H center qf
      hT hcap hcolumn hcore hweight hends.1 hends.2 hB₀ M₀ hqf hC₀ hK₀ henergy
  have hendpoints : ∀ i,
      Γ.reference.w (if i = 0 then H.left center else H.right center) /
        (if i = 0 then H.left center else H.right center) ≤
          (16 * C₀ * centralRadiusWeightConstant) * centralModel.kappa i :=
    fixedCentralPhysicalModelChart_endpoint_weight_bound B Γ.reference hAcc hb H center qf
      hT hcap hcolumn hcore hweight hends.1 hends.2 hB₀ M₀ hqf hC₀ henergy
  have herr : ∀ sign : Bool,
      ‖innerTwoCutWeightedError centralModel.kappa (fun _ => 1)
        centralModel.errorMatrix sign‖ ≤ (1 : ℝ) / 8 := by
    rw [hkappa, hmatrix]
    exact herror₀
  have hj : 1 ≤ 2 * (qf : ℝ) := by
    have hqreal : (1 : ℝ) ≤ qf := by exact_mod_cast hqf
    linarith only [hqreal]
  obtain ⟨inverse, hgraph, hnorm, hself⟩ :=
    P.exists_retainedMorseChainInverse hD hw hS G₀ hfirst hhead hTpos
      hleft hright hTL hTR k hk hbridge hmodel hwindow
      (centralModelBordered qf) (2 * (qf : ℝ)) hj
      (matchingBorderVector Γ.reference hAcc hb) hB models centralModel
      hCM (fixedCentralModelDirichletCost_nonneg T B₀ hC₀.le)
      (fixedCentralPolynomialColumnConstant_nonneg T B₀ C₀ K₀)
      (mul_nonneg (mul_nonneg (by norm_num) hC₀.le) centralRadiusWeightConstant_pos.le)
      hcentral hdir hcols hendpoints herr hrem herror
  refine ⟨inverse, hgraph, hself, ?_⟩
  exact InnerRadialPhysicalInverse.pairInverse_norm_le_of_bound inverse hAcc hnorm

end SeedRetainedPair

end ContinuousFlexibility.Radial
