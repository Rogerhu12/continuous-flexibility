import ContinuousFlexibility.Radial.MatchedRetainedWeightedInverse
import ContinuousFlexibility.Radial.MatchedFixedCentralPoisson
import ContinuousFlexibility.Radial.MatchedInnerModelWeights
import ContinuousFlexibility.Radial.RetainedFixedCentralInverse
import ContinuousFlexibility.Radial.SelectedFirstInnerInverse
import ContinuousFlexibility.Blueprint.R10a.Geometry

/-!
# Actual weighted inner data of the retained family

The fixed central witness and the original localized Morse witnesses
form the existing retainedMorseActualChain. Its two signed weighted
bounds follow from the proved finite-chain theorem. The displayed cost
depends on the fixed model suppliers and the initial index, before the
frequency or the length of this finite chain is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Matrix.Norms.L2Operator

def matchedRetainedInnerWeightCost (N : ℕ) (T B₀ C₀ CM : ℝ) : ℝ :=
  1 + retainedMorseDirichletCoefficient (fixedCentralModelDirichletCost T B₀ C₀) CM *
      radialE N ^ (37 : ℝ) +
    2 * (max ((2 * retainedMorsePoissonCoefficient innerCentralPoissonConstant) ^ 2) 48 +
      24 * retainedMorseEndpointCoefficient (16 * C₀ * centralRadiusWeightConstant) CM)

theorem matchedRetainedInnerWeightCost_pos (N : ℕ) (T B₀ : ℝ)
    {C₀ CM : ℝ} (hC₀ : 0 ≤ C₀) (hCM : 0 ≤ CM) :
    0 < matchedRetainedInnerWeightCost N T B₀ C₀ CM := by
  have hD := fixedCentralModelDirichletCost_nonneg T B₀ hC₀
  have hM := innerMorseDirichletConstant_nonneg hCM
  have hR := centralRadiusWeightConstant_pos.le
  unfold matchedRetainedInnerWeightCost retainedMorseDirichletCoefficient
    retainedMorseEndpointCoefficient
  positivity

private theorem matchedRetainedWeight_temperature_pos {T : ℝ} (hT : 8 ≤ T) : 0 < T := by
  linarith only [hT]

private theorem matchedRetainedWeight_frequency_pos {q : ℕ} (hq : 1 ≤ q) :
    0 < 2 * (q : ℝ) := by
  exact mul_pos (by norm_num) (Nat.cast_pos.mpr hq)

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff}
  {headLength length Cstar T : ℝ} {requested : ℕ}
  (P : SeedRetainedPair S K headLength length)
  (metadata : R10aSelectedMetadata Cstar requested S)
  {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
  (hw : Γ.reference.w = P.pair.profile) (hhead : 0 < headLength) (hT : 8 ≤ T)
  (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
  (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
  (k : ℕ) (hk : 0 < k)

local notation "hD" => matchingProfileGeometry (And.left (And.right hΓ))
local notation "hTpos" => matchedRetainedWeight_temperature_pos hT
local notation "H" => P.retainedMorseInnerGeometry hD hw metadata.selected metadata.geometry
  metadata.first_two hhead hTpos hleft hright hTL hTR k hk
local notation "center" => innerModelChainPiece (innerMorseInnerCenter k)
local notation "hcenter" => P.retainedMorseInnerGeometry_center hD hw metadata.selected
  metadata.geometry metadata.first_two hhead hTpos hleft hright hTL hTR k hk

include P metadata hΓ hw hhead hT hleft hright hTL hTR k hk in
theorem retainedFamily_inner_central_core :
    Ioo (centralRadius (-T)) (centralRadius T) ⊆ radialCore Γ.reference := by
  intro r hr
  apply radialCore_mem_of_profile_pos hD
  apply (H).weight_pos center r
  change r ∈ Icc ((H).left center) ((H).right center)
  rw [(hcenter).1, (hcenter).2]
  exact Ioo_subset_Icc_self hr

/-- The actual matching cuts and the fixed border column belong to this
same finite geometry. No support condition is added to the family. -/
theorem retainedFamily_inner_matching_geometry
    (B : FixedCentralBorder) (hcap : sqrt centralOscillatorA + 2 ≤ T)
    (hcolumn : referenceColumn Γ.reference = fixedCentralColumn B.chi)
    (M : RadialMatchingData Γ.reference)
    (hML : M.innerLeft = P.sideRadius false * S.joinInner false (S.chain.index + k))
    (hMR : M.innerRight = P.sideRadius true * S.joinInner true (S.chain.index + k)) :
    M.innerLeft = (H).left 0 ∧
      M.innerRight = (H).right (Fin.last (2 * (2 * k + 1))) ∧
      Icc M.innerLeft M.innerRight ⊆ radialCore Γ.reference ∧
      innerL2PieceProjection (radialHilbertMeasure Γ.reference)
        (Ioo ((H).left center) ((H).right center))
        (matchingBorderVector Γ.reference hΓ.2.1 hΓ.2.2.1) =
          matchingBorderVector Γ.reference hΓ.2.1 hΓ.2.2.1 := by
  have hends := P.retainedMorseInnerGeometry_outer hD hw metadata.selected metadata.geometry
    metadata.first_two hhead hTpos hleft hright hTL hTR k hk metadata.later_join
  have hL : M.innerLeft = (H).left 0 := hML.trans hends.1.symm
  have hR : M.innerRight = (H).right (Fin.last (2 * (2 * k + 1))) := hMR.trans hends.2.symm
  have hLcore : (H).left 0 ∈ radialCore Γ.reference :=
    radialCore_mem_of_profile_pos hD
      ((H).weight_pos 0 _ (left_mem_Icc.mpr ((H).left_lt_right 0).le))
  have hRcore : (H).right (Fin.last (2 * (2 * k + 1))) ∈ radialCore Γ.reference :=
    radialCore_mem_of_profile_pos hD
      ((H).weight_pos _ _ (right_mem_Icc.mpr ((H).left_lt_right _).le))
  refine ⟨hL, hR, ?_, ?_⟩
  · intro r hr
    rw [hL, hR] at hr
    exact ⟨hLcore.1.trans_le hr.1, hr.2.trans_lt hRcore.2⟩
  · apply innerL2PieceProjection_eq_self _ _ isOpen_Ioo.measurableSet
    have hs : Function.support (referenceColumn Γ.reference) ⊆
        Ioo ((H).left center) ((H).right center) := by
      rw [(hcenter).1, (hcenter).2, hcolumn]
      exact B.column_support_in_model hcap
    filter_upwards [matchingBorderVector_coe hΓ.2.1 hΓ.2.2.1] with r hr
    intro hout
    rw [hr]
    have hz : referenceColumn Γ.reference r = 0 := by
      by_contra hne
      exact hout (hs hne)
    simp only [matchingBorderTest, hz, zero_div]

variable (hwindow : selectedFirstInnerModelWindow ≤ T)
  (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
  (B : FixedCentralBorder) (hcap : sqrt centralOscillatorA + 2 ≤ T)
  (hcolumn : referenceColumn Γ.reference = fixedCentralColumn B.chi)
  {B₀ C₀ K₀ CM KM : ℝ} (qf : ℕ) (hqf : 1 ≤ qf)
  (hB₀ : BufferHypotheses (B.modelBuffer qf T B₀))
  (M₀ : InnerBufferLocalizedData (B.modelBuffer qf T B₀) C₀ K₀)

local notation "hcore" => P.retainedFamily_inner_central_core metadata hΓ hw hhead hT
  hleft hright hTL hTR k hk
local notation "hweight" => retainedMorse_central_weight_identity hTL hTR hmodel
local notation "column" => matchingBorderVector Γ.reference
  (And.left (And.right hΓ)) (And.left (And.right (And.right hΓ)))
local notation "centralModel" => fixedCentralPhysicalModelChart B Γ.reference
  (And.left (And.right hΓ)) (And.left (And.right (And.right hΓ)))
  H center qf hT hcap hcolumn hcore hweight (And.left hcenter) (And.right hcenter) hB₀ M₀
local notation "hwin" => (And.right (And.right selectedFirstInnerModelWindow_spec)) T hwindow
local notation "j" => (2 * (qf : ℝ))
local notation "jpos" => matchedRetainedWeight_frequency_pos hqf

/-- The existing strong suppliers determine the same actual retained
chain. Its common cost is fixed before qf and k. -/
theorem exists_retainedFamily_innerWeightData
    (hC₀ : 0 < C₀) (hCM : 0 < CM) (hN : 4096 ≤ S.chain.index)
    (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + k) (2 * qf))
    (henergy : ∀ i, 0 < fixedCentralModelCutEnergy M₀ i ∧
      (M₀.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M₀ i)
    (hrem₀ : ∀ i,
      (sqrt 12 * (centralRadiusWeightConstant * (1 + T)) + 1) *
        (innerBufferRemainderEnvelope (B.modelBuffer qf T B₀) C₀ K₀ i /
          sqrt (fixedCentralModelCutEnergy M₀ i)) ≤ 1 / j)
    (herror₀ : ∀ sign : Bool,
      ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa M₀) (fun _ => 1)
        (M₀.physicalFluxError 1
          (fun i => centralDensityRoot (bufferCut (B.modelBuffer qf T B₀) i))) sign‖ ≤
            (1 : ℝ) / 8)
    (hsupplier : ∀ m n jf : ℕ, S.chain.index ≤ m → m < n → 2 ≤ jf →
      radialFrequencyBand S.chain S.Cstar n jf →
      BufferHypotheses
        (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) jf
          (8 * (S.chain.d m : ℝ) ^ 9)) ∧
      ∃ model : InnerBufferLocalizedData
          (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) jf
            (8 * (S.chain.d m : ℝ) ^ 9)) CM KM,
        (∀ i, innerMorseModelNormalizedRemainder model i ≤ 1 / (jf : ℝ)) ∧
        InnerMorsePhysicalPoissonBound
          ((metadata.selected.2.2.2.1 S.sigma metadata.selected.2.2.1).1)
          S.chain.index 0 model ∧
        ∀ γ : ℝ, |γ| ≤ 1 → ∀ side : Bool, ∀ height : ℝ, 0 < height → ∀ sign : Bool,
          ‖innerTwoCutWeightedError
            (innerPhysicalCutKappa height (fun _ => 1)
              (fun i => (model.column i).inwardEnergy))
            (innerMorseCutWeight S.chain.index 0 γ side m)
            (model.physicalFluxError height (fun _ => 1)) sign‖ < (1 : ℝ) / 8) :
    ∃ hB : ∀ (side : Bool) (p : Fin k), BufferHypotheses
        (innerMorseBufferData
          (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
          (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
          j (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)),
    ∃ models : ∀ (side : Bool) (p : Fin k), InnerBufferLocalizedData
        (innerMorseBufferData
          (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
          (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
          j (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)) CM KM,
    let A := P.retainedMorseActualChain hD hw metadata.selected metadata.geometry
      metadata.first_two hhead hTpos hleft hright hTL hTR k hk
      metadata.initial_bridge_positive hmodel hwin (centralModelBordered qf) j jpos
      column hB models centralModel
    let W := fun (sign : Bool) x =>
      (innerMorseInnerWeight S.chain.index k 0 1 H
        A.matchedWeightLeft A.matchedWeightRight x) ^ (if sign then (1 : ℝ) else -1)
    let hW := fun sign => (innerMorseInnerWeight_measurable S.chain.index k 0 1 H
      A.matchedWeightLeft A.matchedWeightRight).pow_const (if sign then (1 : ℝ) else -1)
    let loss := innerMorseInnerLoss S.chain.index k H 37
    let hloss := innerMorseInnerLoss_measurable S.chain.index k H 37
    let hlossBound := innerMorseInnerLoss_le_one S.chain.index k H (by norm_num : (0 : ℝ) ≤ 37)
    ∃ CW : ℝ, ∃ hCW : ∀ sign x, |W sign x| ≤ CW,
    ∃ hmatrix : IsUnit A.fluxMatrix, ∀ sign : Bool,
      ‖innerSupportedWeightMultiplier (radialHilbertMeasure Γ.reference)
          (innerRadialChainRegion Γ.reference H) (innerRadialChainRegion_measurable Γ.reference H)
          (centralModelBordered qf) (fun x => loss x * W sign x) (hloss.mul (hW sign)) CW
          (innerWeight_mul_bound_one loss (W sign) hlossBound CW (hCW sign)) ∘L
        A.inverse (hD).2.2.1.1 hmatrix ∘L
        innerSupportedWeightMultiplier (radialHilbertMeasure Γ.reference)
          (innerRadialChainRegion Γ.reference H) (innerRadialChainRegion_measurable Γ.reference H)
          (centralModelBordered qf) (W (!sign)) (hW (!sign)) CW (hCW (!sign))‖ ≤
        matchedRetainedInnerWeightCost S.chain.index T B₀ C₀ CM := by
  classical
  have hdata (side : Bool) (p : Fin k) :
      BufferHypotheses
        (innerMorseBufferData
          (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
          (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
          j (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)) ∧
      ∃ model : InnerBufferLocalizedData
          (innerMorseBufferData
            (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
            (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
            j (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)) CM KM,
        (∀ i, innerMorseModelNormalizedRemainder model i ≤ 1 / j) ∧
        ∀ height : ℝ, 0 < height → ∀ sign : Bool,
          ‖innerTwoCutWeightedError
            (innerPhysicalCutKappa height (fun _ => 1)
              (fun i => (model.column i).inwardEnergy))
            (innerMorseCutWeight S.chain.index 0 1 side
              (innerMorseInnerTailIndex S.chain.index k side p))
            (model.physicalFluxError height (fun _ => 1)) sign‖ ≤ (1 : ℝ) / 8 := by
    have hi := innerMorseInnerTailIndex_bounds S.chain.index k side p
    have hs := hsupplier _ (S.chain.index + k) (2 * qf) hi.1 hi.2 (by omega) hband
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
    obtain ⟨hB, model, hrem, _, herror⟩ := hs
    exact ⟨hB, model, hrem, fun height hh sign =>
      (herror 1 (by norm_num) side height hh sign).le⟩
  choose hB models hrem herror using hdata
  refine ⟨hB, models, ?_⟩
  have hkappa : (centralModel).kappa = fixedCentralModelPhysicalKappa M₀ := by
    funext i
    exact fixedCentralPhysicalModelChart_kappa B Γ.reference hΓ.2.1 hΓ.2.2.1 H center qf
      hT hcap hcolumn hcore hweight (hcenter).1 (hcenter).2 hB₀ M₀ i
  have hmatrix : (centralModel).errorMatrix = M₀.physicalFluxError 1
      (fun i => centralDensityRoot (bufferCut (B.modelBuffer qf T B₀) i)) :=
    fixedCentralPhysicalModelChart_errorMatrix B Γ.reference hΓ.2.1 hΓ.2.2.1 H center qf
      hT hcap hcolumn hcore hweight (hcenter).1 (hcenter).2 hB₀ M₀
  have hcentral : ∀ i, 0 < (centralModel).kappa i := by
    rw [hkappa]
    exact fixedCentralModelPhysicalKappa_pos M₀ (fun i => (henergy i).1)
  have hdir : ‖(centralModel).dirichlet‖ ≤ fixedCentralModelDirichletCost T B₀ C₀ :=
    fixedCentralPhysicalModelChart_dirichlet_bound B Γ.reference hΓ.2.1 hΓ.2.2.1 H center qf
      hT hcap hcolumn hcore hweight (hcenter).1 (hcenter).2 hB₀ M₀ hqf hC₀.le
  have hcols (i : Fin 2) :
      ‖(sqrt ((centralModel).kappa i))⁻¹ • (centralModel).column i‖ ≤
        innerCentralPoissonConstant / j := by
    have hb := matchedFixedCentralModelChart_weighted_column_bound B Γ.reference
      hΓ.2.1 hΓ.2.2.1 H center qf hT hcap hcolumn hcore hweight (hcenter).1 (hcenter).2
      hB₀ M₀ hqf henergy hrem₀ (fun _ => 1) measurable_const 1 (fun _ => by norm_num)
      (fun _ _ => rfl) i
    rw [(centralModel).matchedColumn_weight_one (fun _ => 1) measurable_const 1
      (fun _ => by norm_num) (fun _ _ => rfl) i] at hb
    exact hb
  have hendpoints : ∀ i,
      Γ.reference.w (if i = 0 then (H).left center else (H).right center) /
        (if i = 0 then (H).left center else (H).right center) ≤
          (16 * C₀ * centralRadiusWeightConstant) * (centralModel).kappa i :=
    fixedCentralPhysicalModelChart_endpoint_weight_bound B Γ.reference hΓ.2.1 hΓ.2.2.1
      H center qf hT hcap hcolumn hcore hweight (hcenter).1 (hcenter).2 hB₀ M₀ hqf hC₀ henergy
  have herr : ∀ sign : Bool,
      ‖innerTwoCutWeightedError (centralModel).kappa (fun _ => 1)
        (centralModel).errorMatrix sign‖ ≤ (1 : ℝ) / 8 := by
    rw [hkappa, hmatrix]
    exact herror₀
  have hj : 1 ≤ j := by
    have hqreal : (1 : ℝ) ≤ qf := by exact_mod_cast hqf
    linarith only [hqreal]
  obtain ⟨CW, hCW, hS, hbound⟩ := P.retainedMorseActualChain_signed_inverse_bound
    hD hw metadata.selected metadata.geometry metadata.first_two hhead hTpos
    hleft hright hTL hTR k hk metadata.initial_bridge_positive hmodel hwin
    (centralModelBordered qf) j hj column hB models centralModel hCM
    (fixedCentralModelDirichletCost_nonneg T B₀ hC₀.le) innerCentralPoissonConstant_pos.le
    (mul_nonneg (mul_nonneg (by norm_num) hC₀.le) centralRadiusWeightConstant_pos.le)
    hN hcentral hdir hcols hendpoints herr hrem herror
  refine ⟨CW, hCW, hS, fun sign => (hbound sign).trans ?_⟩
  have hp : 0 ≤ retainedMorsePoissonCoefficient innerCentralPoissonConstant :=
    add_nonneg innerMorsePoissonConstant_pos.le innerCentralPoissonConstant_pos.le
  have hdiv : 2 * retainedMorsePoissonCoefficient innerCentralPoissonConstant / j ≤
      2 * retainedMorsePoissonCoefficient innerCentralPoissonConstant := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hj)).mpr
    nlinarith only [hp, hj]
  have hsquare := (sq_le_sq₀ (by positivity :
      0 ≤ 2 * retainedMorsePoissonCoefficient innerCentralPoissonConstant / j)
      (by positivity : 0 ≤ 2 * retainedMorsePoissonCoefficient innerCentralPoissonConstant)).mpr hdiv
  have hmax := max_le_max hsquare (le_refl (48 : ℝ))
  unfold matchedRetainedInnerWeightCost
  linarith only [hmax]

end SeedRetainedPair

end ContinuousFlexibility.Radial
