import ContinuousFlexibility.Analysis.N03FixedRootTravelIdentification
import ContinuousFlexibility.Analysis.RootCircleSampleMaterialJets

/-!
# The actual two first-integral labels on a fixed left root section

The already proved whole-band travel and angular-average identities
identify each first integral with a signed sample of the very same
controlled root input. Thus its angular jets are restrictions of that
input; no radial fractional-power estimate is needed at the section.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n03_leftRoot_firstIntegrals_eq_controlled_samples
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hE : N02Properties D T S C E base ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R δ η : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (C.left m) 1 R)
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations
      (rootRescaledField (localizedRootDrift D S C (C.left m) 1 hR z)
        (localizedRootSpeed D S C g (C.left m) 1 hR z) δ) Θ)
    (hmatch : RootStoredFlowAgreementOn C L z m false δ η Θ)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) η)
    (hphysical : C.left m + δ * x ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m false) (Real.sqrt δ)
    canonicalGluedAiryIntegral S K z m 1 (C.left m + δ * x, θ) =
        rootCircleSample G x (-(x ^ (3 / 2 : ℝ))) θ ∧
      canonicalGluedAiryIntegral S K z m (-1) (C.left m + δ * x, θ) =
        rootCircleSample G x (x ^ (3 / 2 : ℝ)) θ := by
  let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m false) (Real.sqrt δ)
  let V := canonicalGluedAiryIntegral S K z m 1 (C.left m + δ * x, θ)
  let U := canonicalGluedAiryIntegral S K z m (-1) (C.left m + δ * x, θ)
  have hphysical' : n01ComponentRoot C m false +
      n01ComponentRootOrientation false * (δ * x) ∈ Ioo (C.left m) (C.right m) := by
    simpa only [n01ComponentRoot, n01ComponentRootOrientation,
      Bool.false_eq_true, ↓reduceIte, one_mul] using hphysical
  have hh := n03_rootTravel_eq_controlledRootTravel_on_band
    hS hT hN hE hL hA hB hz hs m false hg hR hstrip hΘ hmatch hx hphysical' θ
  have htravel : (V - U) / 2 = x ^ (3 / 2 : ℝ) * rootOddCoefficient G (x, θ) := by
    simpa only [V, U, G, canonicalGluedRootTravel, n01ComponentRoot,
      n01ComponentRootOrientation, Bool.false_eq_true, ↓reduceIte, one_mul] using hh.1
  have hangle : (V + U) / 2 =
      (G (x, x ^ (3 / 2 : ℝ), θ) + G (x, -(x ^ (3 / 2 : ℝ)), θ)) / 2 := by
    simpa only [V, U, G, rootEven, n01ComponentRoot,
      n01ComponentRootOrientation, Bool.false_eq_true, ↓reduceIte, one_mul] using hh.2
  have ht := congrArg Prod.fst
    (characteristicTravelChart_rootCharacteristicCoordinate G (p := (x, θ)) hx.1)
  change (G (x, -(x ^ (3 / 2 : ℝ)), θ) - G (x, x ^ (3 / 2 : ℝ), θ)) / 2 =
    x ^ (3 / 2 : ℝ) * rootOddCoefficient G (x, θ) at ht
  change V = G (x, -(x ^ (3 / 2 : ℝ)), θ) ∧ U = G (x, x ^ (3 / 2 : ℝ), θ)
  constructor <;> linarith only [htravel, hangle, ht]

end ContinuousFlexibility.Analysis
