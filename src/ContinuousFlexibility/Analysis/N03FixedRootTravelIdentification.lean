module

public import ContinuousFlexibility.Analysis.N03FixedRootInverseIdentification
public import ContinuousFlexibility.Analysis.RootCharacteristicReflection
public import ContinuousFlexibility.Analysis.RootScaledInverseReflection
public import ContinuousFlexibility.Analysis.RootTravelDifferential
public import ContinuousFlexibility.Analysis.CanonicalRootTravelDomain

/-!
# Actual root travel throughout the fixed correction band

The same controlled inverse identifies both true glued characteristic
values before any choice of a canonical half. Their difference therefore
identifies the root travel on the entire physical band, including points
on the moving cut. This is the input to a quantitative domain criterion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem rootTravelAndAngle_eq_of_reflected_footpoint_values
    {G : ℝ × ℝ × ℝ → ℝ} {p : PolarPoint} {V U T : ℝ}
    (rightEnd : Bool) (hp : 0 < p.1)
    (hreflect : ∀ x ζ θ, G (x, -ζ, -θ) = -G (x, ζ, θ))
    (hV : G (p.1, (if rightEnd then (1 : ℝ) else -1) * p.1 ^ (3 / 2 : ℝ), p.2) =
      V - if rightEnd then T else 0)
    (hU : G (p.1, (if rightEnd then (1 : ℝ) else -1) * p.1 ^ (3 / 2 : ℝ), -p.2) =
      -U - if rightEnd then T else 0) :
    (if rightEnd then T - (V - U) / 2 else (V - U) / 2) =
        p.1 ^ (3 / 2 : ℝ) * rootOddCoefficient G p ∧
      (V + U) / 2 = rootEven G p := by
  have ht := congrArg Prod.fst (characteristicTravelChart_rootCharacteristicCoordinate G hp)
  simp only [characteristicTravelChart, rootCharacteristicCoordinate,
    one_mul, neg_one_mul] at ht
  have he : (G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) +
      G (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2)) / 2 = rootEven G p := rfl
  cases rightEnd with
  | false =>
      simp only [Bool.false_eq_true, ite_false, neg_one_mul, sub_zero] at hV hU ⊢
      have hr : G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) =
          -G (p.1, -(p.1 ^ (3 / 2 : ℝ)), -p.2) := by
        simpa only [neg_neg] using hreflect p.1 (-(p.1 ^ (3 / 2 : ℝ))) (-p.2)
      rw [hr, hV, hU] at ht he
      constructor <;> linarith only [ht, he]
  | true =>
      simp only [ite_true, one_mul] at hV hU ⊢
      have hr : G (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2) =
          -G (p.1, p.1 ^ (3 / 2 : ℝ), -p.2) := by
        simpa only [neg_neg] using hreflect p.1 (p.1 ^ (3 / 2 : ℝ)) (-p.2)
      rw [hr, hV, hU] at ht he
      constructor <;> linarith only [ht, he]

theorem n03_rootTravel_eq_controlledRootTravel_on_band
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hE : N02Properties D T S C E base ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R δ η : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations
      (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z) δ) Θ)
    (hmatch : RootStoredFlowAgreementOn C L z m rightEnd δ η Θ)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) η)
    (hphysical : n01ComponentRoot C m rightEnd +
      n01ComponentRootOrientation rightEnd * (δ * x) ∈ Ioo (C.left m) (C.right m))
    (θ : ℝ) :
    let r := n01ComponentRoot C m rightEnd
    let σ := n01ComponentRootOrientation rightEnd
    let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
    canonicalGluedRootTravel S K z m rightEnd (r + σ * (δ * x), θ) =
        x ^ (3 / 2 : ℝ) * rootOddCoefficient G (x, θ) ∧
      (canonicalGluedAiryIntegral S K z m 1 (r + σ * (δ * x), θ) +
        canonicalGluedAiryIntegral S K z m (-1) (r + σ * (δ * x), θ)) / 2 =
          rootEven G (x, θ) := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let p : PolarPoint := (r + σ * (δ * x), θ)
  let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
  let V := canonicalGluedAiryIntegral S K z m 1 p
  let U := canonicalGluedAiryIntegral S K z m (-1) p
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  have hparity := localizedRootFields_reflect hS C g r σ hR z
  have hreflect (a ζ φ : ℝ) : G (a, -ζ, -φ) = -G (a, ζ, φ) :=
    rootScaledInverseCoordinate_reflect hregular.1 hregular.2 hperiod.1 hperiod.2
      (fun a b => (hparity a b).1) (fun a b => (hparity a b).2) hΘ
      (n01RootLabel_odd hN hz hs m rightEnd) (Real.sqrt δ) a ζ φ
  have hfoot (φ : ℝ) : G (x, (-σ) * x ^ (3 / 2 : ℝ), φ) =
      stateLeftChart S z.1 m (Function.invFun (L.minusFlow z m p.1) φ) -
        if rightEnd then C.travel m else 0 :=
    n03_rootScaledInverseCoordinate_eq_storedFootpoint_on_band
      hS hT hN hL hA hB hz hs m rightEnd hg hR hstrip hΘ hmatch ⟨hx.1.le, hx.2⟩ φ
  have hV : V = stateLeftChart S z.1 m (Function.invFun (L.minusFlow z m p.1) θ) :=
    (canonicalGluedAiryIntegral_eq_storedFootpoints
      hS hT hN hL hA hB hz hs hE m hphysical θ).1
  have honto := (n03CharacteristicSlice_bijective
    hS hT hN hL hA hB hz hs hE m hphysical).2
  let φ := Function.invFun (L.minusFlow z m p.1) (-θ)
  have hφ : L.minusFlow z m p.1 φ = -θ := Function.rightInverse_invFun honto (-θ)
  have hodd : stateLeftChart S z.1 m (-φ) = -stateLeftChart S z.1 m φ :=
    (hN.2.2.2.2.2.2.2.1 z hz hs m φ).2.2.2
  have hU : U = -stateLeftChart S z.1 m φ := by
    have hflow : canonicalGluedAiryIntegral S K z m (-1)
        (p.1, -L.minusFlow z m p.1 φ) = -stateLeftChart S z.1 m φ := by
      simpa only [neg_neg, hodd] using
        (canonicalGluedAiryIntegral_on_n03Flows
          hS hT hN hE hL hA hB hz hs m hphysical (-φ)).2
    rw [hφ, neg_neg] at hflow
    exact hflow
  have hσ : -σ = if rightEnd then (1 : ℝ) else -1 := by
    cases rightEnd <;> norm_num [σ, n01ComponentRootOrientation]
  have hV' : G (x, (if rightEnd then (1 : ℝ) else -1) * x ^ (3 / 2 : ℝ), θ) =
      V - if rightEnd then C.travel m else 0 := by
    have he := (hfoot θ).trans
      (congrArg (fun v : ℝ => v - if rightEnd then C.travel m else 0) hV.symm)
    simpa only [hσ] using he
  have hU' : G (x, (if rightEnd then (1 : ℝ) else -1) * x ^ (3 / 2 : ℝ), -θ) =
      -U - if rightEnd then C.travel m else 0 := by
    have hv : stateLeftChart S z.1 m φ = -U := by linarith only [hU]
    have he := (hfoot (-θ)).trans
      (congrArg (fun v : ℝ => v - if rightEnd then C.travel m else 0) hv)
    simpa only [hσ] using he
  have ht := rootTravelAndAngle_eq_of_reflected_footpoint_values
    (p := (x, θ)) rightEnd hx.1 hreflect hV' hU'
  have hwidth := (canonicalRootGauges_eq_n01_of_n03
    hS hT hN hE hL hA hB hz hs m).1
  simpa only [canonicalGluedRootTravel, hwidth, V, U, p] using ht

end ContinuousFlexibility.Analysis
