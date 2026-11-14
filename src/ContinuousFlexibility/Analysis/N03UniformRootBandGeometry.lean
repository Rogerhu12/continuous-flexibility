module

public import ContinuousFlexibility.Analysis.N03FixedRootTravelIdentification
public import ContinuousFlexibility.Analysis.RootTravelUniformBounds
public import ContinuousFlexibility.Analysis.RootAiryCoordinateIdentification

/-!
# A uniform physical band in the correct moving canonical half

The cutoff band and a common first-derivative bound determine one smaller
radius before the state or the controlled flow is chosen. Actual travel
then excludes the moving cut and the opposite half. On this whole band
the stored chart equals the chart of the same controlled inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def ControlledRootBandChartAgreement
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (rightEnd : Bool) (δ ρ : ℝ)
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) : Prop :=
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
  let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
  ∀ x ∈ Ioc (0 : ℝ) ρ, ∀ θ : ℝ,
    (r + σ * (δ * x), θ) ∈ physicalPieceOpen S K z i ∧
      K.chart z i (r + σ * (δ * x), θ) = extendedRootEvenOddChart G (x, θ)

private theorem canonical_chart_eq_rootChart_of_glued_values
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {G : ℝ × ℝ × ℝ → ℝ} {p q : PolarPoint} (hq : 0 < q.1)
    (hp : p ∈ physicalPieceOpen S K z
      (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1))
    (ht : canonicalGluedRootTravel S K z m rightEnd p =
      q.1 ^ (3 / 2 : ℝ) * rootOddCoefficient G q)
    (ha : (canonicalGluedAiryIntegral S K z m 1 p +
      canonicalGluedAiryIntegral S K z m (-1) p) / 2 = rootEven G q) :
    K.chart z (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1) p =
      extendedRootEvenOddChart G q := by
  let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
  have hvalues := canonicalCutPair_chartValues_of_gluedIntegrals
    m rightEnd (hB.1.2 z hz hs m).2.2.1 hp
  have htravel : airyTravelPrimitive (K.chart z i p).1 =
      q.1 ^ (3 / 2 : ℝ) * rootOddCoefficient G q := hvalues.2.trans ht
  have hangle : (K.chart z i p).2 = rootEven G q := hvalues.1.trans ha
  obtain ⟨_, _, _, _, _, _, hl, hr, _, _⟩ := hB.1.1 m
  have hzero : K.left i = 0 := by cases rightEnd <;> assumption
  have hcanonical := (hA.charts z hz hs i).1 hp
  have hnonneg : 0 ≤ (K.chart z i p).1 := by
    have hb : K.left i < (K.chart z i p).1 := hcanonical.1.1
    exact (hzero ▸ hb).le
  apply (extendedRootEvenOddChart_eq_of_travel_values hq hnonneg ?_).symm
  exact (characteristicTravelChart_rootCharacteristicCoordinate G hq).trans
    (Prod.ext htravel.symm hangle.symm)

/-- The only numerical input is the true order-one bound for the same
controlled inverse. Its radius is selected before all states and flows. -/
theorem n03_exists_uniform_rootBand_geometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hE : N02Properties D T S C E base ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (m : ℕ) (rightEnd : Bool) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {R δ η M : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hη : 0 < η) (hηone : η ≤ 1)
    (hwidth : δ * η < C.right m - C.left m) (hM : 0 ≤ M)
    (hstrip : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
        (n01ComponentRootOrientation rightEnd) R)
    (hfixed : N03FixedRootFlowIdentification D S C L base ε m rightEnd g hR δ η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ η ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
          N04FlowEquations
            (rootRescaledField
              (localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
                (n01ComponentRootOrientation rightEnd) hR z)
              (localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
                (n01ComponentRootOrientation rightEnd) hR z) δ) Θ →
          CSBound 1
            (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi)
            (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)) M →
          ControlledRootBandChartAgreement C K z m rightEnd δ ρ Θ := by
  have hcut : 0 < K.cutRadius m := (hB.1.1 m).2.2.2.2.2.1
  have hcutTravel : 0 < airyTravelPrimitive (K.cutRadius m) :=
    mul_pos (by norm_num : (0 : ℝ) < 2 / 3) (Real.rpow_pos_of_pos hcut _)
  obtain ⟨ρ, hρ, hρη, hsmall⟩ :=
    exists_rootTravel_uniform_small_band hη hηone hcutTravel hM
  refine ⟨ρ, hρ, hρη, ?_⟩
  intro z hz hs Θ hΘ hbound x hx θ
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
  have hcoeff := hstrip z hz hs
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN hg hR hcoeff
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  have hG := rootScaledInverseCoordinate_regular hregular.1 hregular.2
    hperiod.1 hperiod.2 hΘ (n01RootLabel_contDiff hS hT hN hz hs m rightEnd)
    (n01RootLabel_period_add hN hz hs m rightEnd) (Real.sqrt δ)
  have hdx : 0 < δ * x := mul_pos hδ hx.1
  have hdxwidth : δ * x < C.right m - C.left m :=
    (mul_le_mul_of_nonneg_left (hx.2.trans hρη) hδ.le).trans_lt hwidth
  have hphysical : r + σ * (δ * x) ∈ Ioo (C.left m) (C.right m) := by
    cases rightEnd <;>
      simp only [r, σ, n01ComponentRoot, n01ComponentRootOrientation,
        Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul, Set.mem_Ioo] <;>
      constructor <;> linarith only [hdx, hdxwidth]
  have hvalues := n03_rootTravel_eq_controlledRootTravel_on_band
    hS hT hN hE hL hA hB hz hs m rightEnd hg hR hcoeff hΘ
    (hfixed z hz hs Θ hΘ) ⟨hx.1, hx.2.trans hρη⟩ hphysical θ
  have htravel := hsmall G hG.1 hG.2 hbound x ⟨hx.1.le, hx.2⟩ θ
  have hown := canonicalCutPair_mem_own_half_of_rootTravel_lt hA hB hz hs m rightEnd
    ⟨hphysical, mem_univ θ⟩ (hvalues.1.trans_lt htravel)
  exact ⟨hown, canonical_chart_eq_rootChart_of_glued_values hA hB hz hs m rightEnd
    hx.1 hown hvalues.1 hvalues.2⟩

end ContinuousFlexibility.Analysis
