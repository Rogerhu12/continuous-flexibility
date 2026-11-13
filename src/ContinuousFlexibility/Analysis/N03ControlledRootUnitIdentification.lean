import ContinuousFlexibility.Analysis.N01ControlledRootInput
import ContinuousFlexibility.Analysis.N03StateRootBandIdentification
import ContinuousFlexibility.Analysis.N03RootUnitScaleIdentification

/-!
# The actual controlled input identifies the original stored root jets

The existing N01 constructor supplies the flow and its finite first-jet
bound. That bound is used only to obtain the genuine state-dependent N03
band. The same stored chart and height then have exactly the unit-model
ordinary jets. No inverse of the chosen band or parameter scale is charged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n03_controlledRootInput_unit_identification
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss flowLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R κ δ Λ : ℝ}
    (hR : 0 < R) (hκ : 0 < κ) (hδ : 0 < δ)
    {A : ℕ → ℝ} (hApos : ∀ n, 0 < A n)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m side)
      (n01ComponentRootOrientation side) R)
    (hinput : N01ControlledRootInputAtState D S C m side g hR κ δ Λ flowLoss A z) :
    ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m side)
          (n01ComponentRootOrientation side) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m side)
          (n01ComponentRootOrientation side) hR z) δ) Θ ∧
      ∀ θ : ℝ,
        let r := n01ComponentRoot C m side
        let σ := n01ComponentRootOrientation side
        let i := if side then (K.cutPair m).2 else (K.cutPair m).1
        let arg := rootProfileShift r σ
        let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
          (n01RootLabel S C z m side)
        let V := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ
        (r, θ) ∈ physicalPieceClosed S K z i ∧
          ContDiffAt ℝ ∞ (fun p => K.chart z i (arg p)) (0, θ) ∧
          ContDiffAt ℝ ∞ (fun p => K.height z i (arg p)) (0, θ) ∧
          0 < K.height z i (r, θ) ∧
          (∀ n : ℕ, iteratedFDeriv ℝ n (fun p => K.chart z i (arg p)) (0, θ) =
            iteratedFDeriv ℝ n (extendedRootEvenOddChart G) (0, θ)) ∧
          ∀ γ : ℝ, ∀ n : ℕ,
            iteratedFDeriv ℝ n (fun p => K.height z i (arg p) ^ γ) (0, θ) =
              iteratedFDeriv ℝ n (fun p => rootDividedHeight 1 V G p ^ γ) (0, θ) := by
  obtain ⟨_, Θ, hΘ, hG, hperiod, _, hodd, hCS⟩ := hinput
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let V := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ
  let M := A 1 * (1 + pairGrading (stateGrading S) realGrading (1 + flowLoss)
    (z - (C.referenceState, 0)))
  have hM : 0 ≤ M :=
    mul_nonneg (hApos 1).le (add_nonneg zero_le_one (apply_nonneg _ _))
  obtain ⟨ρ, hρ, _, hρR, hband, hcoeff⟩ :=
    n03_exists_state_controlledRoot_band hS hT hN hfield hA hB hz hs m side
      hg hR hδ hM hstrip Θ hΘ hG hperiod (hCS 1)
  refine ⟨Θ, hΘ, ?_⟩
  intro θ
  have hzero : ((0, θ) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith only [hR]
  have hdata := hstrip (0, θ) hzero
  have hV : ContDiffAt ℝ ∞ V (0, θ) :=
    contDiffAt_rootCoefficientRadialFactor hN.1.1.1.1.choose_spec.1.2.2.1.1 hg
      (contDiff_stateProfile_of_n01 hS hT hN.1.1 z.1)
      (contDiff_stateHeight_of_n01 hS hT hN.1.1 z)
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1
  have hVp : 0 < V (0, θ) := by
    change 0 < rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ (0, θ)
    rw [rootCoefficientRadialFactor_eq hdata.1 hdata.2.1 hdata.2.2.1
      hdata.2.2.2.1 hdata.2.2.2.2.1.ne']
    exact div_pos (rootProfileRadicand_pos hdata.1 hdata.2.1 hdata.2.2.1)
      (pow_pos hdata.2.2.2.1 2)
  have hscaled : ContDiffAt ℝ ∞
      (rootScaledDividedDiscriminant D S C z g r σ δ) (0, θ) := by
    have hv : ContDiffAt ℝ ∞ V ((fun p : PolarPoint => (δ * p.1, p.2)) (0, θ)) := by
      simpa only [mul_zero] using hV
    have hmap : ContDiff ℝ ∞ (fun p : PolarPoint => (δ * p.1, p.2)) :=
      (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
    have hc := hv.comp (0, θ) hmap.contDiffAt
    simpa only [Function.comp_def, V, rootScaledDividedDiscriminant] using hc
  have hscaledPos : 0 < rootScaledDividedDiscriminant D S C z g r σ δ (0, θ) := by
    simpa only [rootScaledDividedDiscriminant, V, mul_zero] using hVp
  have hoddPos : 0 < extendedRootOddCoefficient
      (rootScaledInverseCoordinate Θ (n01RootLabel S C z m side) (Real.sqrt δ))
      (0, θ) := by
    rw [extendedRootOddCoefficient_of_nonneg _ le_rfl]
    apply lt_of_lt_of_le _ (hodd θ)
    exact div_pos (mul_pos (mul_pos hδ (Real.sqrt_pos.mpr hδ)) hκ)
      (by cases side <;> norm_num)
  have hident := n03_fixedRoot_unitScale_ordinaryJets hS hT hN.1.1 hN.2 hA hB
    hz hs m side hR hδ hρ hρR hstrip Θ hband hcoeff hG hperiod θ
    hscaled hscaledPos hoddPos
  have hclosed : (r, θ) ∈ physicalPieceClosed S K z i := by
    simpa only [r, i, n01ComponentRoot] using
      (canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m side θ).1
  have hregular := (hA.boundary z hz hs i).2.2.2.2.1 (r, θ) hclosed
  exact ⟨hclosed, hident.1, hident.2.1, hregular.2.2.2,
    hident.2.2.1, hident.2.2.2⟩

end ContinuousFlexibility.Analysis
