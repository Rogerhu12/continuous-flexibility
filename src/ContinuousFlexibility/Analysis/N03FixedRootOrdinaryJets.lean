module

public import ContinuousFlexibility.Analysis.N03FixedRootHeightIdentity
public import ContinuousFlexibility.Analysis.N01ScaledDividedFactorJets
public import ContinuousFlexibility.Analysis.RootChartExtensionGeometry
public import ContinuousFlexibility.Analysis.OpenGermBoundaryJets

/-!
# Ordinary jets of the actual chart and height on a fixed root band

The genuine whole-band identities determine every ordinary derivative,
including both edges of the band. The old chart and height have their
actual closed-domain regularity. The new height is the divided formula,
so no derivative of a singular quotient is assumed. The same flow,
scale, state and physical half are retained throughout.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n03_fixedRoot_chart_height_ordinaryJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} {R δ ρ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hscale : δ * ρ ≤ R / 4)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hband : ControlledRootBandChartAgreement C K z m rightEnd δ ρ Θ)
    (hcoeff : ∀ x ∈ Ioc (0 : ℝ) ρ, ∀ θ : ℝ,
      let p : PolarPoint := (n01ComponentRoot C m rightEnd +
        n01ComponentRootOrientation rightEnd * (δ * x), θ)
      (L.coefficients z).a p = (originalCoefficients D S C z).a p ∧
      (L.coefficients z).b p = (originalCoefficients D S C z).b p ∧
      (L.coefficients z).c p = (originalCoefficients D S C z).c p)
    (hG : ContDiff ℝ ∞
      (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)))
    (hperiod : ∀ x ζ θ,
      rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
          (x, ζ, θ + Real.pi) =
        rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
          (x, ζ, θ) + Real.pi)
    {q : PolarPoint} (hq : q.1 ∈ Icc (0 : ℝ) ρ)
    (hV : ContDiffAt ℝ ∞
      (rootScaledDividedDiscriminant D S C z g (n01ComponentRoot C m rightEnd)
        (n01ComponentRootOrientation rightEnd) δ) q)
    (hVp : 0 < rootScaledDividedDiscriminant D S C z g
      (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) δ q)
    (hχp : 0 < extendedRootOddCoefficient
      (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)) q) :
    let r := n01ComponentRoot C m rightEnd
    let σ := n01ComponentRootOrientation rightEnd
    let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
    let arg : PolarPoint → PolarPoint := fun p => (r + σ * (δ * p.1), p.2)
    let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
    let V := rootScaledDividedDiscriminant D S C z g r σ δ
    ContDiffAt ℝ ∞ (fun p => K.chart z i (arg p)) q ∧
      ContDiffAt ℝ ∞ (fun p => K.height z i (arg p)) q ∧
      (∀ n : ℕ, iteratedFDeriv ℝ n (fun p => K.chart z i (arg p)) q =
        iteratedFDeriv ℝ n (extendedRootEvenOddChart G) q) ∧
      ∀ a : ℝ, ∀ n : ℕ,
        iteratedFDeriv ℝ n (fun p => K.height z i (arg p) ^ a) q =
          iteratedFDeriv ℝ n (fun p => rootDividedHeight δ V G p ^ a) q := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
  let arg : PolarPoint → PolarPoint := fun p => (r + σ * (δ * p.1), p.2)
  let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
  let V := rootScaledDividedDiscriminant D S C z g r σ δ
  let U : Set PolarPoint := Ioo (0 : ℝ) ρ ×ˢ (univ : Set ℝ)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hqU : q ∈ closure U := by
    dsimp only [U]
    rw [closure_prod_eq, closure_Ioo hρ.ne, closure_univ]
    exact ⟨hq, mem_univ _⟩
  have hclosed : arg q ∈ physicalPieceClosed S K z i := by
    by_cases hzero : q.1 = 0
    · have hh := (canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m rightEnd q.2).1
      simpa only [arg, r, i, n01ComponentRoot, hzero, mul_zero, add_zero] using hh
    · exact subset_closure (hband q.1 ⟨lt_of_le_of_ne hq.1 (Ne.symm hzero), hq.2⟩ q.2).1
  have hregular := (hA.boundary z hz hs i).2.2.2.2.1 (arg q) hclosed
  have harg : ContDiff ℝ ∞ arg :=
    (contDiff_const.add (contDiff_const.mul
      (contDiff_const.mul contDiff_fst))).prodMk contDiff_snd
  have hF := hregular.1.comp q harg.contDiffAt
  have heF : K.chart z i ∘ arg = (fun p => K.chart z i (arg p)) := by
    funext p
    exact Function.comp_apply
  rw [heF] at hF
  have hH := hregular.2.1.comp q harg.contDiffAt
  have heH : K.height z i ∘ arg = (fun p => K.height z i (arg p)) := by
    funext p
    exact Function.comp_apply
  rw [heH] at hH
  have hχperiod : ∀ t, 0 ≤ t →
      Function.Periodic (fun θ => rootOddCoefficient G (t, θ)) Real.pi :=
    fun t _ => rootOddCoefficient_periodic hperiod t
  have hφperiod : ∀ t, 0 ≤ t → ∀ θ,
      rootEven G (t, θ + Real.pi) = rootEven G (t, θ) + Real.pi :=
    fun t _ θ => rootEven_period_add hperiod t θ
  have hnew := contDiffAt_extendedRootEvenOddChart_of_ne_zero
    hG Real.pi_ne_zero hχperiod hφperiod hχp.ne'
  have hχ : ContDiffAt ℝ ∞ (extendedRootOddCoefficient G) q :=
    (contDiff_extendedRootOddCoefficient hG Real.pi_ne_zero hχperiod).contDiffAt
  have hnewH := contDiffAt_rootDividedHeight hδ hV hχ hVp hχp
  have hFeq : EqOn (fun p => K.chart z i (arg p)) (extendedRootEvenOddChart G) U := by
    intro p hp
    exact (hband p.1 ⟨hp.1.1, hp.1.2.le⟩ p.2).2
  have hHeq : EqOn (fun p => K.height z i (arg p)) (rootDividedHeight δ V G) U := by
    intro p hp
    have hpband : p.1 ∈ Ioc (0 : ℝ) ρ := ⟨hp.1.1, hp.1.2.le⟩
    have hpscale : δ * p.1 ≤ R / 4 :=
      (mul_le_mul_of_nonneg_left hpband.2 hδ.le).trans hscale
    exact n03_fixedRoot_height_eq_dividedHeight hS hT hN hL hA hB hz hs m rightEnd
      hR hδ hpband.1 hpscale hstrip (hband p.1 hpband p.2).1
      (hband p.1 hpband p.2).2 (hcoeff p.1 hpband p.2)
  refine ⟨hF, hH, ?_, ?_⟩
  · intro n
    exact iteratedFDeriv_eq_of_eqOn_open_of_mem_closure hU hqU hFeq hF hnew n
  · intro a n
    exact iteratedFDeriv_eq_of_eqOn_open_of_mem_closure hU hqU
      (fun p hp => congrArg (fun t : ℝ => t ^ a) (hHeq hp))
      (hH.rpow_const_of_ne hregular.2.2.2.ne')
      (hnewH.1.rpow_const_of_ne hnewH.2.ne') n

end ContinuousFlexibility.Analysis
