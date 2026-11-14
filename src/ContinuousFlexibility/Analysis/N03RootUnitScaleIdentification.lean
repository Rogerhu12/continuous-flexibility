module

public import ContinuousFlexibility.Analysis.RootParameterUnscaleRegularity
public import ContinuousFlexibility.Analysis.N03FixedRootOrdinaryJets

/-!
# Unit-scale root jets of the same stored canonical fields

The actual state-dependent root band is used only for an open-side
identity. Its parameter normalization is removed before passing to
ordinary root jets. The stored K, chosen flow, angular label, divided
coefficient and physical root all remain the original ones. Neither the
band radius nor the normalization scale occurs in a derivative bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n03_fixedRoot_unitScale_ordinaryJets
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
    (θ : ℝ)
    (hV : ContDiffAt ℝ ∞
      (rootScaledDividedDiscriminant D S C z g (n01ComponentRoot C m rightEnd)
        (n01ComponentRootOrientation rightEnd) δ) (0, θ))
    (hVp : 0 < rootScaledDividedDiscriminant D S C z g
      (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) δ (0, θ))
    (hχ : 0 < extendedRootOddCoefficient
      (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)) (0, θ)) :
    let r := n01ComponentRoot C m rightEnd
    let σ := n01ComponentRootOrientation rightEnd
    let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
    let arg := rootProfileShift r σ
    let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
      (n01RootLabel S C z m rightEnd)
    let V := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ
    ContDiffAt ℝ ∞ (fun p => K.chart z i (arg p)) (0, θ) ∧
      ContDiffAt ℝ ∞ (fun p => K.height z i (arg p)) (0, θ) ∧
      (∀ n : ℕ, iteratedFDeriv ℝ n (fun p => K.chart z i (arg p)) (0, θ) =
        iteratedFDeriv ℝ n (extendedRootEvenOddChart G) (0, θ)) ∧
      ∀ a : ℝ, ∀ n : ℕ,
        iteratedFDeriv ℝ n (fun p => K.height z i (arg p) ^ a) (0, θ) =
          iteratedFDeriv ℝ n (fun p => rootDividedHeight 1 V G p ^ a) (0, θ) := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
  let arg := rootProfileShift r σ
  let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
    (n01RootLabel S C z m rightEnd)
  let V := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ
  let Vs := rootScaledDividedDiscriminant D S C z g r σ δ
  have hcancel (x : ℝ) : δ * (x / δ) = x := by field_simp [hδ.ne']
  have hVs : ContDiffAt ℝ ∞ Vs
      ((fun p : PolarPoint => (p.1 / δ, p.2)) (0, θ)) := by
    simpa only [zero_div] using hV
  have hargInv : ContDiff ℝ ∞ (fun p : PolarPoint => (p.1 / δ, p.2)) :=
    (contDiff_fst.div_const δ).prodMk contDiff_snd
  have hVunit : ContDiffAt ℝ ∞ V (0, θ) := by
    have hc := hVs.comp (0, θ) hargInv.contDiffAt
    have he : (fun p : PolarPoint => Vs (p.1 / δ, p.2)) = V := by
      funext p
      simp only [Vs, rootScaledDividedDiscriminant, V, hcancel]
    simpa only [Function.comp_def, he] using hc
  have hVpunit : 0 < V (0, θ) := by
    simpa only [V, rootScaledDividedDiscriminant, mul_zero] using hVp
  have hunit := rootDividedModel_parameterUnscale_root_regular Θ
    (n01RootLabel S C z m rightEnd) V hδ hG hperiod hχ hVunit hVpunit
  have hclosed : (r, θ) ∈ physicalPieceClosed S K z i := by
    simpa only [r, i, n01ComponentRoot] using
      (canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m rightEnd θ).1
  have hregular := (hA.boundary z hz hs i).2.2.2.2.1 (r, θ) hclosed
  have harg : ContDiff ℝ ∞ arg :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hpoint : arg (0, θ) = (r, θ) := by
    simp only [arg, rootProfileShift, mul_zero, add_zero]
  have hactualF : ContDiffAt ℝ ∞ (K.chart z i) (arg (0, θ)) := by
    simpa only [hpoint] using hregular.1
  have hactualH : ContDiffAt ℝ ∞ (K.height z i) (arg (0, θ)) := by
    simpa only [hpoint] using hregular.2.1
  have hactualHpos : 0 < K.height z i (arg (0, θ)) := by
    simpa only [hpoint] using hregular.2.2.2
  have hF : ContDiffAt ℝ ∞ (fun p => K.chart z i (arg p)) (0, θ) := by
    simpa only [Function.comp_def] using hactualF.comp (0, θ) harg.contDiffAt
  have hH : ContDiffAt ℝ ∞ (fun p => K.height z i (arg p)) (0, θ) := by
    simpa only [Function.comp_def] using hactualH.comp (0, θ) harg.contDiffAt
  let U : Set PolarPoint := Ioo (0 : ℝ) (δ * ρ) ×ˢ (univ : Set ℝ)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hroot : (0, θ) ∈ closure U := by
    dsimp only [U]
    rw [closure_prod_eq, closure_Ioo (mul_pos hδ hρ).ne, closure_univ]
    exact ⟨⟨le_rfl, (mul_pos hδ hρ).le⟩, mem_univ _⟩
  have hnormalized {p : PolarPoint} (hp : p ∈ U) : p.1 / δ ∈ Ioc (0 : ℝ) ρ :=
    ⟨div_pos hp.1.1 hδ,
      ((div_lt_iff₀ hδ).mpr (hp.1.2.trans_eq (mul_comm δ ρ))).le⟩
  have hFeq : EqOn (fun p => K.chart z i (arg p)) (extendedRootEvenOddChart G) U := by
    intro p hp
    have hx := hnormalized hp
    calc
      _ = extendedRootEvenOddChart
          (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd)
            (Real.sqrt δ)) (p.1 / δ, p.2) := by
        simpa only [arg, rootProfileShift, r, σ, i, hcancel] using
          (hband (p.1 / δ) hx p.2).2
      _ = _ := by
        simpa only [hcancel] using extendedRootEvenOddChart_parameterUnscale_pos
          Θ (n01RootLabel S C z m rightEnd) hδ hx.1 p.2
  have hHeq : EqOn (fun p => K.height z i (arg p)) (rootDividedHeight 1 V G) U := by
    intro p hp
    have hx := hnormalized hp
    have hxR : δ * (p.1 / δ) ≤ R / 4 :=
      (mul_le_mul_of_nonneg_left hx.2 hδ.le).trans hscale
    have hh := n03_fixedRoot_height_eq_dividedHeight hS hT hN hL hA hB hz hs m rightEnd
      hR hδ hx.1 hxR hstrip (hband (p.1 / δ) hx p.2).1
      (hband (p.1 / δ) hx p.2).2 (hcoeff (p.1 / δ) hx p.2)
    calc
      _ = rootDividedHeight δ (fun q => V (δ * q.1, q.2))
          (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd)
            (Real.sqrt δ)) (p.1 / δ, p.2) := by
        simpa only [arg, rootProfileShift, r, σ, i, V, hcancel] using hh
      _ = _ := by
        simpa only [hcancel] using rootDividedHeight_parameterUnscale_pos
          Θ (n01RootLabel S C z m rightEnd) V hδ hx.1 p.2
  refine ⟨hF, hH, ?_, ?_⟩
  · intro n
    exact iteratedFDeriv_eq_of_eqOn_open_of_mem_closure hU hroot hFeq hF hunit.1 n
  · intro a n
    exact iteratedFDeriv_eq_of_eqOn_open_of_mem_closure hU hroot
      (fun p hp => congrArg (fun t : ℝ => t ^ a) (hHeq hp))
      (hH.rpow_const_of_ne hactualHpos.ne')
      (hunit.2.1.rpow_const_of_ne hunit.2.2.ne') n

end ContinuousFlexibility.Analysis
