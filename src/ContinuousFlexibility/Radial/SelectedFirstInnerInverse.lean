import ContinuousFlexibility.Radial.FixedCentralFirstInverse
import ContinuousFlexibility.Radial.InnerMorseInnerChain
import ContinuousFlexibility.Radial.InnerPhysicalFrozenInverse
import ContinuousFlexibility.Radial.ReferenceFirstGapSlope
import ContinuousFlexibility.Radial.FirstConeLayerSeparation

/-!
# The actual first-band inner inverse in the frozen coordinates

A fixed central R09 model is installed between the two actual first
matching joins. The retained pair supplies the two complete positive
gaps and their uniform logarithmic slope. The resulting inverse and all
its representatives satisfy the original modal graph, with a cost fixed
before the retained-cone length or either side dilation is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.L2Operator

/-- This threshold depends only on the fixed central model. -/
def selectedFirstInnerModelWindow : ℝ :=
  Classical.choose exists_centralModel_logSlope_window

theorem selectedFirstInnerModelWindow_spec :
    8 ≤ selectedFirstInnerModelWindow ∧
      sqrt centralOscillatorA + 2 ≤ selectedFirstInnerModelWindow ∧
      ∀ T : ℝ, selectedFirstInnerModelWindow ≤ T → ∀ r : ℝ, 0 < r →
        (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
        (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r :=
  Classical.choose_spec exists_centralModel_logSlope_window

theorem SeedRetainedPair.exists_first_inner_inverse {S : SelectedTailData}
    {K₀ : SeedCentralCutoff} {headLength length : ℝ}
    (P : SeedRetainedPair S K₀ headLength length)
    (hS : IsSelectedTail S)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hcone : ∀ side, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ uIcc (S.cut side S.chain.index)
      (S.joinInner side S.chain.index), (S.family S.sigma).w =ᶠ[𝓝 x] (fun t => c * t))
    (hhead : 0 < headLength) (B : FixedCentralBorder)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hleft : Γ.centralLeft = exp K₀.left) (hright : Γ.centralRight = exp K₀.right)
    {T B₀ C K : ℝ} (hT : selectedFirstInnerModelWindow ≤ T) (hC : 0 < C)
    (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
    (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
    (hcolumn : referenceColumn Γ.reference = fixedCentralColumn B.chi)
    (q : ℕ) (hq : 1 ≤ q) (hB : BufferHypotheses (B.modelBuffer q T B₀))
    (model : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)
    (hk : ∀ i, 0 < fixedCentralModelCutEnergy model i)
    (herror : ∀ sign : Bool,
      ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa model) (fun _ => 1)
        (model.physicalFluxError 1
          (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))) sign‖ ≤
        (1 : ℝ) / 8)
    (M : RadialMatchingData Γ.reference) (hfrequency : M.frequency = 2 * q)
    (hML : M.innerLeft = P.sideRadius false * S.joinInner false S.chain.index)
    (hMR : M.innerRight = P.sideRadius true * S.joinInner true S.chain.index)
    (hsource : M.sourceInner = modeInnerSource Γ.reference M.innerLeft M.innerRight) :
    ∃ A : RadialModePair Γ.reference →L[ℝ] RadialModePair Γ.reference,
    ∃ u : RadialModePair Γ.reference → ℝ → ℝ,
      ‖A‖ ≤ sqrt 2 * fixedCentralFirstInverseCost model (2 * (q : ℝ)) T B₀ ∧
      (∀ F, A (M.sourceInner F) = A F) ∧
      (∀ F, (M.frequency ≠ 2 → F.2 = 0) →
        ModeInnerDirichletGraph Γ.reference M (A (M.sourceInner F)) (M.sourceInner F)) ∧
      (∀ U F, ModeInnerDirichletGraph Γ.reference M U F → A F = U) ∧
      ∀ F, ((A (M.sourceInner F)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure Γ.reference] u F ∧
        ModeLocalEquation Γ.reference M.frequency (Ioo M.innerLeft M.innerRight)
          (A (M.sourceInner F)) (M.sourceInner F) ∧
        ContDiffOn ℝ 1 (u F) (Icc M.innerLeft M.innerRight) ∧
        (∀ r ∈ matchingOuterRegion Γ.reference M, u F r = 0) ∧
        (if M.frequency = 2 then
          (∫ r in Γ.reference.a..Γ.reference.b, referenceColumn Γ.reference r * u F r) = F.2
         else (A (M.sourceInner F)).2 = 0) ∧
        ∀ i, u F (matchingCut Γ.reference M i) = 0 := by
  have hD : IsAccumulatingProfile Γ.reference := hΓ.2.1
  have hb : RadialTrueBorder Γ.reference := hΓ.2.2.1
  have hgeom : RadialProfileGeometry Γ.reference := (Classical.choose_spec hD).1
  have hold : RadialProfileGeometry (S.family S.sigma) :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have h8 : 8 ≤ T := selectedFirstInnerModelWindow_spec.1.trans hT
  have hcap : sqrt centralOscillatorA + 2 ≤ T :=
    selectedFirstInnerModelWindow_spec.2.1.trans hT
  have hwindow := selectedFirstInnerModelWindow_spec.2.2 T hT
  let L := P.sideRadius false * S.joinInner false S.chain.index
  let R := P.sideRadius true * S.joinInner true S.chain.index
  let center : Fin 2 → ℝ := fun i => if i = 0 then centralRadius (-T) else centralRadius T
  have hjcore (side : Bool) :
      P.sideRadius side * S.joinInner side S.chain.index ∈ radialCore Γ.reference := by
    have hm := hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hfirst
    have ho : if side then S.cut side S.chain.index ≤ S.joinInner side S.chain.index
        else S.joinInner side S.chain.index ≤ S.cut side S.chain.index := by
      cases side
      · exact hm.2.2.2.2.1.2.le
      · exact hm.2.2.2.2.1.1.le
    apply radialCore_mem_of_profile_pos hgeom
    rw [P.reference_side_old_value hw hS side hm.2.2.1 ho]
    exact mul_pos (mul_pos (P.sideHeight_pos side) (P.sideRadius_pos side))
      (hold.2.2.2.2.1 _ hm.2.2.1)
  obtain ⟨hLC, hCI, hIL, _, hRI, hIC, hCJ⟩ :=
    P.first_matching_order hS hfirst hhead hleft hright
  have hl : L < center 0 := hLC.trans (hCI.trans (hIL.trans hTL))
  have hc : center 0 < center 1 :=
    strictMono_centralRadius (by linarith only [h8] : -T < T)
  have hr : center 1 < R := hTR.trans (hRI.trans (hIC.trans hCJ))
  let G := innerCentralOnlyChainGeometry Γ.reference hgeom center L R
    (hjcore false) (hjcore true) hl hc hr
  have hG0 : G.left 0 = L :=
    innerModelChainCuts_first (fun _ : Fin 1 => center) L R
  have hG2 : G.right (Fin.last 2) = R :=
    innerModelChainCuts_last (fun _ : Fin 1 => center) L R
  have hGL : G.left 1 = centralRadius (-T) :=
    innerModelChainCuts_model_left (fun _ : Fin 1 => center) L R 0
  have hGR : G.right 1 = centralRadius T :=
    innerModelChainCuts_model_right (fun _ : Fin 1 => center) L R 0
  have hG01 : G.right 0 = centralRadius (-T) := hGL
  have hG21 : G.left 2 = centralRadius T := hGR
  have hab : M.innerLeft < M.innerRight := by
    rw [hML, hMR]
    exact hl.trans (hc.trans hr)
  have hsub : Icc M.innerLeft M.innerRight ⊆ radialCore Γ.reference := by
    intro r hmem
    rw [hML, hMR] at hmem
    exact ⟨(hjcore false).1.trans_le hmem.1, hmem.2.trans_lt (hjcore true).2⟩
  have hcentral : Ioo (centralRadius (-T)) (centralRadius T) ⊆ radialCore Γ.reference := by
    intro r hmem
    apply hsub
    rw [hML, hMR]
    exact ⟨(hl.trans hmem.1).le, (hmem.2.trans hr).le⟩
  have hweight (x : ℝ) (hx : x ∈ Icc (-T) T) :
      Γ.reference.w (centralRadius x) = 1 * centralDensityRoot x ^ 2 * deriv centralRadius x := by
    rw [hmodel ⟨hTL.trans_le (strictMono_centralRadius.monotone hx.1),
      (strictMono_centralRadius.monotone hx.2).trans_lt hTR⟩,
      centralRadialProfile_pullback]
  have hslope : ∀ p : Fin 3, p ≠ 1 → ∀ r ∈ Icc (G.left p) (G.right p),
      (3 : ℝ) / 4 ≤ r * deriv Γ.reference.w r / Γ.reference.w r := by
    intro p hp r hmem
    apply (le_div_iff₀ (G.weight_pos p r hmem)).mpr
    apply P.reference_first_gaps_logSlope hw hS hfirst hcone hleft hright
      (by linarith only [h8] : 0 ≤ T) hTL hTR hmodel hwindow
      ((G.left_pos p).trans_le hmem.1)
    rcases (show p = 0 ∨ p = 2 by omega) with rfl | rfl
    · exact Or.inl (by simpa only [hG0, hG01] using hmem)
    · exact Or.inr (by simpa only [hG21, hG2] using hmem)
  have hbool : centralModelBordered q = decide (M.frequency = 2) := by
    by_cases hq1 : q = 1
    · simp [centralModelBordered, hq1, hfrequency]
    · have hf : M.frequency ≠ 2 := by omega
      simp [centralModelBordered, hq1, hf]
  have hfreq : (M.frequency : ℝ) = 2 * (q : ℝ) := by exact_mod_cast hfrequency
  have hex := exists_fixedCentralThreePieceInverse B Γ.reference hD hb G q hq hC h8 hcap
    hcolumn hcentral hweight hGL hGR hslope hB model hk herror
  rw [hbool] at hex
  obtain ⟨hwD, inverse, hgraph, hnorm, _⟩ := hex
  have hsolve : ∀ F, InnerRadialPhysicalWeakGraph Γ.reference hwD.continuous G
      (decide (M.frequency = 2)) (M.frequency : ℝ) 1
      (matchingBorderVector Γ.reference hD hb) (inverse F) F := by
    intro F
    rw [hfreq]
    exact (hgraph (inverse F) F).mpr rfl
  have hGLM : G.left 0 = M.innerLeft := hG0.trans hML.symm
  have hGRM : G.right (Fin.last 2) = M.innerRight := hG2.trans hMR.symm
  have hcolAE : (matchingBorderVector Γ.reference hD hb : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure Γ.reference]
        fun r => referenceColumn Γ.reference r / matchingDensity Γ.reference r :=
    matchingBorderVector_coe hD hb
  have hgs : Function.support (referenceColumn Γ.reference) ⊆ Ioo (G.left 1) (G.right 1) := by
    rw [hGL, hGR, hcolumn]
    exact B.column_support_in_model hcap
  let A := InnerRadialPhysicalInverse.pairInverse inverse hD
  let u := InnerRadialPhysicalInverse.frozenRepresentative inverse hD hb hwD hsolve
    hGLM hGRM hab hsub hcolAE hgs
  refine ⟨A, u, InnerRadialPhysicalInverse.pairInverse_norm_le_of_bound inverse hD hnorm,
    ?_, ?_, ?_, ?_⟩
  · intro F
    rw [hsource]
    simpa only [hGLM, hGRM] using
      InnerRadialPhysicalInverse.pairInverse_innerSource inverse hD F
  · intro F hF
    rw [hsource]
    exact InnerRadialPhysicalInverse.pairInverse_right_frozen inverse hD hb hwD hsolve
      hGLM hGRM hab hsub hcolAE hgs F hF
  · intro U F hU
    exact InnerRadialPhysicalInverse.pairInverse_left_frozen inverse hD hb hwD hsolve
      hGLM hGRM hab hsub hcolAE hgs hU
  · intro F
    rw [hsource]
    exact InnerRadialPhysicalInverse.frozenRepresentative_spec inverse hD hb hwD hsolve
      hGLM hGRM hab hsub hcolAE hgs F

end ContinuousFlexibility.Radial
