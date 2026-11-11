import ContinuousFlexibility.Analysis.N01cActualFlowAngularPrefix
import ContinuousFlexibility.Analysis.N01cActualFlowLowBounds
import ContinuousFlexibility.Analysis.N01cCommonCosineTowers
import ContinuousFlexibility.Analysis.N01cOrdinaryFlowZeroAngularBounds
import ContinuousFlexibility.Analysis.N01cSpeedBoundsRestriction

/-!
# Positive state prefixes of the actual zero-radial flow family

Four choices are made once: the actual low flow geometry, the
zero-parameter derivative-defect growth, the actual speed towers, and
the interpolation base. Their maximum base and minimum radius precede
every state prefix and every spatial order.

The actual variational equation, strict lower-order forcing induction,
and one final multilinear normalization prove the bound on every
subsequent stronger-base, smaller-radius neighbourhood. The witness
tower for each physical point is canonical and precedes the state-order
quantifier.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- Select the four fixed inputs while their analytic payloads remain opaque. -/
private theorem n01c_ordinaryFlowAngular_common_selection
    {base : ℕ} {ε : ℝ}
    {Low : ℕ → ℝ → ℝ → ℝ → ℝ → Prop}
    {Part Smooth : ℕ → ℝ → Prop}
    {Growth : ∀ b e, Part b e → Smooth b e → ℕ → Prop}
    {Towers : ℕ → ℝ → Prop} {Normalization : ℕ → ℕ → Prop}
    {Result : ℕ → ℝ → Prop}
    (hLow : ∃ b e, base ≤ b ∧ 0 < e ∧ e ≤ min ε (1 / 2) ∧
      ∃ c M Mlin : ℝ, 0 < c ∧ 0 < M ∧ 0 < Mlin ∧ Low b e c M Mlin)
    (hGrowth : ∃ b e, base ≤ b ∧ 0 < e ∧ e ≤ min ε (1 / 2) ∧
      ∃ hB : Part b e, ∃ hGs : Smooth b e, ∃ d : ℕ, Growth b e hB hGs d)
    (hTowers : ∃ b e, base ≤ b ∧ 0 < e ∧ e ≤ ε ∧ Towers b e)
    (hNormalization : ∃ b l : ℕ, Normalization b l)
    (close :
      ∀ (bg : ℕ) (eg c M Mlin : ℝ), 0 < c → 0 < M → 0 < Mlin →
        Low bg eg c M Mlin →
      ∀ (bq : ℕ) (eq : ℝ) (hBq : Part bq eq) (hGs : Smooth bq eq) (d₀ : ℕ),
        Growth bq eq hBq hGs d₀ →
      ∀ (bt : ℕ) (et : ℝ), Towers bt et →
      ∀ (bn normLoss : ℕ), Normalization bn normLoss →
      ∀ (base' : ℕ) (ε' : ℝ), base ≤ base' → 0 < ε' → ε' ≤ ε → ε' ≤ 1 / 2 →
        bg ≤ base' → bq ≤ base' → bt ≤ base' → bn ≤ base' →
        ε' ≤ eg → ε' ≤ eq → ε' ≤ et → Result base' ε') :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ,
      base ≤ base₀ ∧ 0 < ε₀ ∧ ε₀ ≤ min ε (1 / 2) ∧
      ∀ base' : ℕ, base₀ ≤ base' → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ →
        Result base' ε' := by
  obtain ⟨bg, eg, hbg, heg, hege, c, M, Mlin, hc, hM, hMlin, hlow⟩ := hLow
  obtain ⟨bq, eq, hbq, heq, heqe, hBq, hGs, d₀, hQ⟩ := hGrowth
  obtain ⟨bt, et, hbt, het, hete, htowers⟩ := hTowers
  obtain ⟨bn, normLoss, hnormalization⟩ := hNormalization
  let base₀ : ℕ := max bg (max bq (max bt bn))
  let ε₀ : ℝ := min eg (min eq et)
  have hbase₀ : base ≤ base₀ := hbg.trans (le_max_left _ _)
  have hε₀ : 0 < ε₀ := lt_min heg (lt_min heq het)
  have hε₀e : ε₀ ≤ min ε (1 / 2) := (min_le_left _ _).trans hege
  refine ⟨base₀, ε₀, hbase₀, hε₀, hε₀e, ?_⟩
  intro base' hbase' ε' hε' he'
  have hbg' : bg ≤ base' := (le_max_left bg (max bq (max bt bn))).trans hbase'
  have hbq' : bq ≤ base' :=
    ((le_max_left bq (max bt bn)).trans (le_max_right bg (max bq (max bt bn)))).trans hbase'
  have hbt' : bt ≤ base' :=
    ((le_max_left bt bn).trans
      ((le_max_right bq (max bt bn)).trans
        (le_max_right bg (max bq (max bt bn))))).trans hbase'
  have hbn' : bn ≤ base' :=
    ((le_max_right bt bn).trans
      ((le_max_right bq (max bt bn)).trans
        (le_max_right bg (max bq (max bt bn))))).trans hbase'
  have heg' : ε' ≤ eg := he'.trans (min_le_left _ _)
  have heq' : ε' ≤ eq := he'.trans
    ((min_le_right eg (min eq et)).trans (min_le_left eq et))
  have het' : ε' ≤ et := he'.trans
    ((min_le_right eg (min eq et)).trans (min_le_right eq et))
  have heε : ε' ≤ ε := (he'.trans hε₀e).trans (min_le_left _ _)
  have he2 : ε' ≤ 1 / 2 := (he'.trans hε₀e).trans (min_le_right _ _)
  exact close bg eg c M Mlin hc hM hMlin hlow bq eq hBq hGs d₀ hQ
    bt et htowers bn normLoss hnormalization base' ε'
    (hbase₀.trans hbase') hε' heε he2 hbg' hbq' hbt' hbn' heg' heq' het'

theorem n01_exists_ordinaryFlowAngularPositivePrefixBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ,
      base ≤ base₀ ∧ 0 < ε₀ ∧ ε₀ ≤ min ε (1 / 2) ∧
      ∀ base' : ℕ, base₀ ≤ base' →
      ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ →
      ∀ K : ℕ, ∃ dK : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ m b p, b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
        ∃ J : SmoothDirections (stateNeighborhood S C base' ε')
          (fun z => mixedDerivative 0 b (fun q => C.minusFlow z m q.1 q.2) p),
        ∀ j : ℕ, j ≤ K → 0 < j →
        ∀ z ∈ stateNeighborhood S C base' ε', ∀ v : Fin j → (AnnularState S × ℝ),
          |J.D j z v| ≤
            B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
              T.E0 (T.sample (C.cell m)) ^ B *
              oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
                base' (s + loss + dK) (z - (C.referenceState, 0)) v := by
  refine n01c_ordinaryFlowAngular_common_selection (base := base) (ε := ε)
    (n01_exists_stable_actualFlow_lowBounds hS hT hA hε hB hG hSpeed)
    (n01_exists_ordinaryFlowZeroAngularGrowth hS hT hA hε hB hG hSpeed)
    (n01_exists_stable_componentCosineSpeed_towers hS hT hA hε hB hG hE)
    (exists_stable_flowPolynomialNormalization
      (pairGrading (stateGrading S) realGrading)
      (jointStateGrading_monotone S) (jointStateGrading_hasInterpolation hS)) ?_
  intro bg eg c M Mlin hc hM hMlin hlow bq eq hBq hGs d₀ hQ
    bt et htowers bn normLoss hnormalization base' ε'
    hbase' hε' heε he2 hbg' hbq' hbt' hbn' heg' heq' het'
  obtain ⟨hB', hpos, ⟨J⟩⟩ := htowers base' hbt' ε' hε' het'
  have hSpeed' : CharacteristicSpeedTameBounds D T S C base' loss ε' :=
    characteristicSpeedTameBounds_mono hT hA.1.1 hSpeed
      hbase' le_rfl heε
  have hsubq : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C bq eq :=
    stateNeighborhood_subset hbq' heq'
  have hgeometry :
      ∀ N, ∀ u : OrdinaryFlowVariationInput D S C base' ε' N, ∀ t : ℝ,
        (∀ θ, c ≤ deriv
          (ordinaryFlowFiniteAngle u.component u.state u.mem u.plot t) θ) ∧
        u.defectNorm hS hT hA hB' hpos 3 t ≤ M := by
    intro N u t
    have hh := hlow base' hbg' ε' hε' heg' hB' hpos
      u.component u.tower u.dimension u.state u.mem u.plot
    exact ⟨hh.1 t, hh.2.1 t⟩
  have hlinear :
      ∀ n, ∀ u : OrdinaryFlowVariationInput D S C base' ε' (n + 1),
        (u.data hS hT hA hB' hpos).coefficientSize 1 ≤ Mlin := by
    intro n u
    exact (hlow base' hbg' ε' hε' heg' hB' hpos
      u.component u.tower u.dimension u.state u.mem u.plot).2.2 n u.directions
  have horders := n01_ordinaryFlowAngularOrderBounds_of_actual_lowGeometry
    hS hT hA hε' hB' hpos hE hSpeed' he2 (hnormalization base' hbn')
    hBq hGs hQ hsubq c M Mlin hc hM.le hgeometry hlinear
  exact n01_ordinaryFlowAngularPositivePrefixBounds_of_orders
    hS hT hA hB' hpos hE J horders

end ContinuousFlexibility.Blueprint
