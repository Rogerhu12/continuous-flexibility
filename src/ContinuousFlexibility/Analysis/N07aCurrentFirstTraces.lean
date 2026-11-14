module

public import ContinuousFlexibility.Analysis.N07aClosedHeightFirstJet
public import ContinuousFlexibility.Analysis.N07aCurrentCutMeasure

/-!
# The original reference graph determines current first traces

The common reference cutoff is removed from both value and differential.
The source-independent primitive transport then carries these two genuine
traces to the actual moving cut. No trace of a solution is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open N07aClosedJets
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07aClosedReferenceHeight_firstJet
    (hS : IsPhysicalSpaces D T S)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (aL : ℝ) (m : ℕ) {v : PolarPoint → ℝ}
    (J : ClosedJetTower (K.left m) (K.right m) v)
    {p : PolarPoint} (hp : p ∈ closedStrip (K.physicalLeft m) (K.physicalRight m)) :
    fderivWithin ℝ (n07aClosedReferenceHeight S C K aL m J)
        (closedStrip (K.physicalLeft m) (K.physicalRight m)) p =
      n07aClosedPhysicalHeightGradient K (C.referenceState, 0) m J p +
        fderiv ℝ (fun x : PolarPoint => aL * S.chiLeft x.1) p := by
  have hp' : p ∈ physicalPieceClosed S K (C.referenceState, 0) m := by
    rwa [n07a_referencePhysicalPieceClosed h04 m]
  have hd := n07aClosedPhysicalHeight_hasFDerivWithinAt h04 href hsref m J hp'
  rw [n07a_referencePhysicalPieceClosed h04 m] at hd
  have hχ : ContDiff ℝ ∞ (fun x : PolarPoint => aL * S.chiLeft x.1) :=
    contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)
  exact (hd.add ((hχ.differentiable (by simp) p).hasFDerivAt.hasFDerivWithinAt)).fderivWithin
    (((uniqueDiffOn_Icc (h04.1.referenceBounds m).1).prod uniqueDiffOn_univ) p hp)

/-- The common physical scalar column contributes the same first jet on
both reference sides and cancels before transport. -/
theorem n07a_referenceRepresentation_remainder_firstJets
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    (hborder : RadialTrueBorder D)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K (C.referenceState, 0) U F η f)
    {γ M₀ M₁ : ℝ} {G : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ (η, U.2.2.1) G)
    {v : ℕ → PolarPoint → ℝ}
    (hv : ∀ m, (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] v m)
    (hvp : ∀ m, Function.Periodic (v m) (0, Real.pi))
    (J : ∀ m, ClosedJetTower (K.left m) (K.right m) (v m))
    (i j : ℕ) (hboundary : K.physicalRight i = K.physicalLeft j)
    (θ : ℝ) :
    n07aClosedPhysicalHeight K (C.referenceState, 0) i (J i) (K.physicalRight i, θ) =
        n07aClosedPhysicalHeight K (C.referenceState, 0) j (J j) (K.physicalRight i, θ) ∧
      n07aClosedPhysicalHeightGradient K (C.referenceState, 0) i (J i)
          (K.physicalRight i, θ) =
        n07aClosedPhysicalHeightGradient K (C.referenceState, 0) j (J j)
          (K.physicalRight i, θ) := by
  have hm := n07a_referenceRepresentation_adjacent_firstJets hD hS hborder h04
    href hsref hrep hgraph hv hvp J i j hboundary θ
  have hpi : (K.physicalRight i, θ) ∈
      closedStrip (K.physicalLeft i) (K.physicalRight i) :=
    ⟨⟨(h04.1.referenceBounds i).1.le, le_rfl⟩, mem_univ _⟩
  have hpj : (K.physicalRight i, θ) ∈
      closedStrip (K.physicalLeft j) (K.physicalRight j) := by
    rw [hboundary]
    exact ⟨⟨le_rfl, (h04.1.referenceBounds j).1.le⟩, mem_univ _⟩
  refine ⟨add_right_cancel hm.1, ?_⟩
  rw [n07aClosedReferenceHeight_firstJet hS h04 href hsref U.2.1 i (J i) hpi,
    n07aClosedReferenceHeight_firstJet hS h04 href hsref U.2.1 j (J j) hpj] at hm
  exact add_right_cancel hm.2

/-- The true current cut has matching remainder value and full first
covector, derived from the original reference weak graph. -/
theorem n07a_currentRepresentation_cut_firstJets
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    (hborder : RadialTrueBorder D)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K (C.referenceState, 0) U F η f)
    {γ M₀ M₁ : ℝ} {G : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ (η, U.2.2.1) G)
    {v : ℕ → PolarPoint → ℝ}
    (hv : ∀ m, (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] v m)
    (hvp : ∀ m, Function.Periodic (v m) (0, Real.pi))
    (J : ∀ m, ClosedJetTower (K.left m) (K.right m) (v m))
    (k : ℕ) (θ : ℝ) :
    n07aClosedPhysicalHeight K z (K.cutPair k).1 (J (K.cutPair k).1)
        (canonicalCutPoint S K z k θ) =
      n07aClosedPhysicalHeight K z (K.cutPair k).2 (J (K.cutPair k).2)
        (canonicalCutPoint S K z k θ) ∧
    n07aClosedPhysicalHeightGradient K z (K.cutPair k).1 (J (K.cutPair k).1)
        (canonicalCutPoint S K z k θ) =
      n07aClosedPhysicalHeightGradient K z (K.cutPair k).2 (J (K.cutPair k).2)
        (canonicalCutPoint S K z k θ) := by
  let i := (K.cutPair k).1
  let j := (K.cutPair k).2
  let p := canonicalCutPoint S K (C.referenceState, 0) k θ
  obtain ⟨_, _, _, _, hij, hR, hli, _, hri, _⟩ := h04.2.1.1.1 k
  have hpclosed := n07a_currentCutPoint_mem_closed h04 href hsref k θ
  have hpi : p ∈ closedStrip (K.physicalLeft i) (K.physicalRight i) := by
    rw [← n07a_referencePhysicalPieceClosed h04 i]
    exact hpclosed.1
  have hpj : p ∈ closedStrip (K.physicalLeft j) (K.physicalRight j) := by
    rw [← n07a_referencePhysicalPieceClosed h04 j]
    exact hpclosed.2
  have hrad : p.1 = K.physicalRight i :=
    le_antisymm hpi.1.2 (by simpa only [i, j, hij] using hpj.1.1)
  have hpoint : p = (K.physicalRight i, p.2) := Prod.ext hrad rfl
  have hmid : K.physicalRight i < K.physicalRight j := by
    rw [show K.physicalRight i = K.physicalLeft j from hij]
    exact (h04.1.referenceBounds j).1
  have hpD : p ∈ annularOpen D := by
    have hl := (h04.1.referenceBounds i).1
    have ha := ((h04.1.referenceBounds i).2.2
      (show (K.physicalLeft i + K.physicalRight i) / 2 ∈
        Ioo (K.physicalLeft i) (K.physicalRight i) by constructor <;> linarith)).1
    have hb := ((h04.1.referenceBounds j).2.2
      (show (K.physicalRight i + K.physicalRight j) / 2 ∈
        Ioo (K.physicalLeft j) (K.physicalRight j) by
          rw [← show K.physicalRight i = K.physicalLeft j from hij]
          constructor <;> linarith)).2
    exact ⟨by rw [hrad]; constructor <;> linarith, mem_univ _⟩
  have hmatch := n07a_referenceRepresentation_remainder_firstJets hD hS hborder h04
    href hsref hrep hgraph hv hvp J i j hij p.2
  rw [← hpoint] at hmatch
  obtain ⟨τ, q, hτ, hq, _, _, _, _, _, hpiece, _⟩ := hcanonical.transport z hz hs
  have hcur := n07aClosedPhysicalHeight_current_firstJets h04 href hsref hz hs
    hτ hq hpiece i j (J i) (J j) hpclosed.1 hpclosed.2 hpD hmatch.1 hmatch.2
  have hcanonicalPoint : (K.cutRadius k, θ) ∈ canonicalClosed S K i := by
    exact ⟨⟨by simpa only [i, hli] using hR.le, by simpa only [i, hri] using
        (le_rfl : K.cutRadius k ≤ K.cutRadius k)⟩, mem_univ _⟩
  have hFp := (h04.1.boundary (C.referenceState, 0) href hsref i).2.2.2.1
    (K.cutRadius k, θ) hcanonicalPoint
  have hτp := (n07a_primitiveTransport_closed_firstJet h04 href hsref hz hs
    hτ hq hpiece i hpclosed.1 hpD).1.1
  change τ p = K.inverseChart z i (K.chart (C.referenceState, 0) i p) at hτp
  change K.chart (C.referenceState, 0) i p = (K.cutRadius k, θ) at hFp
  rw [hFp] at hτp
  change τ (canonicalCutPoint S K (C.referenceState, 0) k θ) =
    canonicalCutPoint S K z k θ at hτp
  rw [hτp] at hcur
  exact hcur

end ContinuousFlexibility.Analysis
