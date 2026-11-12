import ContinuousFlexibility.Analysis.N07aClosedFirstTraces
import ContinuousFlexibility.Analysis.N07aClosedHeightRepresentation
import ContinuousFlexibility.Analysis.N07aClosedCanonicalRepresentatives

/-!
# Reference weak graph membership forces the actual closed first jets to match

The argument restricts to a compact interval strictly inside the union of
two adjacent pieces. The graph's arbitrary angular tests identify their
radial first traces; differentiating the common angular value trace gives
the other component of the first Fréchet derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open N07aClosedJets
open scoped ContDiff Topology

private theorem n07a_closedRadialJet_restrict
    {l r a b t : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ Icc l r)
    {W : PolarPoint → ℝ} (hW : ContDiffOn ℝ ∞ W (closedStrip l r))
    (ht : t ∈ Icc a b) (θ : ℝ) :
    n07aClosedRadialJet a b W (t, θ) = n07aClosedRadialJet l r W (t, θ) := by
  have hsmall := n07a_closedStrip_radial_hasDerivWithinAt
    (hW.mono (Set.prod_mono hsub Subset.rfl)) ht θ
  have hlarge := (n07a_closedStrip_radial_hasDerivWithinAt hW (hsub ht) θ).mono hsub
  exact (hsmall.derivWithin (uniqueDiffOn_Icc hab t ht)).symm.trans
    (hlarge.derivWithin (uniqueDiffOn_Icc hab t ht))

private theorem n07a_closedStrip_angular_hasDerivAt
    {l r t : ℝ} {W : PolarPoint → ℝ}
    (hW : ContDiffOn ℝ ∞ W (closedStrip l r))
    (ht : t ∈ Icc l r) (θ : ℝ) :
    HasDerivAt (fun s => W (t, s))
      (fderivWithin ℝ W (closedStrip l r) (t, θ) (0, 1)) θ := by
  have hd := (hW.differentiableOn (by simp) (t, θ) ⟨ht, mem_univ θ⟩).hasFDerivWithinAt
  have hs : HasDerivAt (fun s : ℝ => (t, s)) (0, 1) θ :=
    (hasDerivAt_const θ t).prodMk (hasDerivAt_id' θ)
  exact hd.comp_hasDerivAt θ hs (Eventually.of_forall fun s => ⟨ht, mem_univ s⟩)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- Every actual adjacent pair has equal value and first physical jets.
The only equation premise is membership of the original reference graph. -/
theorem n07a_referenceRepresentation_adjacent_firstJets
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
    (i j : ℕ) (hboundary : K.physicalRight i = K.physicalLeft j) :
    ∀ θ : ℝ,
      n07aClosedReferenceHeight S C K U.2.1 i (J i) (K.physicalRight i, θ) =
        n07aClosedReferenceHeight S C K U.2.1 j (J j) (K.physicalRight i, θ) ∧
      fderivWithin ℝ (n07aClosedReferenceHeight S C K U.2.1 i (J i))
          (closedStrip (K.physicalLeft i) (K.physicalRight i)) (K.physicalRight i, θ) =
        fderivWithin ℝ (n07aClosedReferenceHeight S C K U.2.1 j (J j))
          (closedStrip (K.physicalLeft j) (K.physicalRight j)) (K.physicalRight i, θ) := by
  let c := K.physicalRight i
  let l := (K.physicalLeft i + c) / 2
  let r := (c + K.physicalRight j) / 2
  let WL := n07aClosedReferenceHeight S C K U.2.1 i (J i)
  let WR := n07aClosedReferenceHeight S C K U.2.1 j (J j)
  have hi := (h04.1.referenceBounds i).1
  have hj : c < K.physicalRight j := by
    dsimp only [c]
    rw [hboundary]
    exact (h04.1.referenceBounds j).1
  have hil : K.physicalLeft i < l := by dsimp only [l, c]; linarith
  have hlc : l < c := by dsimp only [l, c]; linarith
  have hcr : c < r := by dsimp only [r]; linarith
  have hrj : r < K.physicalRight j := by dsimp only [r]; linarith
  have hleft : Icc l c ⊆ Icc (K.physicalLeft i) (K.physicalRight i) :=
    fun _ hp => ⟨hil.le.trans hp.1, hp.2⟩
  have hright : Icc c r ⊆ Icc (K.physicalLeft j) (K.physicalRight j) := by
    intro x hx
    exact ⟨by simpa only [c, hboundary] using hx.1, hx.2.trans hrj.le⟩
  have hleftOpen : Ioo l c ⊆ Ioo (K.physicalLeft i) (K.physicalRight i) :=
    fun _ hp => ⟨hil.trans hp.1, hp.2⟩
  have hrightOpen : Ioo c r ⊆ Ioo (K.physicalLeft j) (K.physicalRight j) := by
    intro x hx
    exact ⟨by simpa only [c, hboundary] using hx.1, hx.2.trans hrj⟩
  have hsub : Icc l r ⊆ radialCore D := by
    have hal := ((h04.1.referenceBounds i).2.2 ⟨hil, hlc⟩).1
    have hrb := ((h04.1.referenceBounds j).2.2
      ⟨by simpa only [c, hboundary] using hcr, hrj⟩).2
    exact fun _ hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩
  have hWLi : ContDiffOn ℝ ∞ WL
      (closedStrip (K.physicalLeft i) (K.physicalRight i)) :=
    n07aClosedReferenceHeight_contDiffOn hS h04 href hsref U.2.1 i (J i)
  have hWRj : ContDiffOn ℝ ∞ WR
      (closedStrip (K.physicalLeft j) (K.physicalRight j)) :=
    n07aClosedReferenceHeight_contDiffOn hS h04 href hsref U.2.1 j (J j)
  have hWL := hWLi.mono (Set.prod_mono hleft Subset.rfl)
  have hWR := hWRj.mono (Set.prod_mono hright Subset.rfl)
  have hηp : Function.Periodic η (0, Real.pi) := hgraph.1.choose_spec.2.2.1
  have hUL := ae_restrict_of_ae_restrict_of_subset
    (Set.prod_mono hleftOpen Subset.rfl)
    (n07aClosedReferenceHeight_ae h04 href hsref hrep hηp i (hv i) (hvp i) (J i))
  have hUR := ae_restrict_of_ae_restrict_of_subset
    (Set.prod_mono hrightOpen Subset.rfl)
    (n07aClosedReferenceHeight_ae h04 href hsref hrep hηp j (hv j) (hvp j) (J j))
  have hmatch := n07a_referenceGraph_firstTraces_of_closedSmooth hD hborder hgraph
    hlc hcr hsub hWL hWR
    (fun p hp => n07aClosedReferenceHeight_periodic h04 href hsref U.2.1 i (hvp i) (J i)
      p ⟨hleft hp.1, hp.2⟩)
    (fun p hp => n07aClosedReferenceHeight_periodic h04 href hsref U.2.1 j (hvp j) (J j)
      p ⟨hright hp.1, hp.2⟩) hUL hUR
  intro θ
  have hLc : c ∈ Icc (K.physicalLeft i) (K.physicalRight i) := ⟨hi.le, le_rfl⟩
  have hRc : c ∈ Icc (K.physicalLeft j) (K.physicalRight j) := by
    simpa only [c, hboundary] using
      (show K.physicalLeft j ∈ Icc (K.physicalLeft j) (K.physicalRight j) from
        ⟨le_rfl, (h04.1.referenceBounds j).1.le⟩)
  have hnormal : n07aClosedRadialJet (K.physicalLeft i) (K.physicalRight i) WL (c, θ) =
      n07aClosedRadialJet (K.physicalLeft j) (K.physicalRight j) WR (c, θ) :=
    (n07a_closedRadialJet_restrict hlc hleft hWLi ⟨hlc.le, le_rfl⟩ θ).symm.trans
      ((hmatch.2 θ).trans
        (n07a_closedRadialJet_restrict hcr hright hWRj ⟨le_rfl, hcr.le⟩ θ))
  have he : (fun θ => WL (c, θ)) = (fun θ => WR (c, θ)) := funext hmatch.1
  have hangular :
      fderivWithin ℝ WL (closedStrip (K.physicalLeft i) (K.physicalRight i)) (c, θ) (0, 1) =
      fderivWithin ℝ WR (closedStrip (K.physicalLeft j) (K.physicalRight j)) (c, θ) (0, 1) :=
    (n07a_closedStrip_angular_hasDerivAt hWLi hLc θ).deriv.symm.trans
      ((congrArg (fun g : ℝ → ℝ => deriv g θ) he).trans
        (n07a_closedStrip_angular_hasDerivAt hWRj hRc θ).deriv)
  refine ⟨hmatch.1 θ, ?_⟩
  change fderivWithin ℝ WL (closedStrip (K.physicalLeft i) (K.physicalRight i)) (c, θ) =
    fderivWithin ℝ WR (closedStrip (K.physicalLeft j) (K.physicalRight j)) (c, θ)
  change fderivWithin ℝ WL (closedStrip (K.physicalLeft i) (K.physicalRight i)) (c, θ) (1, 0) =
    fderivWithin ℝ WR (closedStrip (K.physicalLeft j) (K.physicalRight j)) (c, θ) (1, 0)
      at hnormal
  rw [scalarCLM_eq_gradient
      (fderivWithin ℝ WL (closedStrip (K.physicalLeft i) (K.physicalRight i)) (c, θ)),
    scalarCLM_eq_gradient
      (fderivWithin ℝ WR (closedStrip (K.physicalLeft j) (K.physicalRight j)) (c, θ)),
    hnormal, hangular]

end ContinuousFlexibility.Analysis
