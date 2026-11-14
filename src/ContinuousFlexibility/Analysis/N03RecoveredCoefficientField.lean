module

public import ContinuousFlexibility.Analysis.CoefficientProbeRecoveredCoefficients
public import ContinuousFlexibility.Analysis.N03CanonicalCoefficientProbes

/-!
# The actual N03 coefficients have one common smooth representative

The representative uses only the original coefficient field and the
decoded source errors of four fixed height probes. Each closed effective
field agrees with it by genuine off-axis division and continuity. The
already proved full-cut faithfulness then identifies the stored field on
the entire fixed negative component, including every cut-axis point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n03ProbeRecoveredCoefficients (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (χ : ℝ → ℝ) (ηr ηc ηrc ηcc : HeightPair S)
    (z : AnnularState S × ℝ) : SymmetricCoefficients :=
  coefficientProbeRecoveredCoefficients (originalCoefficients D S C z)
    (n03CoefficientCrossField S R L χ ηr ηc ηrc z)
    (n03CoefficientSquareField S R L χ ηc ηcc z)

theorem n03ProbeRecoveredCoefficients_contDiffAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (ηr ηc ηrc ηcc : HeightPair S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    let B := n03ProbeRecoveredCoefficients D S C R L χ ηr ηc ηrc ηcc z
    ContDiffAt ℝ ∞ B.a p ∧ ContDiffAt ℝ ∞ B.b p ∧ ContDiffAt ℝ ∞ B.c p := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have ha : ContDiffAt ℝ ∞ (originalCoefficients D S C z).a p :=
    (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 0).contDiffAt
      (hU.mem_nhds hp)
  have hb : ContDiffAt ℝ ∞ (originalCoefficients D S C z).b p :=
    (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 1).contDiffAt
      (hU.mem_nhds hp)
  have hc : ContDiffAt ℝ ∞ (originalCoefficients D S C z).c p :=
    (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 2).contDiffAt
      (hU.mem_nhds hp)
  exact coefficientProbeRecoveredCoefficients_contDiffAt
    (n03CoefficientCrossField_regular hT hS R L hχ ηr ηc ηrc z)
    (n03CoefficientSquareField_regular hT hS R L hχ ηc ηcc z) ha hb hc

section Actual

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hN01 : N01Properties D T S C base loss ε)
  (hN02 : N02Properties D T S C R base ε)
  (hN03 : N03Properties D T S C R L base ε)
  (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ)
  {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
  (hone : ∀ r ∈ Ioo (C.left m) (C.right m), χ r = 1)
  {ηr ηc ηrc ηcc : HeightPair S}
  (hηr : heightPairField S ηr = radialLinearProbe χ)
  (hηc : heightPairField S ηc = radialCosineProbe χ)
  (hηrc : heightPairField S ηrc = fun q => radialLinearProbe χ q * radialCosineProbe χ q)
  (hηcc : heightPairField S ηcc = fun q => radialCosineProbe χ q * radialCosineProbe χ q)

include hS hT hN01 hN02 hN03 hA hB hz hs hone hχ hηr hηc hηrc hηcc

/-- One common smooth field agrees with both genuinely closed effective
fields. The comparison includes root circles and cut axes. -/
theorem n03ProbeRecoveredCoefficients_eq_closed
    (side : Bool) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K z (if side then (K.cutPair m).2 else (K.cutPair m).1))
    (hpAnn : p ∈ annularOpen D) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let A := n03ProbeRecoveredCoefficients D S C R L χ ηr ηc ηrc ηcc z
    let B := negativeCanonicalClosedCoefficients S K z i
    A.a p = B.a p ∧ A.b p = B.b p ∧ A.c p = B.c p := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let B := negativeCanonicalClosedCoefficients S K z i
  have hi : K.positive i = false := by
    cases side
    · exact (hB.1.1 m).1
    · exact (hB.1.1 m).2.1
  have hU := (hA.domains z hz hs i).1
  have hsub : physicalPieceOpen S K z i ⊆ annularOpen D :=
    (hA.domains z hz hs i).2.2.1
  have hUJ (q : PolarPoint) (hq : q ∈ physicalPieceOpen S K z i) :
      q.1 ∈ Ioo (C.left m) (C.right m) := by
    have hqU : q ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
        physicalPieceOpen S K z (K.cutPair m).2 := by
      cases side
      · exact Or.inl hq
      · exact Or.inr hq
    rw [(hB.1.2 z hz hs m).2.2.2.1] at hqU
    exact hqU.1.1
  have hzero (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :=
    n03CoefficientProbe_axis_values hS hT hN01 hN03 hA hB hz hs m
      hχ hone hηr hηc hηrc hηcc hN02 hr
  have hob : ContDiffOn ℝ ∞ (originalCoefficients D S C z).b (annularOpen D) :=
    contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 1
  have hoc : ContDiffOn ℝ ∞ (originalCoefficients D S C z).c (annularOpen D) :=
    contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 2
  have he := coefficientProbeRecoveredCoefficients_eq_on_open
    (A := originalCoefficients D S C z) (B := B)
    (cross := n03CoefficientCrossField S R L χ ηr ηc ηrc z)
    (square := n03CoefficientSquareField S R L χ ηc ηcc z)
    (n03CoefficientCrossField_regular hT hS R L hχ ηr ηc ηrc z)
    (n03CoefficientSquareField_regular hT hS R L hχ ηc ηcc z)
    hU isOpen_Ioo hUJ (fun r hr => (hzero r hr).1) (fun r hr => (hzero r hr).2)
    (hob.continuousOn.mono hsub) (hoc.continuousOn.mono hsub)
    (fun q hq => (negativeCanonicalClosedCoefficients_contDiffAt hA hz hs i
      (subset_closure hq)).2.1.continuousAt.continuousWithinAt)
    (fun q hq => (negativeCanonicalClosedCoefficients_contDiffAt hA hz hs i
      (subset_closure hq)).2.2.continuousAt.continuousWithinAt)
    (fun q hq => n03CoefficientProbe_closed_identities hS hT hN01 hN03 hA hB hz hs m
      hχ hone hηr hηc hηrc hηcc side (subset_closure hq) (hsub hq))
  have hAp := n03ProbeRecoveredCoefficients_contDiffAt (R := R) (L := L)
    hS hT hN01 hz hs hχ ηr ηc ηrc ηcc hpAnn
  have hBp := negativeCanonicalClosedCoefficients_contDiffAt hA hz hs i hp
  refine ⟨?_, ?_, ?_⟩
  · exact (negativeCanonicalClosedCoefficients_radial_eq_original_on_closure
      hS hT hN01 hN03 hA hB hz hs i hi hp hpAnn).symm
  · exact scalar_eq_at_closure_of_continuousAt hp hAp.2.1.continuousAt
      hBp.2.1.continuousAt (fun q hq => (he q hq).1)
  · exact scalar_eq_at_closure_of_continuousAt hp hAp.2.2.continuousAt
      hBp.2.2.continuousAt (fun q hq => (he q hq).2)

/-- This equality concerns the actual stored values everywhere in the
fixed component; cut-axis values use the real trajectory argument. -/
theorem n03ProbeRecoveredCoefficients_eq_stored
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let A := n03ProbeRecoveredCoefficients D S C R L χ ηr ηc ηrc ηcc z
    A.a p = (L.coefficients z).a p ∧ A.b p = (L.coefficients z).b p ∧
      A.c p = (L.coefficients z).c p := by
  have hbounds := hN01.2.2.2.1.1 m
  have hpAnn : p ∈ annularOpen D :=
    ⟨⟨hbounds.1.trans hp.1.1, hp.1.2.trans hbounds.2.2⟩, mem_univ _⟩
  have hfinish (side : Bool)
      (hclosed : p ∈ physicalPieceClosed S K z (if side then (K.cutPair m).2 else (K.cutPair m).1))
      (hfaith : (L.coefficients z).a p = (negativeCanonicalClosedCoefficients S K z
          (if side then (K.cutPair m).2 else (K.cutPair m).1)).a p ∧
        (L.coefficients z).b p = (negativeCanonicalClosedCoefficients S K z
          (if side then (K.cutPair m).2 else (K.cutPair m).1)).b p ∧
        (L.coefficients z).c p = (negativeCanonicalClosedCoefficients S K z
          (if side then (K.cutPair m).2 else (K.cutPair m).1)).c p) :
      (n03ProbeRecoveredCoefficients D S C R L χ ηr ηc ηrc ηcc z).a p =
          (L.coefficients z).a p ∧
        (n03ProbeRecoveredCoefficients D S C R L χ ηr ηc ηrc ηcc z).b p =
          (L.coefficients z).b p ∧
        (n03ProbeRecoveredCoefficients D S C R L χ ηr ηc ηrc ηcc z).c p =
          (L.coefficients z).c p := by
    have he := n03ProbeRecoveredCoefficients_eq_closed hS hT hN01 hN02 hN03 hA hB hz hs m
      hχ hone hηr hηc hηrc hηcc side hclosed hpAnn
    exact ⟨he.1.trans hfaith.1.symm, he.2.1.trans hfaith.2.1.symm,
      he.2.2.trans hfaith.2.2.symm⟩
  by_cases hcut : p ∈ Set.range (canonicalCutPoint S K z m)
  · obtain ⟨θ, rfl⟩ := hcut
    exact hfinish false (canonicalCut_closed_and_chart hA hB hz hs m false θ).1
      (negativeCutPair_coefficients_eq_closed_on_cut
        hS hT hN01 hN02 hN03 hA hB hz hs m false θ)
  · have hwhere : p ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
        physicalPieceOpen S K z (K.cutPair m).2 := by
      rw [(hB.1.2 z hz hs m).2.2.2.1]
      exact ⟨hp, hcut⟩
    have hopen (side : Bool)
        (hq : p ∈ physicalPieceOpen S K z (if side then (K.cutPair m).2 else (K.cutPair m).1)) :=
      hfinish side (subset_closure hq)
        (negativeCutPair_coefficients_eq_closed hS hT hN01 hN03 hA hB hz hs m side p hq)
    exact hwhere.elim (hopen false) (hopen true)

theorem n03_storedCoefficients_contDiffAt_negativeComponent
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    ContDiffAt ℝ ∞ (L.coefficients z).a p ∧ ContDiffAt ℝ ∞ (L.coefficients z).b p ∧
      ContDiffAt ℝ ∞ (L.coefficients z).c p := by
  let A := n03ProbeRecoveredCoefficients D S C R L χ ηr ηc ηrc ηcc z
  have hbounds := hN01.2.2.2.1.1 m
  have hpAnn : p ∈ annularOpen D :=
    ⟨⟨hbounds.1.trans hp.1.1, hp.1.2.trans hbounds.2.2⟩, mem_univ _⟩
  have hregular := n03ProbeRecoveredCoefficients_contDiffAt (R := R) (L := L)
    hS hT hN01 hz hs hχ ηr ηc ηrc ηcc hpAnn
  have he : ∀ᶠ q in 𝓝 p, (L.coefficients z).a q = A.a q ∧
      (L.coefficients z).b q = A.b q ∧ (L.coefficients z).c q = A.c q := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    have hh := n03ProbeRecoveredCoefficients_eq_stored hS hT hN01 hN02 hN03 hA hB hz hs m
      hχ hone hηr hηc hηrc hηcc hq
    exact ⟨hh.1.symm, hh.2.1.symm, hh.2.2.symm⟩
  exact ⟨hregular.1.congr_of_eventuallyEq (he.mono fun _ h => h.1),
    hregular.2.1.congr_of_eventuallyEq (he.mono fun _ h => h.2.1),
    hregular.2.2.congr_of_eventuallyEq (he.mono fun _ h => h.2.2)⟩

end Actual

end ContinuousFlexibility.Analysis
