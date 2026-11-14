module

public import ContinuousFlexibility.Analysis.CoefficientProbeFieldRegularity
public import ContinuousFlexibility.Analysis.CanonicalCutFullFaithfulness

/-!
# Common smooth numerators for the actual corrected coefficients

One fixed radial cutoff and four genuine height probes give globally
smooth numerator fields. Their identities on each open canonical half
extend to its closure by actual continuity. The stored coefficients are
then identified on the whole negative component, including the cut axes.
Consequently the fixed two-axis normalization leaves every actual local
jet unchanged on that common physical component.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n03CoefficientCrossField (S : PhysicalSpacesData) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (χ : ℝ → ℝ) (ηr ηc ηrc : HeightPair S)
    (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  coefficientErrorCrossNumerator χ
    (decodedCorrectionError S L z (R.residual z) ηr)
    (decodedCorrectionError S L z (R.residual z) ηc)
    (decodedCorrectionError S L z (R.residual z) ηrc)

def n03CoefficientSquareField (S : PhysicalSpacesData) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (χ : ℝ → ℝ) (ηc ηcc : HeightPair S)
    (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  coefficientErrorSquareNumerator χ
    (decodedCorrectionError S L z (R.residual z) ηc)
    (decodedCorrectionError S L z (R.residual z) ηcc)

theorem n03CoefficientCrossField_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (R : ReturnEquationData S) (L : ReturnCorrectionData S)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (ηr ηc ηrc : HeightPair S)
    (z : AnnularState S × ℝ) :
    CoefficientProbeFieldRegularity D (n03CoefficientCrossField S R L χ ηr ηc ηrc z) :=
  coefficientErrorCrossNumerator_fieldRegularity hχ
    (decodedCorrectionError_fieldRegularity hT hS L z (R.residual z) ηr)
    (decodedCorrectionError_fieldRegularity hT hS L z (R.residual z) ηc)
    (decodedCorrectionError_fieldRegularity hT hS L z (R.residual z) ηrc)

theorem n03CoefficientSquareField_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (R : ReturnEquationData S) (L : ReturnCorrectionData S)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (ηc ηcc : HeightPair S)
    (z : AnnularState S × ℝ) :
    CoefficientProbeFieldRegularity D (n03CoefficientSquareField S R L χ ηc ηcc z) :=
  coefficientErrorSquareNumerator_fieldRegularity hχ
    (decodedCorrectionError_fieldRegularity hT hS L z (R.residual z) ηc)
    (decodedCorrectionError_fieldRegularity hT hS L z (R.residual z) ηcc)

section Actual

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hN01 : N01Properties D T S C base loss ε)
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

include hS hT hN01 hN03 hA hB hz hs hone hχ hηr hηc hηrc hηcc

/-- The true probe identities extend to the closed halves without
requiring stored operator derivatives on the cut. -/
theorem n03CoefficientProbe_closed_identities
    (side : Bool) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K z (if side then (K.cutPair m).2 else (K.cutPair m).1))
    (hpAnn : p ∈ annularOpen D) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    n03CoefficientCrossField S R L χ ηr ηc ηrc z p =
        -4 * ((originalCoefficients D S C z).b p -
          (negativeCanonicalClosedCoefficients S K z i).b p) * Real.sin (2 * p.2) ∧
      n03CoefficientSquareField S R L χ ηc ηcc z p =
        8 * ((originalCoefficients D S C z).c p -
          (negativeCanonicalClosedCoefficients S K z i).c p) * Real.sin (2 * p.2) ^ 2 := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let B := negativeCanonicalClosedCoefficients S K z i
  have hi : K.positive i = false := by
    cases side
    · exact (hB.1.1 m).1
    · exact (hB.1.1 m).2.1
  have hoa : ContDiffOn ℝ ∞ (originalCoefficients D S C z).a (annularOpen D) :=
    contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 0
  have hob : ContDiffOn ℝ ∞ (originalCoefficients D S C z).b (annularOpen D) :=
    contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 1
  have hoc : ContDiffOn ℝ ∞ (originalCoefficients D S C z).c (annularOpen D) :=
    contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 2
  have hAnn : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hinside (q : PolarPoint) (hq : q ∈ physicalPieceOpen S K z i) :
      n03CoefficientCrossField S R L χ ηr ηc ηrc z q =
          -4 * ((originalCoefficients D S C z).b q - B.b q) * Real.sin (2 * q.2) ∧
        n03CoefficientSquareField S R L χ ηc ηcc z q =
          8 * ((originalCoefficients D S C z).c q - B.c q) * Real.sin (2 * q.2) ^ 2 := by
    have hqU : q ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
        physicalPieceOpen S K z (K.cutPair m).2 := by
      cases side
      · exact Or.inl hq
      · exact Or.inr hq
    rw [(hB.1.2 z hz hs m).2.2.2.1] at hqU
    have hqAnn := (hA.domains z hz hs i).2.2.1 hq
    have hone' : χ =ᶠ[𝓝 q.1] (fun _ => 1) := by
      filter_upwards [isOpen_Ioo.mem_nhds hqU.1.1] with r hr
      exact hone r hr
    have hBq := negativeCanonicalClosedCoefficients_contDiffAt hA hz hs i (subset_closure hq)
    exact n03Error_coefficientProbe_identities
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      hN03 hz hs hqAnn hχ hone' hηr hηc hηrc hηcc
      (((hoa q hqAnn).contDiffAt (hAnn.mem_nhds hqAnn)).differentiableAt (by simp))
      (((hob q hqAnn).contDiffAt (hAnn.mem_nhds hqAnn)).differentiableAt (by simp))
      (((hoc q hqAnn).contDiffAt (hAnn.mem_nhds hqAnn)).differentiableAt (by simp))
      (hBq.1.differentiableAt (by simp)) (hBq.2.1.differentiableAt (by simp))
      (hBq.2.2.differentiableAt (by simp))
      (fun f hf => negativeCanonicalClosedOperator_of_parts hA hB hz hs i hi f hf.contDiffOn hq)
  have hBp := negativeCanonicalClosedCoefficients_contDiffAt hA hz hs i hp
  have hOb := (hob p hpAnn).contDiffAt (hAnn.mem_nhds hpAnn)
  have hOc := (hoc p hpAnn).contDiffAt (hAnn.mem_nhds hpAnn)
  have hsin : ContDiffAt ℝ ∞ (fun q : PolarPoint => Real.sin (2 * q.2)) p :=
    (contDiffAt_const.mul contDiffAt_snd).sin
  have hcross : ContDiffAt ℝ ∞
      (fun q => -4 * ((originalCoefficients D S C z).b q - B.b q) * Real.sin (2 * q.2)) p :=
    (contDiffAt_const.mul (hOb.sub hBp.2.1)).mul hsin
  have hsquare : ContDiffAt ℝ ∞
      (fun q => 8 * ((originalCoefficients D S C z).c q - B.c q) * Real.sin (2 * q.2) ^ 2) p :=
    (contDiffAt_const.mul (hOc.sub hBp.2.2)).mul (hsin.pow 2)
  exact ⟨scalar_eq_at_closure_of_continuousAt hp
      (n03CoefficientCrossField_regular hT hS R L hχ ηr ηc ηrc z).1.continuous.continuousAt
      hcross.continuousAt (fun q hq => (hinside q hq).1),
    scalar_eq_at_closure_of_continuousAt hp
      (n03CoefficientSquareField_regular hT hS R L hχ ηc ηcc z).1.continuous.continuousAt
      hsquare.continuousAt (fun q hq => (hinside q hq).2)⟩

/-- One pair of smooth numerator fields represents the actual stored
coefficient differences on the entire fixed negative component. -/
theorem n03CoefficientProbe_stored_identities
    (hN02 : N02Properties D T S C R base ε) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    n03CoefficientCrossField S R L χ ηr ηc ηrc z p =
        -4 * ((originalCoefficients D S C z).b p - (L.coefficients z).b p) * Real.sin (2 * p.2) ∧
      n03CoefficientSquareField S R L χ ηc ηcc z p =
        8 * ((originalCoefficients D S C z).c p - (L.coefficients z).c p) * Real.sin (2 * p.2) ^ 2 := by
  have hbounds := hN01.2.2.2.1.1 m
  have hpAnn : p ∈ annularOpen D :=
    ⟨⟨hbounds.1.trans hp.1.1, hp.1.2.trans hbounds.2.2⟩, mem_univ _⟩
  have hfinish (side : Bool)
      (hclosed : p ∈ physicalPieceClosed S K z (if side then (K.cutPair m).2 else (K.cutPair m).1))
      (hb : (L.coefficients z).b p = (negativeCanonicalClosedCoefficients S K z
        (if side then (K.cutPair m).2 else (K.cutPair m).1)).b p)
      (hc : (L.coefficients z).c p = (negativeCanonicalClosedCoefficients S K z
        (if side then (K.cutPair m).2 else (K.cutPair m).1)).c p) :
      n03CoefficientCrossField S R L χ ηr ηc ηrc z p =
          -4 * ((originalCoefficients D S C z).b p - (L.coefficients z).b p) * Real.sin (2 * p.2) ∧
        n03CoefficientSquareField S R L χ ηc ηcc z p =
          8 * ((originalCoefficients D S C z).c p - (L.coefficients z).c p) * Real.sin (2 * p.2) ^ 2 := by
    have h := n03CoefficientProbe_closed_identities hS hT hN01 hN03 hA hB hz hs m
      hχ hone hηr hηc hηrc hηcc side hclosed hpAnn
    dsimp only at h
    rw [← hb, ← hc] at h
    exact h
  by_cases hcut : p ∈ Set.range (canonicalCutPoint S K z m)
  · obtain ⟨θ, rfl⟩ := hcut
    have hf := negativeCutPair_coefficients_eq_closed_on_cut
      hS hT hN01 hN02 hN03 hA hB hz hs m false θ
    exact hfinish false (canonicalCut_closed_and_chart hA hB hz hs m false θ).1 hf.2.1 hf.2.2
  · have hwhere : p ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
        physicalPieceOpen S K z (K.cutPair m).2 := by
      rw [(hB.1.2 z hz hs m).2.2.2.1]
      exact ⟨hp, hcut⟩
    have hopen (side : Bool)
        (hq : p ∈ physicalPieceOpen S K z (if side then (K.cutPair m).2 else (K.cutPair m).1)) := by
      have hf := negativeCutPair_coefficients_eq_closed hS hT hN01 hN03 hA hB hz hs m side p hq
      exact hfinish side (subset_closure hq) hf.2.1 hf.2.2
    exact hwhere.elim (hopen false) (hopen true)

theorem n03CoefficientProbe_axis_values
    (hN02 : N02Properties D T S C R base ε) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    (n03CoefficientCrossField S R L χ ηr ηc ηrc z (r, 0) = 0 ∧
      n03CoefficientCrossField S R L χ ηr ηc ηrc z (r, Real.pi / 2) = 0) ∧
    (n03CoefficientSquareField S R L χ ηc ηcc z (r, 0) = 0 ∧
      n03CoefficientSquareField S R L χ ηc ηcc z (r, Real.pi / 2) = 0) := by
  have h0 := n03CoefficientProbe_stored_identities hS hT hN01 hN03 hA hB hz hs m
    hχ hone hηr hηc hηrc hηcc hN02 (p := (r, 0)) ⟨hr, mem_univ _⟩
  have hhalf := n03CoefficientProbe_stored_identities hS hT hN01 hN03 hA hB hz hs m
    hχ hone hηr hηc hηrc hηcc hN02 (p := (r, Real.pi / 2)) ⟨hr, mem_univ _⟩
  simp only [mul_zero, Real.sin_zero, show 2 * (Real.pi / 2) = Real.pi by ring,
    Real.sin_pi, zero_pow two_ne_zero] at h0 hhalf
  exact ⟨⟨h0.1, hhalf.1⟩, h0.2, hhalf.2⟩

theorem n03CoefficientProbe_normalized_germs
    (hN02 : N02Properties D T S C R base ε) {p : PolarPoint}
    (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    coefficientAxisNormalize (n03CoefficientCrossField S R L χ ηr ηc ηrc z) =ᶠ[𝓝 p]
        n03CoefficientCrossField S R L χ ηr ηc ηrc z ∧
      coefficientAxisNormalize (n03CoefficientSquareField S R L χ ηc ηcc z) =ᶠ[𝓝 p]
        n03CoefficientSquareField S R L χ ηc ηcc z := by
  have hzero (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :=
    n03CoefficientProbe_axis_values hS hT hN01 hN03 hA hB hz hs m
      hχ hone hηr hηc hηrc hηcc hN02 hr
  exact ⟨coefficientAxisNormalize_eventuallyEq isOpen_Ioo (fun r hr => (hzero r hr).1) hp,
    coefficientAxisNormalize_eventuallyEq isOpen_Ioo (fun r hr => (hzero r hr).2) hp⟩

end Actual

end ContinuousFlexibility.Analysis
