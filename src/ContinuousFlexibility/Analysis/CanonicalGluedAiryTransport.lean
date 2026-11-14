module

public import ContinuousFlexibility.Analysis.CanonicalGluedAiryFirstJets
public import ContinuousFlexibility.Analysis.CanonicalCutOffAxisFaithfulness
public import ContinuousFlexibility.Analysis.CanonicalCutOrientation
public import ContinuousFlexibility.Analysis.ReversedAiryTransport

/-!
# The genuine glued integral transports the stored characteristic field

Interior faithfulness supplies the stored coefficients on both halves.
At a non-axis cut point, the actual N03 test-germ argument supplies the
same equality. The glued ordinary derivative and the orientation of each
half then give the characteristic transport equation throughout the
component except at cut points on the reflection axes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem canonicalGluedAiryIntegral_characteristic_transport
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (haxis : p ∈ Set.range (canonicalCutPoint S K z m) → Real.sin (2 * p.2) ≠ 0) :
    radialPartial (canonicalGluedAiryIntegral S K z m σ) p =
      -((L.coefficients z).b p / (L.coefficients z).a p -
        σ * Real.sqrt ((L.coefficients z).b p ^ 2 -
          (L.coefficients z).a p * (L.coefficients z).c p) / (L.coefficients z).a p) *
        angularPartial (canonicalGluedAiryIntegral S K z m σ) p := by
  let i : Bool → ℕ := fun side => if side then (K.cutPair m).2 else (K.cutPair m).1
  let v : ℝ := (L.coefficients z).b p / (L.coefficients z).a p -
    σ * Real.sqrt ((L.coefficients z).b p ^ 2 -
      (L.coefficients z).a p * (L.coefficients z).c p) / (L.coefficients z).a p
  have hbounds := hN01.2.2.2.1.1 m
  have hpAnn : p ∈ annularOpen D :=
    ⟨⟨hbounds.1.trans hp.1.1, hp.1.2.trans hbounds.2.2⟩, mem_univ _⟩
  have hLa : 0 < (L.coefficients z).a p := by
    rw [hN03.1 z hz hs p]
    exact n01_originalRadialCoefficient_pos hN01 hz hs hpAnn
  have hsigns := canonicalCutPair_planeJacobian_signs hA hB.1 hz hs m
  have hpart (side : Bool) (hclosed : p ∈ physicalPieceClosed S K z (i side))
      (hξ : 0 < (K.chart z (i side) p).1)
      (hcoeff : (L.coefficients z).a p = (negativeCanonicalClosedCoefficients S K z (i side)).a p ∧
        (L.coefficients z).b p = (negativeCanonicalClosedCoefficients S K z (i side)).b p ∧
        (L.coefficients z).c p = (negativeCanonicalClosedCoefficients S K z (i side)).c p)
      (hjet : fderiv ℝ (canonicalGluedAiryIntegral S K z m σ) p =
        fderiv ℝ (airyFirstIntegral (K.chart z (i side)) (if side then -σ else σ)) p) :
      radialPartial (canonicalGluedAiryIntegral S K z m σ) p =
        -v * angularPartial (canonicalGluedAiryIntegral S K z m σ) p := by
    have hreg := (hA.boundary z hz hs (i side)).2.2.2.2.1 p hclosed
    have hJ : if side then planeJacobian (K.chart z (i side)) p < 0 else
        0 < planeJacobian (K.chart z (i side)) p := by
      cases side with
      | false => exact hsigns.1 p hclosed
      | true => exact hsigns.2 p hclosed
    have ha : (negativeCanonicalClosedCoefficients S K z (i side)).a p ≠ 0 := by
      rw [← hcoeff.1]
      exact hLa.ne'
    have htransport := airyFirstIntegral_signed_characteristic_transport
      (F := K.chart z (i side)) (h := K.height z (i side))
      (hreg.1.differentiableAt (by simp)) side hJ hreg.2.2.2.ne' hξ ha hσ
    have hr : radialPartial (canonicalGluedAiryIntegral S K z m σ) p =
        radialPartial (airyFirstIntegral (K.chart z (i side)) (if side then -σ else σ)) p :=
      congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (1, 0)) hjet
    have hθ : angularPartial (canonicalGluedAiryIntegral S K z m σ) p =
        angularPartial (airyFirstIntegral (K.chart z (i side)) (if side then -σ else σ)) p :=
      congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (0, 1)) hjet
    rw [hr, hθ]
    dsimp only [v]
    rw [hcoeff.1, hcoeff.2.1, hcoeff.2.2]
    exact htransport
  have hopen (side : Bool) (hopen : p ∈ physicalPieceOpen S K z (i side)) :
      radialPartial (canonicalGluedAiryIntegral S K z m σ) p =
        -v * angularPartial (canonicalGluedAiryIntegral S K z m σ) p := by
    obtain ⟨_, _, _, _, _, _, hl, hr, _, _⟩ := hB.1.1 m
    have hleft : K.left (i side) = 0 := by cases side <;> assumption
    have hξ : 0 < (K.chart z (i side) p).1 := by
      simpa only [hleft] using ((hA.charts z hz hs (i side)).1 hopen).1.1
    exact hpart side (subset_closure hopen) hξ
      (negativeCutPair_coefficients_eq_closed hS hT hN01 hN03 hA hB hz hs m side p hopen)
      (canonicalGluedAiryIntegral_fderiv_on_piece hA hB hz hs m side σ hopen)
  by_cases hcut : p ∈ Set.range (canonicalCutPoint S K z m)
  · have hsin := haxis hcut
    obtain ⟨θ, hpθ⟩ := hcut
    have hp' := canonicalCut_closed_and_chart hA hB hz hs m false θ
    have hρ := (hB.1.1 m).2.2.2.2.2.1
    have hξ : 0 < (K.chart z (i false) p).1 := by
      rw [← hpθ, hp'.2]
      exact hρ
    apply hpart false (by simpa only [hpθ] using hp'.1) hξ
    · simpa only [hpθ] using negativeCutPair_coefficients_eq_closed_on_cut_of_nonaxis
        hS hT hN01 hN03 hA hB hz hs m false θ (by rw [hpθ]; exact hsin)
    · simpa only [i, Bool.false_eq_true, ite_false, hpθ] using
        canonicalGluedAiryIntegral_fderiv_on_cut hA hB hz hs m σ θ
  · have hwhere : p ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
        physicalPieceOpen S K z (K.cutPair m).2 := by
      rw [(hB.1.2 z hz hs m).2.2.2.1]
      exact ⟨hp, hcut⟩
    exact hwhere.elim (hopen false) (hopen true)

end ContinuousFlexibility.Analysis
