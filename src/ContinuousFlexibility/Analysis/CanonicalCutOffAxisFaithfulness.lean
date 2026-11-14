module

public import ContinuousFlexibility.Analysis.N03OffAxisOperatorRegularity
public import ContinuousFlexibility.Analysis.ClosureOperatorFaithfulness
public import ContinuousFlexibility.Analysis.CanonicalCutCoefficientMatching
public import ContinuousFlexibility.Analysis.NegativeCanonicalFaithfulness

/-!
# The actual stored operator is faithful on the non-axis cut

The N03 error supplies smooth actual operator outputs for all local
physical test germs off the reflection axes. The one-sided canonical
action and coefficient equality extend to the cut by genuine limits.
Thus both closed effective fields have the stored coefficient values
there. No all-domain regularity of the stored field is an extra premise.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- One side parameter covers both current negative halves. The only
excluded points are the physical reflection axes, not an arbitrary
neighborhood or a possibly infinite family of cut crossings. -/
theorem negativeCutPair_coefficients_eq_closed_on_cut_of_nonaxis
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (θ : ℝ)
    (hsin : Real.sin (2 * (canonicalCutPoint S K z m θ).2) ≠ 0) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let p := canonicalCutPoint S K z m θ
    (L.coefficients z).a p = (negativeCanonicalClosedCoefficients S K z i).a p ∧
      (L.coefficients z).b p = (negativeCanonicalClosedCoefficients S K z i).b p ∧
      (L.coefficients z).c p = (negativeCanonicalClosedCoefficients S K z i).c p := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let p := canonicalCutPoint S K z m θ
  obtain ⟨hnegL, hnegR, _, _, _, hρ, _, _, _, _⟩ := hB.1.1 m
  have hm : K.positive i = false := by cases side <;> assumption
  have hcut := canonicalCut_closed_and_chart hA hB hz hs m side θ
  have hclosed : p ∈ physicalPieceClosed S K z i := hcut.1
  have hpN : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    (hB.1.2 z hz hs m).2.1 ⟨θ, rfl⟩
  have hbounds := hN01.2.2.2.1.1 m
  have hpAnn : p ∈ annularOpen D :=
    ⟨⟨hbounds.1.trans hpN.1.1, hpN.1.2.trans hbounds.2.2⟩, mem_univ _⟩
  have hAnn : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hOriginal : ContDiffOn ℝ ∞ (originalCoefficients D S C z).a (annularOpen D) :=
    contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 0
  have hLaeq : (L.coefficients z).a = (originalCoefficients D S C z).a :=
    funext (hN03.1 z hz hs)
  have hLa : DifferentiableAt ℝ (L.coefficients z).a p := by
    rw [hLaeq]
    exact ((hOriginal p hpAnn).contDiffAt (hAnn.mem_nhds hpAnn)).differentiableAt (by simp)
  have hLa0 : (L.coefficients z).a p ≠ 0 := by
    rw [hLaeq]
    exact (n01_originalRadialCoefficient_pos hN01 hz hs hpAnn).ne'
  have hregular := negativeCanonicalClosedCoefficients_contDiffAt hA hz hs i hclosed
  have hdisc : 0 < (negativeCanonicalClosedCoefficients S K z i).b p ^ 2 -
      (negativeCanonicalClosedCoefficients S K z i).a p *
        (negativeCanonicalClosedCoefficients S K z i).c p := by
    have hh : 0 < K.height z i p :=
      ((hA.boundary z hz hs i).2.2.2.2.1 p hclosed).2.2.2
    have hξ : (K.chart z i p).1 = K.cutRadius m := congrArg Prod.fst hcut.2
    have hquot : 0 < (K.chart z i p).1 / K.height z i p ^ 4 :=
      div_pos (by rw [hξ]; exact hρ) (pow_pos hh 4)
    have he := negativeCanonicalClosedCoefficients_determinant hA hz hs i hclosed
    rw [neg_div] at he
    linarith only [he, hquot]
  apply operatorCoefficients_eq_at_closure_of_output_continuous hclosed hLa hLa0
    hregular.1 hregular.2.1 hregular.2.2 hdisc
  · intro q hq
    exact (negativeCutPair_coefficients_eq_closed hS hT hN01 hN03 hA hB
      hz hs m side q hq).2.1
  · intro u hu
    exact (n03_contDiffAt_divergenceOperator_of_nonaxis
      hS hT hN01 hN03 hz hs hpAnn hsin hu).continuousAt
  · intro u hu q hq
    exact negativeCanonicalClosedOperator_of_parts hA hB hz hs i hm u hu.contDiffOn hq

end ContinuousFlexibility.Analysis
