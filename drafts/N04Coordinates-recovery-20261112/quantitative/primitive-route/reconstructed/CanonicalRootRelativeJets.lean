import ContinuousFlexibility.Analysis.N03RootEndpointPhysicalJets
import ContinuousFlexibility.Analysis.RelativeRootJetBounds
import ContinuousFlexibility.Analysis.CanonicalRootTransportBoundary

/-!
# Actual relative root maps on one common neighborhood

The stored inverse germs and the actual zero-circle images are used at
both ends of the composition. The reference root jets are lifted from
zero state displacement. No chart, inverse chart, root, or reference
witness is replaced, and no bound on an angular lift value is requested.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem RootPhysicalFieldJetBound.from_zero
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {B : ℕ → ℝ}
    {F : PolarPoint → PolarPoint} {H : PolarPoint → ℝ} {q : PolarPoint}
    (hB : ∀ n, 0 ≤ B n) (h : RootPhysicalFieldJetBound p loss B 0 F H q) (z : E) :
    RootPhysicalFieldJetBound p loss B z F H q := by
  have hmono (n : ℕ) {v : ℝ} (hv : v ≤ B n * (1 + p (n + loss) 0)) :
      v ≤ B n * (1 + p (n + loss) z) := by
    calc
      v ≤ B n := by simpa only [map_zero, add_zero, mul_one] using hv
      _ = B n * 1 := (mul_one _).symm
      _ ≤ B n * (1 + p (n + loss) z) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (apply_nonneg _ _)) (hB n)
  exact ⟨h.1, h.2.1, h.2.2.1, fun n hn => hmono n (h.2.2.2.1 n hn),
    fun n => hmono n (h.2.2.2.2.1 n), fun n => hmono n (h.2.2.2.2.2 n)⟩

private theorem rootBetween_states_radial
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (hcut : CanonicalCutGeometry S C K base ε)
    {z₀ z₁ : AnnularState S × ℝ}
    (hz₀ : z₀ ∈ stateNeighborhood S C base ε) (hs₀ : stateSector S z₀.1)
    (hz₁ : z₁ ∈ stateNeighborhood S C base ε) (hs₁ : stateSector S z₁.1)
    (m : ℕ) (side : Bool) (θ : ℝ) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let r := n01ComponentRoot C m side
    (K.inverseChart z₁ i (K.chart z₀ i (r, θ))).1 = r := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let r := n01ComponentRoot C m side
  have hroot := canonicalCutRoot_mem_closed_and_zero hA hcut hz₀ hs₀ m side θ
  have hzero : K.inverseChart z₁ i '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
      ({r} ×ˢ (univ : Set ℝ)) := by
    cases side
    · exact (hcut.2 z₁ hz₁ hs₁ m).2.2.2.2.1
    · exact (hcut.2 z₁ hz₁ hs₁ m).2.2.2.2.2
  have hmem := mem_image_of_mem (K.inverseChart z₁ i)
    (show K.chart z₀ i (r, θ) ∈ ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) from
      ⟨hroot.2, mem_univ _⟩)
  rw [hzero] at hmem
  exact hmem.1

def CanonicalRootRelativeJetFamily
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (side : Bool) (B : ℕ → ℝ) : Prop :=
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let r := n01ComponentRoot C m side
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ θ : ℝ,
    ContDiffAt ℝ ∞ (canonicalCurrentPoint C K z i) (r, θ) ∧
      ContDiffAt ℝ ∞ (canonicalReferencePoint C K z i) (r, θ) ∧
      (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (canonicalCurrentPoint C K z i) (r, θ)‖ ≤
        B n * (1 + pairGrading (stateGrading S) realGrading (n + loss)
          (z - (C.referenceState, 0)))) ∧
      ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (canonicalReferencePoint C K z i) (r, θ)‖ ≤
        B n * (1 + pairGrading (stateGrading S) realGrading (n + loss)
          (z - (C.referenceState, 0)))

/-- Actual forward root bounds give both relative directions. The only
smallness change is a common low-order restriction, before any component. -/
theorem n04b_exists_common_root_relative_positiveJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ outLoss ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∀ side : Bool, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        CanonicalRootRelativeJetFamily S C K newBase outLoss ε' m side B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨rootBase, rootLoss, η, hb, _hrootLow, hη, hηε, hroots⟩ :=
    n04b_exists_common_root_endpoint_fields hS hT hN hfield hA hB
  obtain ⟨low, outLoss, hbound⟩ := relativeChart_positiveJets_fixed_loss hp hI rootLoss
  let newBase := max rootBase (max low outLoss)
  let ε' := min η (1 / 2 : ℝ)
  have hε' : 0 < ε' := lt_min hη (by norm_num)
  have hb' : base ≤ newBase := hb.trans (le_max_left _ _)
  have hε'ε : ε' ≤ ε := (min_le_left _ _).trans hηε
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hrefRoot : (C.referenceState, 0) ∈ stateNeighborhood S C rootBase η :=
    reference_mem_stateNeighborhood S C rootBase hη
  have hsref : stateSector S C.referenceState := hN.1.1.2.2.1.stateSector
  refine ⟨newBase, outLoss, ε', hb', (le_max_right _ _).trans (le_max_right _ _),
    hε', hε'ε, ?_⟩
  intro m side
  let r := n01ComponentRoot C m side
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  obtain ⟨κJ, A, hκJ, hApos, hroots⟩ := hroots m side
  obtain ⟨B, hBpos, hbnd⟩ := hbound A hApos κJ hκJ
  refine ⟨B, hBpos, ?_⟩
  dsimp only [CanonicalRootRelativeJetFamily]
  intro z hz hs θ
  have hzold : z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C hb' hε'ε hz
  have hzroot : z ∈ stateNeighborhood S C rootBase η :=
    stateNeighborhood_mono S C (le_max_left _ _) (min_le_left _ _) hz
  have hzlow : z ∈ stateNeighborhood S C low ε' :=
    stateNeighborhood_mono S C ((le_max_left _ _).trans (le_max_right _ _)) le_rfl hz
  have hsmall : pairGrading (stateGrading S) realGrading low
      (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hzlow).trans (by
      have he : ε' ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  have hreference (φ : ℝ) : RootPhysicalFieldJetBound
      (pairGrading (stateGrading S) realGrading) rootLoss A
      (z - (C.referenceState, 0)) (K.chart (C.referenceState, 0) i)
      (K.height (C.referenceState, 0) i) (r, φ) :=
    RootPhysicalFieldJetBound.from_zero (fun n => (hApos n).le)
      (by simpa only [sub_self] using (hroots _ hrefRoot hsref φ).2.2) _
  have hcurrent (φ : ℝ) : RootPhysicalFieldJetBound
      (pairGrading (stateGrading S) realGrading) rootLoss A
      (z - (C.referenceState, 0)) (K.chart z i) (K.height z i) (r, φ) :=
    (hroots z hzroot hs φ).2.2
  have hbetween (z₀ z₁ : AnnularState S × ℝ)
      (hz₀ : z₀ ∈ stateNeighborhood S C base ε) (hs₀ : stateSector S z₀.1)
      (hz₁ : z₁ ∈ stateNeighborhood S C base ε) (hs₁ : stateSector S z₁.1)
      (hF₀ : ∀ φ, RootPhysicalFieldJetBound
        (pairGrading (stateGrading S) realGrading) rootLoss A
        (z - (C.referenceState, 0)) (K.chart z₀ i) (K.height z₀ i) (r, φ))
      (hF₁ : ∀ φ, RootPhysicalFieldJetBound
        (pairGrading (stateGrading S) realGrading) rootLoss A
        (z - (C.referenceState, 0)) (K.chart z₁ i) (K.height z₁ i) (r, φ))
      (hJ₁ : ∀ φ, κJ ≤ |planeJacobian (K.chart z₁ i) (r, φ)|) :
      ContDiffAt ℝ ∞ (K.inverseChart z₁ i ∘ K.chart z₀ i) (r, θ) ∧
        ∀ n : ℕ, 1 ≤ n →
          ‖iteratedFDeriv ℝ n (K.inverseChart z₁ i ∘ K.chart z₀ i) (r, θ)‖ ≤
            B n * (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
    have hc : (r, θ) ∈ physicalPieceClosed S K z₀ i :=
      (canonicalCutRoot_mem_closed_and_zero hA hB.1 hz₀ hs₀ m side θ).1
    have hq : K.chart z₀ i (r, θ) ∈ canonicalClosed S K i :=
      (hA.boundary z₀ hz₀ hs₀ i).1 hc
    let y := K.inverseChart z₁ i (K.chart z₀ i (r, θ))
    have hy : y = (r, y.2) :=
      Prod.ext (rootBetween_states_radial hA hB.1 hz₀ hs₀ hz₁ hs₁ m side θ) rfl
    have hF : ContDiffAt ℝ ∞ (K.chart z₁ i) y := by
      rw [hy]
      exact (hF₁ y.2).1
    have hG := n04b_inverseChart_contDiffAt_closed hA hz₁ hs₁ i hq
    have hgerms := canonicalClosed_inverse_germs hA hz₁ hs₁ i hq
    refine ⟨hG.comp (r, θ) (hF₀ θ).1, ?_⟩
    exact hbnd (z - (C.referenceState, 0)) hsmall
      (K.chart z₁ i) (K.inverseChart z₁ i) (K.chart z₀ i) (r, θ)
      hF hG (hF₀ θ).1 hgerms.2 hgerms.1
      (by change κJ ≤ |planeJacobian (K.chart z₁ i) y|; rw [hy]; exact hJ₁ y.2)
      (fun n hn => by
        change ‖iteratedFDeriv ℝ n (K.chart z₁ i) y‖ ≤ _
        rw [hy]
        exact (hF₁ y.2).2.2.2.1 n hn)
      (fun n hn => (hF₀ θ).2.2.2.1 n hn)
  have hforward := hbetween (C.referenceState, 0) z href hsref hzold hs
    hreference hcurrent (fun φ => (hroots z hzroot hs φ).2.1)
  have hinverse := hbetween z (C.referenceState, 0) hzold hs href hsref
    hcurrent hreference (fun φ => (hroots _ hrefRoot hsref φ).2.1)
  exact ⟨hforward.1, hinverse.1, hforward.2, hinverse.2⟩

end ContinuousFlexibility.Analysis
