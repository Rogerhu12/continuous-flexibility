import ContinuousFlexibility.Analysis.RetainedMorsePositiveGapEndpointX
import ContinuousFlexibility.Analysis.MaterialClosedHostEndpointX
import ContinuousFlexibility.Analysis.MaterialOneSidedEndpointComparison
import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# A true negative host sample compared with the positive midpoint sample

The common physical root lies in the closure of the original negative
host and in the same retained positive gap. Continuity supplies the
host-index bound there. The genuine gap oscillation then connects it
to the selected positive midpoint, without replacing either sample.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- Every fixed power of the original negative-host sample is controlled
at any cell containing the actual positive midpoint. A root shared with
that negative component is a special case of the displayed closed
intersection; no root-index or host assignment is changed. -/
theorem retainedReference_positive_gap_host_sample_bound
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ (side : Bool) (n : ℕ), S.chain.index ≤ n →
      ∀ j k l u r,
        NegativeRadialComponent Γ.reference l u → Ioo l u ⊆ Γ.reference.cells j →
        r ∈ Icc (n06MorsePositiveLeft S.chain side n)
          (n06MorsePositiveRight S.chain side n) →
        P.sideRadius side * r ∈ Icc l u →
        P.sideRadius side * ((n06MorsePositiveLeft S.chain side n +
          n06MorsePositiveRight S.chain side n) / 2) ∈ Γ.reference.cells k →
        T.E0 (T.sample j) ^ R ≤ C * T.E0 (T.sample k) ^ A := by
  obtain ⟨L, hL, hgap⟩ := retainedReference_positive_gap_endpointX_oscillation
    P hS hband hcoordinates hT
  obtain ⟨B, hB, hcell, hclosed⟩ := material_cell_endpointX_closed_interval hT
  obtain ⟨CH, AH, C, A, _, _, hC, hA, hmaterial⟩ :=
    material_oneSided_endpoint_comparison hT hΓ.2.1 hR
      (show 0 ≤ L + 4 * B by positivity)
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, _⟩ := hdata
  refine ⟨C, A, hC, hA, ?_⟩
  intro side n hn j k l u r hcomponent hhost hr hroot hmid
  let x : ℝ := P.sideRadius side * r
  let t : ℝ := (n06MorsePositiveLeft S.chain side n +
    n06MorsePositiveRight S.chain side n) / 2
  let y : ℝ := P.sideRadius side * t
  have hg := n06_morsePositive_gap_geometry
    (hS.2.2.2.1 S.sigma hS.2.2.1).1 side hn
  have hspan : n06MorsePositiveLeft S.chain side n <
      n06MorsePositiveRight S.chain side n :=
    hg.2.1.trans (hg.2.2.1.trans hg.2.2.2.1)
  have ht : t ∈ Icc (n06MorsePositiveLeft S.chain side n)
      (n06MorsePositiveRight S.chain side n) := by
    constructor <;> dsimp only [t] <;> linarith only [hspan]
  have hsJ := abs_le.mp (hcell j (T.sample j) (hsample j))
  have hxJ := abs_le.mp (hclosed l u j hcomponent.1 hcomponent.2.1
    hcomponent.2.2.1 hhost x hroot)
  have hxy := (abs_le.mp (hgap side n hn r t hr ht)).2
  have hyK := abs_le.mp (hcell k y hmid)
  have hsK := abs_le.mp (hcell k (T.sample k) (hsample k))
  have hshift : endpointX 1 (Statements.endpointDistance Γ.reference (T.sample j)) ≤
      endpointX 1 (Statements.endpointDistance Γ.reference (T.sample k)) + (L + 4 * B) := by
    change endpointX 1 (Statements.endpointDistance Γ.reference x) -
      endpointX 1 (Statements.endpointDistance Γ.reference y) ≤ L at hxy
    linarith only [hsJ.2, hxJ.1, hxy, hyK.2, hsK.1]
  exact (hmaterial (T.sample k) (T.sample j)
    (materialSample_mem_interval hΓ.2.1 hT k)
    (materialSample_mem_interval hΓ.2.1 hT j) hshift).2

end ContinuousFlexibility.Radial
