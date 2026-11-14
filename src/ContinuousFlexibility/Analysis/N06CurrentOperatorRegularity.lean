module

public import ContinuousFlexibility.Analysis.N06CurrentOperatorPeriodicity
public import ContinuousFlexibility.Analysis.N06PositiveCurrentTestLp
public import ContinuousFlexibility.Analysis.N06CanonicalHeightGerm

/-!
# Local smoothness of the actual corrected operator on even fields

The original coefficients are smooth by N01. N03 subtracts a decoded
source, which is genuinely smooth in the original physical model. Thus
its operator value on every HeightPair is smooth. Compact realization of
local even periodic germs transfers that conclusion to the actual N04
height, including on negative pieces where corrected coefficient
regularity was not separately stipulated.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n06_divergenceOperator_congr_eventually
    (A : SymmetricCoefficients) {f g : PolarPoint → ℝ} {p : PolarPoint}
    (hfg : f =ᶠ[𝓝 p] g) :
    divergenceOperator A f =ᶠ[𝓝 p] divergenceOperator A g := by
  filter_upwards [hfg.eventuallyEq_nhds] with q hq
  exact n05_divergenceOperator_congr A hq

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- This is smoothness of the actual operator value, derived from the
original N03 source identity on the same HeightPair. -/
theorem n06_correctedDivergence_heightPair_contDiffAt
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (η : HeightPair S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (divergenceOperator (L.coefficients z) (heightPairField S η)) p := by
  have hcoef := n06_originalCoefficients_contDiffAt hT hS h01 hz hs hp
  have hη : ContDiff ℝ ∞ (heightPairField S η) :=
    physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4) η.1 η.2
  have horig := n06_contDiffAt_divergenceOperator hcoef.1 hcoef.2.1 hcoef.2.2 hη.contDiffAt
  have herr : ContDiff ℝ ∞
      ((S.height (3 / 4 : ℝ)).decode (L.error z (R.residual z) η).val) :=
    (physical_height_contDiff_and_flatJets hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) (L.error z (R.residual z) η).val).1
  have he : divergenceOperator (L.coefficients z) (heightPairField S η) =ᶠ[𝓝 p]
      (fun q => divergenceOperator (originalCoefficients D S C z) (heightPairField S η) q -
        (S.height (3 / 4 : ℝ)).decode (L.error z (R.residual z) η).val q) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    have hid := h03.2.2.2.2.2.1 z hz hs η q hq
    exact eq_sub_iff_add_eq.mpr
      ((add_comm _ _).trans (sub_eq_iff_eq_add.mp hid).symm)
  exact (horig.sub herr.contDiffAt).congr_of_eventuallyEq he

/-- Smooth even periodic strip fields are tested through their genuine
compact height realizations, so the corrected divergence is smooth there. -/
theorem n06_correctedDivergence_contDiffOn_strip
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {l r : ℝ} (hsub : Ioo l r ⊆ radialCore D)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo l r ×ˢ univ))
    (hp : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), f (p + (0, Real.pi)) = f p)
    (he : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), f (p.1, -p.2) = f p) :
    ContDiffOn ℝ ∞ (divergenceOperator (L.coefficients z) f) (Ioo l r ×ˢ univ) := by
  intro p hpI
  obtain ⟨η, hη⟩ := n06_exists_heightPair_strip_germ hT hS hsub hpI.1 hf hp he
  have hreg := n06_correctedDivergence_heightPair_contDiffAt hT hS h01 h03 hz hs η
    (p := p) ⟨hsub hpI.1, mem_univ _⟩
  exact (hreg.congr_of_eventuallyEq
    (n06_divergenceOperator_congr_eventually (L.coefficients z) (hη p.2).symm)).contDiffWithinAt

/-- The actual current N04 height has a smooth corrected divergence on
each original physical piece. No coefficient extension is selected. -/
theorem n06_correctedHeightDivergence_contDiffOn_piece
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    ContDiffOn ℝ ∞ (divergenceOperator (L.coefficients z) (K.height z m))
      (physicalPieceOpen S K z m) := by
  intro p hp
  obtain ⟨η, hη⟩ := n06_exists_heightPair_canonicalHeight_germ hT hS hA hz hs m hp
  have hreg := n06_correctedDivergence_heightPair_contDiffAt hT hS h01 h03 hz hs η
    ((hA.domains z hz hs m).2.2.1 hp)
  exact (hreg.congr_of_eventuallyEq
    (n06_divergenceOperator_congr_eventually (L.coefficients z)
      (hη p hp rfl).symm)).contDiffWithinAt

end ContinuousFlexibility.Statements
