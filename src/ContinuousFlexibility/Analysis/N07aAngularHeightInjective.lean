import ContinuousFlexibility.Analysis.N07aAngularCandidateCoordinates
import ContinuousFlexibility.Analysis.N07aPhysicalPieceBound

/-!
# The actual canonical height coordinates determine the physical height

The smooth canonical transform agrees almost everywhere with zero, so it
vanishes throughout the open strip. The actual inverse chart and positive
height recover the physical function on each piece. Original null-set
coverage and continuity then recover every interface as well.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_height_eq_zero_of_canonical
    (hS : IsPhysicalSpaces D T S)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : (S.height (3 / 4 : ℝ)).Space)
    (hU : ∀ m, canonicalHeight S K z m ((S.height (3 / 4 : ℝ)).decode u)
      =ᵐ[canonicalMeasure S K m] fun _ => 0) : u = 0 := by
  have hd := (hS.1 (3 / 4 : ℝ)).2.2.2.1 u
  have hpiece (m : ℕ) : EqOn ((S.height (3 / 4 : ℝ)).decode u)
      (fun _ => 0) (physicalPieceOpen S K m) := by
    have hcanon : EqOn (canonicalHeight S K z m ((S.height (3 / 4 : ℝ)).decode u))
        (fun _ => 0) (canonicalOpen S K m) :=
      n07a_canonical_periodicOn_eqOn_of_ae_eq
        (n07a_candidateCanonicalHeight_contDiffOn h04 hz hs hd.1 m).continuousOn
        continuousOn_const (n07a_candidateCanonicalHeight_periodic h04 hz hs hd.2.2.1 m)
        (fun _ _ => rfl) (hU m)
    have hg := h04.2.2.2.2.2.2.2.1 z hz hs m
    intro p hp
    have he := hcanon (hg.1 hp)
    simp only [canonicalHeight, hg.2.2.1 p hp] at he
    exact (div_eq_zero_iff).mp he |>.resolve_right (hg.2.2.2.2.2.2.2 p hp).1.ne'
  have hbound : ∀ p ∈ annularOpen D,
      |(S.height (3 / 4 : ℝ)).decode u p| ≤ (0 : ℝ) :=
    n07a_physicalPiece_bound h04 hd.1.continuousOn.abs continuousOn_const
      (fun m p hp => by rw [hpiece m hp, abs_zero])
  apply (hS.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext p
  rw [map_zero, Pi.zero_apply]
  by_cases hp : p ∈ annularOpen D
  · exact abs_eq_zero.mp (le_antisymm (hbound p hp) (abs_nonneg _))
  · exact hd.2.2.2.1 p hp

end ContinuousFlexibility.Analysis
