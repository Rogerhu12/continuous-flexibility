import ContinuousFlexibility.Analysis.N08ControlResidualColumn
import ContinuousFlexibility.Analysis.N08SectorParameterChart

/-!
# The control column on the actual sector chart

The scalar inverse is prescribed on sector states. Extending the control
column by zero off that sector preserves its actual sector derivatives and
its smooth pullback to the sector chart. No regularity across the ambient
sector boundary is asserted or needed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

def n08SectorControlColumn (S : PhysicalSpacesData)
    (H : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    (z : AnnularState S × ℝ) : ControlBanach →L[ℝ] S.Source := by
  classical
  exact if stateSector S z.1 then H z else 0

theorem n08SectorControlColumn_of_sector {S : PhysicalSpacesData}
    (H : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    {z : AnnularState S × ℝ} (hs : stateSector S z.1) :
    n08SectorControlColumn S H z = H z := by
  classical
  simp only [n08SectorControlColumn, if_pos hs]

theorem n08SectorControlColumn_of_not_sector {S : PhysicalSpacesData}
    (H : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    {z : AnnularState S × ℝ} (hs : ¬ stateSector S z.1) :
    n08SectorControlColumn S H z = 0 := by
  classical
  simp only [n08SectorControlColumn, if_neg hs]

theorem n08SectorControlColumn_lift {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (href : referenceStateConditions D S C)
    (H : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    (z : StateDirections S × ℝ) :
    n08SectorControlColumn S H (liftSectorParameter S C z) = H (liftSectorParameter S C z) :=
  n08SectorControlColumn_of_sector H (n08_liftSectorParameter_sector href z)

def n08SectorControlInclusion (S : PhysicalSpacesData) :
    (StateDirections S × ℝ) × ControlBanach →L[ℝ] (AnnularState S × ℝ) × ControlBanach :=
  (n08SectorParameterInclusion S).prodMap (ContinuousLinearMap.id ℝ ControlBanach)

theorem n08SectorControlInclusion_grading (S : PhysicalSpacesData) (s : ℕ)
    (z : (StateDirections S × ℝ) × ControlBanach) :
    n08ExtendedControlGrading S s (n08SectorControlInclusion S z) =
      pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading s z := by
  change pairGrading (stateGrading S) realGrading s (n08SectorParameterInclusion S z.1) +
    controlGrading s z.2 =
      pairGrading (sectorGrading S) realGrading s z.1 + controlGrading s z.2
  rw [n08SectorParameterInclusion_grading]

theorem n08SectorControlInclusion_affine (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : (StateDirections S × ℝ) × ControlBanach) :
    ((C.referenceState, 0), 0) + n08SectorControlInclusion S z =
      (liftSectorParameter S C z.1, z.2) := by
  apply Prod.ext
  · exact (n08_liftSectorParameter_eq S C z.1).symm
  · exact zero_add z.2

theorem n08SectorControlColumn_smoothTame
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C)
    {H : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source}
    {U : Set (AnnularState S × ℝ)} {base : ℕ} {ε : ℝ}
    (hH : SmoothTameOn (n08ExtendedControlGrading S) S.sourceGrading (U ×ˢ univ)
      (fun z : (AnnularState S × ℝ) × ControlBanach => H z.1 z.2))
    (hmap : MapsTo (liftSectorParameter S C) (sectorNeighborhood S base ε ε) U) :
    SmoothTameOn (pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading)
      S.sourceGrading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ControlBanach =>
        n08SectorControlColumn S H (liftSectorParameter S C z.1) z.2) := by
  have hpre := n08_smoothTameOn_affine_pullback hH ((C.referenceState, 0), 0)
    (n08SectorControlInclusion S) (A := 1) le_rfl
    (fun n x => by rw [n08SectorControlInclusion_grading, one_mul])
  have hs := smoothTameOn_mono hpre
    ((n08_isOpen_sectorNeighborhood S base ε ε).prod isOpen_univ)
    (fun z hz => by
      change ((C.referenceState, 0), 0) + n08SectorControlInclusion S z ∈ U ×ˢ univ
      rw [n08SectorControlInclusion_affine]
      exact ⟨hmap hz.1, mem_univ _⟩)
  exact smoothTameOn_congr hs (fun z _ => by
    rw [n08SectorControlInclusion_affine, n08SectorControlColumn_lift href])

def n08SectorParameterCenter {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (href : referenceStateConditions D S C)
    (z : AnnularState S × ℝ) (hs : stateSector S z.1) : StateDirections S × ℝ :=
  (⟨z.1 - C.referenceState,
    (stateSectorSubmodule S).sub_mem hs (n08_referenceState_sector href)⟩, z.2)

theorem n08SectorParameterCenter_lift {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (href : referenceStateConditions D S C)
    (z : AnnularState S × ℝ) (hs : stateSector S z.1) :
    liftSectorParameter S C (n08SectorParameterCenter href z hs) = z := by
  apply Prod.ext
  · change C.referenceState + (z.1 - C.referenceState) = z.1
    exact (add_comm _ _).trans (sub_add_cancel _ _)
  · rfl

theorem n08SectorParameterCenter_grading {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (href : referenceStateConditions D S C)
    (s : ℕ) (z : AnnularState S × ℝ) (hs : stateSector S z.1) :
    pairGrading (sectorGrading S) realGrading s (n08SectorParameterCenter href z hs) =
      n08StateParameterGrading S s (z - (C.referenceState, 0)) := by
  have h := n08_liftSectorParameter_difference S C s (n08SectorParameterCenter href z hs)
  rw [n08SectorParameterCenter_lift] at h
  exact h.symm

theorem n08SectorParameterCenter_mem {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (href : referenceStateConditions D S C)
    {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} (hs : stateSector S z.1)
    (hz : z ∈ stateNeighborhood S C base ε) :
    n08SectorParameterCenter href z hs ∈ sectorNeighborhood S base ε ε := by
  apply (n08_liftSectorParameter_mem S C base ε (n08SectorParameterCenter href z hs)).mp
  rwa [n08SectorParameterCenter_lift]

theorem n08_sectorNeighborhood_pairGrading_lt {S : PhysicalSpacesData}
    {base s : ℕ} {ε : ℝ} {z : StateDirections S × ℝ}
    (hs : s ≤ base) (hz : z ∈ sectorNeighborhood S base ε ε) :
    pairGrading (sectorGrading S) realGrading s z < 2 * ε := by
  have hfirst := (solve_sectorGrading_monotone S hs z.1).trans_lt hz.1
  change sectorGrading S s z.1 + |z.2| < 2 * ε
  linarith only [hfirst, hz.2]

theorem n08_stateNeighborhood_pairGrading_lt {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base s : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hs : s ≤ base) (hz : z ∈ stateNeighborhood S C base ε) :
    n08StateParameterGrading S s (z - (C.referenceState, 0)) < 2 * ε := by
  have hfirst := (solve_stateGrading_monotone S hs (z.1 - C.referenceState)).trans_lt hz.1
  change stateGrading S s (z.1 - C.referenceState) + |z.2 - 0| < 2 * ε
  rw [sub_zero]
  linarith only [hfirst, hz.2]

theorem n08_sectorNeighborhood_maps_controlBall {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base columnBase : ℕ} {ε δ : ℝ}
    (hb : columnBase ≤ base) (hε : 2 * ε ≤ δ) :
    MapsTo (liftSectorParameter S C) (sectorNeighborhood S base ε ε)
      {z | n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ} := by
  intro z hz
  change pairGrading (stateGrading S) realGrading columnBase
    (liftSectorParameter S C z - (C.referenceState, 0)) < δ
  rw [n08_liftSectorParameter_difference]
  exact (n08_sectorNeighborhood_pairGrading_lt hb hz).trans_le hε

end ContinuousFlexibility.Statements
