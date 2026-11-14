module

public import ContinuousFlexibility.Analysis.N08ControlResidualColumn
public import ContinuousFlexibility.Analysis.N08SectorParameterChart

/-!
# The control column on the actual sector chart

The scalar inverse is prescribed on sector states. Extending the control
column by zero off that sector preserves its actual sector derivatives and
its smooth pullback to the sector chart. No regularity across the ambient
sector boundary is asserted or needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private theorem n08_prodMap_preserves_grading
    {E F B : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace B] [AddCommGroup B] [Module ℝ B]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (b : ℕ → Seminorm ℝ B)
    (L : E →L[ℝ] F) (hL : ∀ s x, q s (L x) = p s x) (s : ℕ) (z : E × B) :
    pairGrading q b s ((L.prodMap (ContinuousLinearMap.id ℝ B)) z) =
      pairGrading p b s z := by
  change q s (L z.1) + b s z.2 = p s z.1 + b s z.2
  exact congrArg (fun y : ℝ => y + b s z.2) (hL s z.1)

private theorem n08_smoothTameOn_product_chart
    {E F B Y : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F]
    [TopologicalSpace B] [AddCommGroup B] [Module ℝ B] [IsTopologicalAddGroup B]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {b : ℕ → Seminorm ℝ B} {r : ℕ → Seminorm ℝ Y}
    {U : Set F} {V : Set E} {f : F × B → Y} {g : E × B → Y}
    (hf : SmoothTameOn (pairGrading q b) r (U ×ˢ univ) f)
    (a : F) (L : E →L[ℝ] F) (chart : E → F) (hchart : ∀ x, chart x = a + L x)
    (hV : IsOpen V) (hL : ∀ s x, q s (L x) ≤ 1 * p s x)
    (hmap : MapsTo chart V U) (hg : ∀ z, g z = f (chart z.1, z.2)) :
    SmoothTameOn (pairGrading p b) r (V ×ˢ univ) g := by
  have hbig (s : ℕ) (z : E × B) :
      pairGrading q b s ((L.prodMap (ContinuousLinearMap.id ℝ B)) z) ≤
        1 * pairGrading p b s z := by
    change q s (L z.1) + b s z.2 ≤ 1 * (p s z.1 + b s z.2)
    simpa only [one_mul] using add_le_add (hL s z.1) (le_rfl : b s z.2 ≤ b s z.2)
  have hbigchart (z : E × B) :
      (a, 0) + (L.prodMap (ContinuousLinearMap.id ℝ B)) z = (chart z.1, z.2) := by
    apply Prod.ext
    · exact (hchart z.1).symm
    · exact zero_add z.2
  have hpre := n08_smoothTameOn_affine_pullback hf (a, 0)
    (L.prodMap (ContinuousLinearMap.id ℝ B)) (A := 1) le_rfl hbig
  have hs := smoothTameOn_mono hpre (hV.prod isOpen_univ) (fun z hz => by
    change (a, 0) + (L.prodMap (ContinuousLinearMap.id ℝ B)) z ∈ U ×ˢ univ
    rw [hbigchart]
    exact ⟨hmap hz.1, mem_univ _⟩)
  exact smoothTameOn_congr hs (fun z _ => (congrArg f (hbigchart z)).trans (hg z).symm)

private theorem n08_rectangle_pairGrading_lt
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) {base s : ℕ} {ε : ℝ}
    (hs : s ≤ base) (z : E × ℝ) (hz : p base z.1 < ε ∧ |z.2| < ε) :
    pairGrading p realGrading s z < 2 * ε := by
  have hfirst := (hp hs z.1).trans_lt hz.1
  change p s z.1 + |z.2| < 2 * ε
  exact (add_lt_add hfirst hz.2).trans_eq (by ring)

private theorem n08_centered_rectangle_pairGrading_lt
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (a : E) {base s : ℕ} {ε : ℝ}
    (hs : s ≤ base) (z : E × ℝ) (hz : p base (z.1 - a) < ε ∧ |z.2| < ε) :
    pairGrading p realGrading s (z - (a, 0)) < 2 * ε := by
  have h := n08_rectangle_pairGrading_lt p hp hs (z.1 - a, z.2) hz
  change p s (z.1 - a) + |z.2| < 2 * ε at h
  change p s (z.1 - a) + |z.2 - 0| < 2 * ε
  simpa only [sub_zero] using h

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
      pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading s z :=
  n08_prodMap_preserves_grading (pairGrading (sectorGrading S) realGrading)
    (pairGrading (stateGrading S) realGrading) controlGrading
    (n08SectorParameterInclusion S) (n08SectorParameterInclusion_grading S) s z

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
        n08SectorControlColumn S H (liftSectorParameter S C z.1) z.2) :=
  n08_smoothTameOn_product_chart
    (E := StateDirections S × ℝ) (F := AnnularState S × ℝ)
    (B := ControlBanach) (Y := S.Source)
    (p := pairGrading (sectorGrading S) realGrading)
    (q := n08StateParameterGrading S) (b := controlGrading)
    hH (C.referenceState, 0) (n08SectorParameterInclusion S) (liftSectorParameter S C)
    (n08_liftSectorParameter_eq S C) (n08_isOpen_sectorNeighborhood S base ε ε)
    (n08SectorParameterInclusion_bound S) hmap
    (fun z => congrArg (fun L : ControlBanach →L[ℝ] S.Source => L z.2)
      (n08SectorControlColumn_lift href H z.1))

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
      n08StateParameterGrading S s (z - (C.referenceState, 0)) :=
  (n08_liftSectorParameter_difference S C s (n08SectorParameterCenter href z hs)).symm.trans
    (congrArg (fun w : AnnularState S × ℝ =>
      n08StateParameterGrading S s (w - (C.referenceState, 0)))
      (n08SectorParameterCenter_lift href z hs))

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
    pairGrading (sectorGrading S) realGrading s z < 2 * ε :=
  n08_rectangle_pairGrading_lt (sectorGrading S) (solve_sectorGrading_monotone S) hs z hz

theorem n08_stateNeighborhood_pairGrading_lt {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base s : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hs : s ≤ base) (hz : z ∈ stateNeighborhood S C base ε) :
    n08StateParameterGrading S s (z - (C.referenceState, 0)) < 2 * ε :=
  n08_centered_rectangle_pairGrading_lt (stateGrading S) (solve_stateGrading_monotone S)
    C.referenceState hs z hz

theorem n08_sectorNeighborhood_maps_controlBall {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base columnBase : ℕ} {ε δ : ℝ}
    (hb : columnBase ≤ base) (hε : 2 * ε ≤ δ) :
    MapsTo (liftSectorParameter S C) (sectorNeighborhood S base ε ε)
      {z | n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ} := by
  intro z hz
  exact (n08_liftSectorParameter_difference S C columnBase z).trans_lt
    ((n08_sectorNeighborhood_pairGrading_lt hb hz).trans_le hε)

end ContinuousFlexibility.Statements
