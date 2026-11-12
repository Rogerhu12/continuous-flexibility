import ContinuousFlexibility.Analysis.N08AffineTamePullback
import ContinuousFlexibility.Analysis.N08Neighborhoods

/-! # The actual affine inclusion of the closed sector parameter space -/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private def n08_pairSubtypeCLM {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (Q : Submodule ℝ E) : Q × ℝ →L[ℝ] E × ℝ :=
  Q.subtypeL.prodMap (ContinuousLinearMap.id ℝ ℝ)

private theorem n08_pairSubtype_grading {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (Q : Submodule ℝ E) (p : ℕ → Seminorm ℝ E) (s : ℕ) (z : Q × ℝ) :
    pairGrading p realGrading s (n08_pairSubtypeCLM Q z) =
      pairGrading (fun n => (p n).comp Q.subtype) realGrading s z := rfl

private theorem n08_pairSubtype_grading_bound {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (Q : Submodule ℝ E) (p : ℕ → Seminorm ℝ E) (s : ℕ) (z : Q × ℝ) :
    pairGrading p realGrading s (n08_pairSubtypeCLM Q z) ≤
      1 * pairGrading (fun n => (p n).comp Q.subtype) realGrading s z := by
  simpa only [one_mul] using (n08_pairSubtype_grading Q p s z).le

private theorem n08_centered_pair_membership {E : Type*}
    [AddCommGroup E] [Module ℝ E] (p : ℕ → Seminorm ℝ E)
    (base : ℕ) (ε q : ℝ) (a x : E) :
    (p base (a + x - a) < ε ∧ |q| < ε) ↔ (p base x < ε ∧ |q| < ε) := by
  rw [add_sub_cancel_left]

private theorem n08_smoothTameOn_affine_chart
    {E F G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set F} {f : F → G} (hf : SmoothTameOn q r U f)
    (a : F) (L : E →L[ℝ] F) (chart : E → F) (hchart : ∀ z, chart z = a + L z)
    {V : Set E} (hV : IsOpen V) (hL : ∀ n x, q n (L x) ≤ 1 * p n x)
    (hmap : MapsTo chart V U) : SmoothTameOn p r V (fun z => f (chart z)) := by
  have hpre := n08_smoothTameOn_affine_pullback (p := p) hf a L (A := 1) le_rfl hL
  have hs := smoothTameOn_mono hpre hV (fun z hz => by
    change a + L z ∈ U
    rw [← hchart z]
    exact hmap hz)
  exact smoothTameOn_congr hs (fun z _ => congrArg f (hchart z).symm)

def n08SectorParameterInclusion (S : PhysicalSpacesData) :
    StateDirections S × ℝ →L[ℝ] AnnularState S × ℝ :=
  n08_pairSubtypeCLM (stateSectorSubmodule S)

theorem n08SectorParameterInclusion_apply (S : PhysicalSpacesData)
    (z : StateDirections S × ℝ) : n08SectorParameterInclusion S z = (z.1.val, z.2) := rfl

theorem n08SectorParameterInclusion_grading (S : PhysicalSpacesData)
    (s : ℕ) (z : StateDirections S × ℝ) :
    pairGrading (stateGrading S) realGrading s (n08SectorParameterInclusion S z) =
      pairGrading (sectorGrading S) realGrading s z :=
  n08_pairSubtype_grading (stateSectorSubmodule S) (stateGrading S) s z

theorem n08SectorParameterInclusion_bound (S : PhysicalSpacesData)
    (s : ℕ) (z : StateDirections S × ℝ) :
    pairGrading (stateGrading S) realGrading s (n08SectorParameterInclusion S z) ≤
      1 * pairGrading (sectorGrading S) realGrading s z :=
  n08_pairSubtype_grading_bound (stateSectorSubmodule S) (stateGrading S) s z

theorem n08_liftSectorParameter_eq (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ) :
    liftSectorParameter S C z = (C.referenceState, 0) + n08SectorParameterInclusion S z := by
  apply Prod.ext
  · rfl
  · exact (zero_add z.2).symm

private theorem n08_centered_pair_grading {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (s : ℕ) (a x : E) (q : ℝ) :
    pairGrading p realGrading s ((a + x, q) - (a, 0)) =
      pairGrading p realGrading s (x, q) := by
  simp only [Prod.mk_sub_mk, add_sub_cancel_left, sub_zero]

theorem n08_liftSectorParameter_difference (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (s : ℕ) (z : StateDirections S × ℝ) :
    pairGrading (stateGrading S) realGrading s
      (liftSectorParameter S C z - (C.referenceState, 0)) =
      pairGrading (sectorGrading S) realGrading s z :=
  (n08_centered_pair_grading (stateGrading S) s C.referenceState z.1.val z.2).trans
    (n08SectorParameterInclusion_grading S s z)

theorem n08_liftSectorParameter_mem (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) (z : StateDirections S × ℝ) :
    liftSectorParameter S C z ∈ stateNeighborhood S C base ε ↔
      z ∈ sectorNeighborhood S base ε ε :=
  n08_centered_pair_membership (stateGrading S) base ε z.2 C.referenceState z.1.val

theorem n08_referenceState_sector {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (href : referenceStateConditions D S C) :
    stateSector S C.referenceState := by
  obtain ⟨_, _, _, hκ, hh, _⟩ := href
  constructor
  · intro m θ φ
    simp only [hκ, map_zero, Pi.zero_apply]
  · intro m θ
    simp only [hh, map_zero, Pi.zero_apply, neg_zero]

theorem n08_liftSectorParameter_sector {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (href : referenceStateConditions D S C)
    (z : StateDirections S × ℝ) : stateSector S (liftSectorParameter S C z).1 :=
  (stateSectorSubmodule S).add_mem (n08_referenceState_sector href) z.1.property

theorem n08_smoothTameOn_sector_pullback
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {q : ℕ → Seminorm ℝ Y} {U : Set (AnnularState S × ℝ)}
    {f : AnnularState S × ℝ → Y} {base : ℕ} {ε : ℝ}
    (hf : SmoothTameOn (pairGrading (stateGrading S) realGrading) q U f)
    (hmap : MapsTo (liftSectorParameter S C) (sectorNeighborhood S base ε ε) U) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading) q
      (sectorNeighborhood S base ε ε) (fun z => f (liftSectorParameter S C z)) :=
  n08_smoothTameOn_affine_chart (p := pairGrading (sectorGrading S) realGrading)
    hf (C.referenceState, 0) (n08SectorParameterInclusion S) (liftSectorParameter S C)
    (n08_liftSectorParameter_eq S C) (n08_isOpen_sectorNeighborhood S base ε ε)
    (n08SectorParameterInclusion_bound S) hmap

end ContinuousFlexibility.Statements
