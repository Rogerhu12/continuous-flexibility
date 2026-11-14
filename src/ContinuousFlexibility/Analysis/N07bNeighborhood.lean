module

public import ContinuousFlexibility.Analysis.N06Neighborhood

/-!
# Restriction of the scalar inverse on the same nonlinear construction

Increasing the low order and decreasing the positive radius preserves the
properties through N06, the scalar inverse family, and its Banach
identification. Every chart, source space, reference domain, relative
inverse, and scalar inverse remains the original witness.

A fixed state order can be put below the new low order. On a neighborhood
of radius at most one half, the corresponding state weight is at most two.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

private theorem n07b_linearFamilyTame_mono
    {E F G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (r : ℕ → Seminorm ℝ G) (A : E → G →ₗ[ℝ] F)
    {U V : Set E} (hVU : V ⊆ U) (h : LinearFamilyTame p q r U A) :
    LinearFamilyTame p q r V A := by
  obtain ⟨loss, base, hbound⟩ := h
  refine ⟨loss, base, fun s hs => ?_⟩
  obtain ⟨C, hC, hCs⟩ := hbound s hs
  exact ⟨C, hC, fun x hx => hCs x (hVU hx)⟩

private theorem n07b_smoothTameOn_product_mono
    {E F G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (r : ℕ → Seminorm ℝ G) (f : E × G → F)
    {U V : Set E} (hV : IsOpen V) (hVU : V ⊆ U)
    (h : SmoothTameOn (pairGrading p r) q (U ×ˢ univ) f) :
    SmoothTameOn (pairGrading p r) q (V ×ˢ univ) f :=
  smoothTameOn_mono h (hV.prod isOpen_univ)
    (Set.prod_mono hVU (subset_refl _))

theorem n07b_N06Properties_mono {D : ReferenceData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {L : ReturnCorrectionData S}
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    {P : RelativeInverseData S K V b B}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : N06Properties D S C K L V b B P base ε)
    (hb : base ≤ base') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    N06Properties D S C K L V b B P base' ε' := by
  refine ⟨hε', ?_⟩
  intro z hz
  exact h.2 z (n06_stateNeighborhood_mono (C := C) hb hε hz)

/-- The complete construction through N06 restricts without changing any
of its witnesses or its loss. -/
theorem n07b_NonlinearPropertiesThrough06_mono
    {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    {P : RelativeInverseData S K V b B}
    {base base' loss : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough06 D T S C R L K V b B P base loss ε)
    (hb : base ≤ base') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough06 D T S C R L K V b B P base' loss ε' :=
  ⟨n06_NonlinearPropertiesThrough05_mono hT h.1 hb hε' hε,
    n07b_N06Properties_mono h.2 hb hε' hε⟩

/-- Both uniqueness and the smooth tame directional tower restrict for the
same scalar inverse family. -/
theorem n07b_ScalarInverseProperties_mono {D : ReferenceData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {G : ScalarInverseData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : ScalarInverseProperties D S C L G base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    ScalarInverseProperties D S C L G base' ε' := by
  rcases h with ⟨hsolve, hunique, htame, hsmooth⟩
  have hU := n06_stateNeighborhood_mono (C := C) hb hε
  have hsector := n06_sectorNeighborhood_mono (S := S) hb hε hε
  refine ⟨(fun z hz => hsolve z (hU hz)), (fun z hz => hunique z (hU hz)), ?_, ?_⟩
  · exact n07b_linearFamilyTame_mono
      (E := StateDirections S × ℝ) (F := HeightPair S × ℝ) (G := S.Source)
      (pairGrading (sectorGrading S) realGrading)
      (pairGrading (heightPairGrading S) realGrading) S.sourceGrading
      (fun z => (G.G (liftSectorParameter S C z)).toLinearMap) hsector htame
  · exact n07b_smoothTameOn_product_mono
      (E := StateDirections S × ℝ) (F := HeightPair S × ℝ) (G := S.Source)
      (pairGrading (sectorGrading S) realGrading)
      (pairGrading (heightPairGrading S) realGrading) S.sourceGrading
      (fun z => G.G (liftSectorParameter S C z.1) z.2)
      (n06_isOpen_sectorNeighborhood S base' ε' ε') hsector hsmooth

/-- Restriction retains the actual source representative and the same
Banach solution, including both scalar coordinates. -/
theorem n07b_ScalarBanachBridgeProperties_mono {D : ReferenceData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    {P : RelativeInverseData S K V b B} {G : ScalarInverseData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : ScalarBanachBridgeProperties D S C K V b B P G base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    ScalarBanachBridgeProperties D S C K V b B P G base' ε' := by
  rcases h with ⟨s, hbs, C0, hC0, hbridge⟩
  refine ⟨s, hbs, C0, hC0, ?_⟩
  intro z hz
  exact hbridge z (n06_stateNeighborhood_mono (C := C) hb hε hz)

/-- The full N07 conclusion restricts on the original construction. -/
theorem n07b_NonlinearPropertiesThrough07_mono
    {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    {P : RelativeInverseData S K V b B} {G : ScalarInverseData S}
    {base base' loss : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough07 D T S C R L K V b B P G base loss ε)
    (hb : base ≤ base') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough07 D T S C R L K V b B P G base' loss ε' :=
  ⟨n07b_NonlinearPropertiesThrough06_mono hT h.1 hb hε' hε,
    n07b_ScalarInverseProperties_mono h.2.1 hb hε,
    n07b_ScalarBanachBridgeProperties_mono h.2.2 hb hε⟩

/-- A fixed state order below the new low order is uniformly bounded on
the smaller neighborhood. -/
theorem n07b_stateWeight_le_two {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {r base : ℕ} {ε : ℝ}
    {z : AnnularState S × ℝ}
    (hr : r ≤ base) (hε : ε ≤ (1 / 2 : ℝ))
    (hz : z ∈ stateNeighborhood S C base ε) :
    1 + stateGrading S r (z.1 - C.referenceState) + |z.2| ≤ 2 := by
  have hs : stateGrading S r (z.1 - C.referenceState) < ε :=
    (solve_stateGrading_monotone S hr (z.1 - C.referenceState)).trans_lt hz.1
  have hq : |z.2| < ε := hz.2
  linarith

end ContinuousFlexibility.Statements
