module

public import ContinuousFlexibility.Analysis.N07bCanonicalAEPullback

/-!
# Almost-everywhere identification on the whole physical annulus

At each admissible state the actual physical domains cover the annulus
outside a planar null set. Countably many piecewise a.e. identities
therefore give one a.e. identity on the physical fundamental strip.

This uses the actual atlas and its stated null exceptional set. Neither
integrability nor continuity of the represented functions is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- An a.e. assertion on every current physical piece holds on the whole
physical fundamental strip, using the planar a.e. cover in Part A. -/
theorem n07b_ae_physical_of_ae_pieces
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {P : PolarPoint → Prop}
    (hP : ∀ m, ∀ᵐ p ∂volume.restrict
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)), P p) :
    ∀ᵐ p ∂volume.restrict (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi), P p := by
  obtain ⟨E, hE, hcover⟩ := hK.partition z hz hsector
  have houtside : ∀ᵐ p : PolarPoint ∂volume, p ∉ E := by
    apply ae_iff.mpr
    simpa only [not_not, setOf_mem_eq] using hE
  have hpieces : ∀ᵐ p : PolarPoint ∂volume,
      ∀ m, p ∈ physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi) → P p := by
    apply ae_all_iff.mpr
    intro m
    exact (ae_restrict_iff'
      ((hK.domains z hz hsector m).1.measurableSet.inter
        (MeasurableSet.univ.prod measurableSet_Ioc))).mp (hP m)
  apply (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioc)).mpr
  filter_upwards [houtside, hpieces] with p hpE hp hpstrip
  obtain ⟨m, hm, _⟩ := hcover p ⟨⟨hpstrip.1, mem_univ _⟩, hpE⟩
  exact hp m ⟨hm, ⟨mem_univ _, hpstrip.2⟩⟩

/-- Restrict an a.e. physical assertion to any one of the current pieces. -/
theorem n07b_ae_piece_of_ae_physical
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {P : PolarPoint → Prop}
    (hP : ∀ᵐ p ∂volume.restrict (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi), P p)
    (m : ℕ) :
    ∀ᵐ p ∂volume.restrict
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)), P p := by
  have h := (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioc)).mp hP
  apply (ae_restrict_iff'
    ((hK.domains z hz hsector m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc))).mpr
  filter_upwards [h] with p hp hpiece
  exact hp ⟨((hK.domains z hz hsector m).2.2.1 hpiece.1).1, hpiece.2.2⟩

/-- All canonical source classes together determine exactly the physical
a.e. class on one fundamental angular period. -/
theorem n07b_canonicalSources_ae_iff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (f g : PolarPoint → ℝ) :
    (∀ m, canonicalSource S K z m f =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m g) ↔
    f =ᵐ[volume.restrict (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi)] g := by
  constructor
  · intro h
    apply n07b_ae_physical_of_ae_pieces hK hz hsector
    intro m
    exact (n07b_canonicalSource_ae_iff hK hz hsector m f g).mp (h m)
  · intro h m
    apply (n07b_canonicalSource_ae_iff hK hz hsector m f g).mpr
    exact n07b_ae_piece_of_ae_physical hK hz hsector h m

/-- The same whole-annulus identification holds for canonical heights. -/
theorem n07b_canonicalHeights_ae_iff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (f g : PolarPoint → ℝ) :
    (∀ m, canonicalHeight S K z m f =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m g) ↔
    f =ᵐ[volume.restrict (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi)] g := by
  constructor
  · intro h
    apply n07b_ae_physical_of_ae_pieces hK hz hsector
    intro m
    exact (n07b_canonicalHeight_ae_iff hK hz hsector m f g).mp (h m)
  · intro h m
    apply (n07b_canonicalHeight_ae_iff hK hz hsector m f g).mpr
    exact n07b_ae_piece_of_ae_physical hK hz hsector h m

/-- Two physical witnesses of one canonical representation have the same
field and source a.e. on the whole physical fundamental strip. -/
theorem n07b_representation_physical_ae_global
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    {η ξ f g : PolarPoint → ℝ}
    (hη : HasCanonicalRepresentation D S C K z U F η f)
    (hξ : HasCanonicalRepresentation D S C K z U F ξ g) :
    η =ᵐ[volume.restrict (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi)] ξ ∧
    f =ᵐ[volume.restrict (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi)] g := by
  constructor
  · exact n07b_ae_physical_of_ae_pieces hK hz hsector (fun m =>
      (n07b_representation_physical_ae hK hz hsector hη hξ m).1)
  · exact n07b_ae_physical_of_ae_pieces hK hz hsector (fun m =>
      (n07b_representation_physical_ae hK hz hsector hη hξ m).2)

end ContinuousFlexibility.Analysis
