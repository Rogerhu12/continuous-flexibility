import ContinuousFlexibility.Analysis.N07bAtlasAEPullback
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Summing physical energy over the current canonical atlas

At every admissible state the planar a.e. uniqueness of the cover and
openness of its actual domains imply pairwise disjointness. Thus a physical
integrable energy splits into a summable family of piece energies, with no
multiplicity factor. The radial reference intervals retain their separate
disjointness statement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ENNReal

/-- The reference radial intervals are disjoint, by the reference a.e.
unique cover and positivity of the measure of a nonempty open overlap. -/
theorem n07b_physicalIntervals_pairwiseDisjoint
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε) :
    Pairwise (fun m n => Disjoint
      (Ioo (K.physicalLeft m) (K.physicalRight m))
      (Ioo (K.physicalLeft n) (K.physicalRight n))) := by
  obtain ⟨E, hE, hcover⟩ := hK.referencePartition
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro r hrm hrn
  have hsub : Ioo (K.physicalLeft m) (K.physicalRight m) ∩
      Ioo (K.physicalLeft n) (K.physicalRight n) ⊆ E := by
    intro x hx
    by_contra hxE
    obtain ⟨k, _, huniq⟩ := hcover x ⟨(hK.referenceBounds m).2.2 hx.1, hxE⟩
    exact hmn ((huniq m hx.1).trans (huniq n hx.2).symm)
  have hzero : volume (Ioo (K.physicalLeft m) (K.physicalRight m) ∩
      Ioo (K.physicalLeft n) (K.physicalRight n)) = 0 :=
    measure_mono_null hsub hE
  have hpos := (isOpen_Ioo.inter isOpen_Ioo).measure_pos volume
    (show (Ioo (K.physicalLeft m) (K.physicalRight m) ∩
      Ioo (K.physicalLeft n) (K.physicalRight n)).Nonempty from ⟨r, hrm, hrn⟩)
  rw [hzero] at hpos
  exact (lt_irrefl (0 : ℝ≥0∞)) hpos

/-- The current planar domains themselves are disjoint. An open overlap
cannot be contained in the planar null exceptional set of the atlas. -/
theorem n07b_physicalDomains_pairwiseDisjoint
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) :
    Pairwise (fun m n => Disjoint
      (physicalPieceOpen S K z m) (physicalPieceOpen S K z n)) := by
  let : (volume : Measure PolarPoint).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  obtain ⟨E, hE, hcover⟩ := hK.partition z hz hsector
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro p hpm hpn
  have hsub : physicalPieceOpen S K z m ∩ physicalPieceOpen S K z n ⊆ E := by
    intro x hx
    by_contra hxE
    obtain ⟨k, _, huniq⟩ := hcover x
      ⟨(hK.domains z hz hsector m).2.2.1 hx.1, hxE⟩
    exact hmn ((huniq m hx.1).trans (huniq n hx.2).symm)
  have hzero : volume (physicalPieceOpen S K z m ∩ physicalPieceOpen S K z n) = 0 :=
    measure_mono_null hsub hE
  have hpos := ((hK.domains z hz hsector m).1.inter
    (hK.domains z hz hsector n).1).measure_pos volume
    (show (physicalPieceOpen S K z m ∩ physicalPieceOpen S K z n).Nonempty from
      ⟨p, hpm, hpn⟩)
  rw [hzero] at hpos
  exact (lt_irrefl (0 : ℝ≥0∞)) hpos

/-- The actual fundamental physical pieces form a disjoint family. -/
theorem n07b_physicalPieces_pairwiseDisjoint
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) :
    Pairwise (fun m n => Disjoint
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))
      (physicalPieceOpen S K z n ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro p hpm hpn
  exact Set.disjoint_left.mp (n07b_physicalDomains_pairwiseDisjoint hK hz hsector hmn)
    hpm.1 hpn.1

/-- The union of the current physical pieces equals the physical fundamental
strip up to a null set. -/
theorem n07b_physicalPieces_ae_cover
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) :
    (⋃ m, physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))
      =ᵐ[volume] Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi := by
  have hcover : ∀ᵐ p ∂volume.restrict (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi),
      p ∈ ⋃ m, physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi) := by
    apply n07b_ae_physical_of_ae_pieces hK hz hsector
    intro m
    filter_upwards [ae_restrict_mem
      ((hK.domains z hz hsector m).1.measurableSet.inter
        (MeasurableSet.univ.prod measurableSet_Ioc))] with p hp
    exact mem_iUnion.mpr ⟨m, hp⟩
  have h := (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioc)).mp hcover
  filter_upwards [h] with p hp
  apply propext
  constructor
  · intro hmem
    obtain ⟨m, hm⟩ := mem_iUnion.mp hmem
    exact ⟨((hK.domains z hz hsector m).2.2.1 hm.1).1, hm.2.2⟩
  · exact hp

/-- A genuine physical integrable function has a summable family of actual
piece integrals. -/
theorem n07b_summable_integral_pieces
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {g : PolarPoint → ℝ}
    (hg : IntegrableOn g (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi)) :
    Summable (fun m => ∫ p in
      physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi), g p) := by
  have hsub : (⋃ m, physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) ⊆
      Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi := by
    intro p hp
    obtain ⟨m, hm⟩ := mem_iUnion.mp hp
    exact ⟨((hK.domains z hz hsector m).2.2.1 hm.1).1, hm.2.2⟩
  exact (hasSum_integral_iUnion
    (fun m => (hK.domains z hz hsector m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc))
    (n07b_physicalPieces_pairwiseDisjoint hK hz hsector) (hg.mono_set hsub)).summable

/-- The sum of the actual piece energies is the physical energy itself. -/
theorem n07b_tsum_integral_pieces
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {g : PolarPoint → ℝ}
    (hg : IntegrableOn g (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi)) :
    (∑' m, ∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi), g p) =
      ∫ p in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi, g p := by
  have hsub : (⋃ m, physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) ⊆
      Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi := by
    intro p hp
    obtain ⟨m, hm⟩ := mem_iUnion.mp hp
    exact ⟨((hK.domains z hz hsector m).2.2.1 hm.1).1, hm.2.2⟩
  have hsum := hasSum_integral_iUnion
    (fun m => (hK.domains z hz hsector m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc))
    (n07b_physicalPieces_pairwiseDisjoint hK hz hsector) (hg.mono_set hsub)
  exact hsum.tsum_eq.trans
    (setIntegral_congr_set (n07b_physicalPieces_ae_cover hK hz hsector))

/-- Piecewise domination by one genuine physical integrable energy gives
both square summability and the global bound needed by the source lift. -/
theorem n07b_summable_energy_of_piece_integral_bound
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {g : PolarPoint → ℝ}
    (hg : IntegrableOn g (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi))
    {e : ℕ → ℝ} (he : ∀ m, 0 ≤ e m)
    (hbound : ∀ m, e m ≤ ∫ p in
      physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi), g p) :
    Summable e ∧ (∑' m, e m) ≤ ∫ p in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi, g p := by
  have hgSum := n07b_summable_integral_pieces hK hz hsector hg
  have heSum := Summable.of_nonneg_of_le he hbound hgSum
  refine ⟨heSum, ?_⟩
  have h := Summable.tsum_le_tsum hbound heSum hgSum
  rw [n07b_tsum_integral_pieces hK hz hsector hg] at h
  exact h

end ContinuousFlexibility.Analysis
