import ContinuousFlexibility.Analysis.N07bReferenceMaterialSeeds
import ContinuousFlexibility.Analysis.N07bNormalizedDirectionChain
import ContinuousFlexibility.Radial.ReferenceColumnSmooth

/-!
# Actual reference transition geometry and its primitive fields

The transition maps, height ratio, source factor and transported directions
are the actual functions retained in the statement layer. Their mapping,
inverse and smoothness properties follow from the two actual chart systems.
The fifteen scalar primitive fields agree with the analysis normalizers,
direction components and reference multipliers used in the finite expansion.
No coefficient regularity or membership conclusion is an additional input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

section Geometry

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  (hK : N04PartA D S C K base ε)
  (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
  (hsref : stateSector S C.referenceState)
  (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)

include hK href hsref hz hs

theorem n07b_canonicalReferencePoint_mapsTo (m : ℕ) :
    MapsTo (canonicalReferencePoint C K z m) (physicalPieceOpen S K z m)
      (physicalPieceOpen S K (C.referenceState, 0) m) := by
  intro p hp
  exact (hK.charts (C.referenceState, 0) href hsref m).2.1
    ((hK.charts z hz hs m).1 hp)

theorem n07b_canonicalCurrentPoint_mapsTo (m : ℕ) :
    MapsTo (canonicalCurrentPoint C K z m) (physicalPieceOpen S K (C.referenceState, 0) m)
      (physicalPieceOpen S K z m) := by
  intro p hp
  exact (hK.charts z hz hs m).2.1
    ((hK.charts (C.referenceState, 0) href hsref m).1 hp)

theorem n07b_canonicalCurrentPoint_referencePoint (m : ℕ)
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K z m) :
    canonicalCurrentPoint C K z m (canonicalReferencePoint C K z m p) = p := by
  have hcur := hK.charts z hz hs m
  have hreference := hK.charts (C.referenceState, 0) href hsref m
  change K.inverseChart z m
    (K.chart (C.referenceState, 0) m
      (K.inverseChart (C.referenceState, 0) m (K.chart z m p))) = p
  rw [hreference.2.2.2.1 _ (hcur.1 hp), hcur.2.2.1 p hp]

theorem n07b_canonicalReferencePoint_currentPoint (m : ℕ)
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K (C.referenceState, 0) m) :
    canonicalReferencePoint C K z m (canonicalCurrentPoint C K z m p) = p := by
  have hcur := hK.charts z hz hs m
  have hreference := hK.charts (C.referenceState, 0) href hsref m
  change K.inverseChart (C.referenceState, 0) m
    (K.chart z m (K.inverseChart z m (K.chart (C.referenceState, 0) m p))) = p
  rw [hcur.2.2.2.1 _ (hreference.1 hp), hreference.2.2.1 p hp]

theorem n07b_canonicalReferencePoint_contDiffOn (m : ℕ) :
    ContDiffOn ℝ ∞ (canonicalReferencePoint C K z m) (physicalPieceOpen S K z m) := by
  change ContDiffOn ℝ ∞
    (K.inverseChart (C.referenceState, 0) m ∘ K.chart z m) (physicalPieceOpen S K z m)
  exact (hK.charts (C.referenceState, 0) href hsref m).2.2.2.2.2.1.comp
    (hK.charts z hz hs m).2.2.2.2.1 (hK.charts z hz hs m).1

theorem n07b_canonicalCurrentPoint_contDiffOn (m : ℕ) :
    ContDiffOn ℝ ∞ (canonicalCurrentPoint C K z m)
      (physicalPieceOpen S K (C.referenceState, 0) m) := by
  change ContDiffOn ℝ ∞
    (K.inverseChart z m ∘ K.chart (C.referenceState, 0) m)
      (physicalPieceOpen S K (C.referenceState, 0) m)
  exact (hK.charts z hz hs m).2.2.2.2.2.1.comp
    (hK.charts (C.referenceState, 0) href hsref m).2.2.2.2.1
    (hK.charts (C.referenceState, 0) href hsref m).1

theorem n07b_canonicalReferenceHeightRatio_contDiffOn (m : ℕ) :
    ContDiffOn ℝ ∞ (canonicalReferenceHeightRatio C K z m) (physicalPieceOpen S K z m) := by
  intro p hp
  have hΘ := (n07b_canonicalReferencePoint_contDiffOn hK href hsref hz hs m).contDiffAt
    ((hK.domains z hz hs m).1.mem_nhds hp)
  have hrefp := n07b_canonicalReferencePoint_mapsTo hK href hsref hz hs m hp
  have hr := (hK.boundary (C.referenceState, 0) href hsref m).2.2.2.2.1
    _ (subset_closure hrefp)
  have hc := (hK.boundary z hz hs m).2.2.2.2.1 p (subset_closure hp)
  exact ((hr.2.1.comp p hΘ).div hc.2.1 hc.2.2.2.ne').contDiffWithinAt

theorem n07b_canonicalReferenceSourceFactor_contDiffOn (m : ℕ) :
    ContDiffOn ℝ ∞ (canonicalReferenceSourceFactor C K z m) (physicalPieceOpen S K z m) := by
  intro p hp
  have hΘ := (n07b_canonicalReferencePoint_contDiffOn hK href hsref hz hs m).contDiffAt
    ((hK.domains z hz hs m).1.mem_nhds hp)
  have hrefp := n07b_canonicalReferencePoint_mapsTo hK href hsref hz hs m hp
  have hr := (hK.boundary (C.referenceState, 0) href hsref m).2.2.2.2.1
    _ (subset_closure hrefp)
  have hJ := (ContinuousFlexibility.contDiffAt_planeJacobian hr.1).abs hr.2.2.1
  exact ((hr.2.1.comp p hΘ).div (hJ.comp p hΘ)
    (abs_ne_zero.mpr hr.2.2.1)).contDiffWithinAt

/-- Both reference coordinate directions have their actual transported
smooth vector fields on the current piece. -/
theorem n07b_canonicalReferenceDirection_contDiffOn (m : ℕ) (e : PolarPoint) :
    ContDiffOn ℝ ∞
      (n07bReferenceDirection (canonicalCurrentPoint C K z m)
        (canonicalReferencePoint C K z m) e) (physicalPieceOpen S K z m) :=
  n07bReferenceDirection_contDiffOn (hK.domains z hz hs m).1
    (hK.domains (C.referenceState, 0) href hsref m).1
    (n07b_canonicalCurrentPoint_contDiffOn hK href hsref hz hs m)
    (n07b_canonicalReferencePoint_contDiffOn hK href hsref hz hs m)
    (n07b_canonicalReferencePoint_mapsTo hK href hsref hz hs m) e

/-- All three reference differential multipliers are actual smooth fields.
The globally flat quotient treats the apparent singularity at zero. -/
theorem n07b_canonicalReferenceSeedMultiplier_contDiffOn
    (hgeom : RadialProfileGeometry D) (m : ℕ) (k : Fin 3) :
    ContDiffOn ℝ ∞
      (n07bReferenceSeedMultiplier D.w (canonicalReferencePoint C K z m)
        (canonicalReferenceSourceFactor C K z m) k) (physicalPieceOpen S K z m) := by
  intro p hp
  have hΘ := (n07b_canonicalReferencePoint_contDiffOn hK href hsref hz hs m).contDiffAt
    ((hK.domains z hz hs m).1.mem_nhds hp)
  have hB := (n07b_canonicalReferenceSourceFactor_contDiffOn hK href hsref hz hs m).contDiffAt
    ((hK.domains z hz hs m).1.mem_nhds hp)
  have hwd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hgeom.2.2.1.1).2
  unfold n07bReferenceSeedMultiplier
  split_ifs
  · exact (hB.mul (hwd.contDiffAt.comp p hΘ.fst)).contDiffWithinAt
  · exact (hB.mul (hgeom.2.2.1.1.contDiffAt.comp p hΘ.fst)).contDiffWithinAt
  · exact (hB.mul
      ((reference_contDiff_flat_deriv_div hgeom.1 hgeom.2.2.1).contDiffAt.comp p hΘ.fst)).contDiffWithinAt

end Geometry

section PrimitiveIdentities

variable {S : PhysicalSpacesData} (D : ReferenceData) (T : MaterialData)
  (C : NonlinearGeometryData S) (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ)

theorem n07b_canonicalPrimitiveDirection_zero :
    canonicalPrimitiveDirection C K z m 0 = n07bInverseAngleVector (K.chart z m) := rfl

theorem n07b_canonicalPrimitiveDirection_one :
    canonicalPrimitiveDirection C K z m 1 =
      n07bReferenceDirection (canonicalCurrentPoint C K z m)
        (canonicalReferencePoint C K z m) (1, 0) := rfl

theorem n07b_canonicalPrimitiveDirection_two :
    canonicalPrimitiveDirection C K z m 2 =
      n07bReferenceDirection (canonicalCurrentPoint C K z m)
        (canonicalReferencePoint C K z m) (0, 1) := rfl

theorem n07b_canonicalMaterialNormalizer_eq (β : ℝ) :
    canonicalMaterialNormalizer T K z m β = n07bSourceNormalizer T K z m β := rfl

/-- All nine material direction fields are the existing actual component
and normalization-drift fields, including their signs. -/
theorem n07b_canonicalPrimitiveField_direction (i : Fin 3) (y : PolarPoint) :
    canonicalPrimitiveField D T C K z m (.inl (i, 0)) (n07bMaterialRadiusChart T y) =
        n07bMaterialDirectionV1 T (canonicalPrimitiveDirection C K z m i) y ∧
      canonicalPrimitiveField D T C K z m (.inl (i, 1)) (n07bMaterialRadiusChart T y) =
        n07bMaterialDirectionV2 T (canonicalPrimitiveDirection C K z m i) y ∧
      canonicalPrimitiveField D T C K z m (.inl (i, 2)) (n07bMaterialRadiusChart T y) =
        n07bMaterialDirectionDrift T K z m (canonicalPrimitiveDirection C K z m i) y :=
  ⟨rfl, rfl, rfl⟩

theorem n07b_canonicalPrimitiveField_source_initial :
    canonicalPrimitiveField D T C K z m (.inr (.inl 0)) =
      (fun x => n07bSourceNormalizer T K z m (3 / 4 : ℝ) x *
        (K.height z m x / |planeJacobian (K.chart z m) x|)) := rfl

theorem n07b_canonicalPrimitiveField_height_initial :
    canonicalPrimitiveField D T C K z m (.inr (.inl 1)) =
      (fun x => n07bSourceNormalizer T K z m (3 / 4 : ℝ) x *
        (K.height z m x)⁻¹) := rfl

theorem n07b_canonicalPrimitiveField_reference_initial :
    canonicalPrimitiveField D T C K z m (.inr (.inl 2)) =
      (fun x => n07bSourceNormalizer T K z m (3 / 4 : ℝ) x *
        canonicalReferenceHeightRatio C K z m x) := rfl

theorem n07b_canonicalPrimitiveField_reference_multiplier (k : Fin 3) :
    canonicalPrimitiveField D T C K z m (.inr (.inr k)) =
      n07bReferenceSeedMultiplier D.w (canonicalReferencePoint C K z m)
        (canonicalReferenceSourceFactor C K z m) k := by
  funext x
  unfold canonicalPrimitiveField n07bReferenceSeedMultiplier
  split_ifs <;> rfl

end PrimitiveIdentities

end ContinuousFlexibility.Analysis
