import ContinuousFlexibility.Analysis.N04PieceData
import ContinuousFlexibility.Analysis.N04LiouvilleCharts
import ContinuousFlexibility.Blueprint.Statements
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# The reference Liouville atlas on the actual sign pieces

The geometry in N04PartA is realized by oriented affine coordinates on
the actual physical pieces and the positive reference Liouville factor.
The atlas is fixed throughout the state neighborhood, so its normalization
holds on the whole radial line. Its remaining operator fields are the
actual principal-density, potential, and divided-difference formulas for
this coordinate and height change.

This proves the geometric part of the coordinate stage. It does not assert
that these reference coordinates give the characteristic Tricomi normal
form or the transmission identity required by N04PartB.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- The actual principal density after the oriented affine coordinate
change and reference Liouville multiplication. -/
def n04CanonicalAtlasCoefficients (D : ReferenceData) (S : PhysicalSpacesData)
    (L : ReturnCorrectionData S) (P : N04PieceData)
    (z : AnnularState S × ℝ) (m : ℕ) : SymmetricCoefficients :=
  let inverse := n04UnitInverseChart (P.left m) (P.right m) (P.reversed m)
  let height := n04LiouvilleHeight D.w (P.left m) (P.right m)
  let slope := n04UnitSlope (P.left m) (P.right m) (P.reversed m)
  { a := fun p => height (inverse p) ^ 2 * |slope| * (L.coefficients z).a (inverse p)
    b := fun p => height (inverse p) ^ 2 * slope / |slope| *
      (L.coefficients z).b (inverse p)
    c := fun p => height (inverse p) ^ 2 / |slope| * (L.coefficients z).c (inverse p) }

/-- The zero-order term obtained by applying the physical divergence
expression to the reference height factor itself. -/
def n04CanonicalAtlasPotential (D : ReferenceData) (S : PhysicalSpacesData)
    (L : ReturnCorrectionData S) (P : N04PieceData)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) : ℝ :=
  let x := n04UnitInverseChart (P.left m) (P.right m) (P.reversed m) p
  let height := n04LiouvilleHeight D.w (P.left m) (P.right m)
  let slope := n04UnitSlope (P.left m) (P.right m) (P.reversed m)
  (if P.positive m then -1 else (1 : ℝ)) * height x / |slope| *
    divergenceOperator (L.coefficients z) height x

/-- The actual difference quotient of the transformed principal densities.
Regularity of this quotient at a boundary is a further normal-form property,
not part of the geometric assertion proved here. -/
def n04CanonicalAtlasDividedDifference (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (P : N04PieceData)
    (z : AnnularState S × ℝ) (m : ℕ) : SymmetricCoefficients :=
  let current := n04CanonicalAtlasCoefficients D S L P z m
  let reference := n04CanonicalAtlasCoefficients D S L P (C.referenceState, 0) m
  { a := fun p => (current.a p - reference.a p) / (p.1 * (1 - p.1)) ^ 3
    b := fun p => (current.b p - reference.b p) / (p.1 * (1 - p.1)) ^ 3
    c := fun p => (current.c p - reference.c p) / (p.1 * (1 - p.1)) ^ 3 }

/-- Fixed reference geometry on the actual oriented sign pieces. -/
def n04CanonicalAtlas (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (P : N04PieceData) : CanonicalData S where
  left := fun _ => 0
  right := fun _ => 1
  physicalLeft := P.left
  physicalRight := P.right
  cell := P.cell
  positive := P.positive
  chart := fun _ m => n04UnitChart (P.left m) (P.right m) (P.reversed m)
  inverseChart := fun _ m => n04UnitInverseChart (P.left m) (P.right m) (P.reversed m)
  height := fun _ m => n04LiouvilleHeight D.w (P.left m) (P.right m)
  coefficients := n04CanonicalAtlasCoefficients D S L P
  potential := n04CanonicalAtlasPotential D S L P
  dividedDifference := n04CanonicalAtlasDividedDifference D S C L P
  cutPair := P.cutPair
  cutRadius := fun _ => 1
  normalizationRegion := univ

theorem n04CanonicalAtlas_physicalPieceOpen (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (P : N04PieceData) (m : ℕ) :
    physicalPieceOpen S (n04CanonicalAtlas D S C L P) m =
      Ioo (P.left m) (P.right m) ×ˢ (univ : Set ℝ) := rfl

theorem n04CanonicalAtlas_canonicalOpen (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (P : N04PieceData) (m : ℕ) :
    canonicalOpen S (n04CanonicalAtlas D S C L P) m =
      Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := rfl

/-- All geometric clauses of Part A, on the original state neighborhood.
No property of the return correction is needed for this fixed atlas. -/
theorem n04CanonicalAtlas_partA {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {P : N04PieceData}
    {base : ℕ} {ε : ℝ} (hD : RadialProfileGeometry D) (hP : N04PieceGeometry D P) :
    N04PartA D S C (n04CanonicalAtlas D S C L P) base ε := by
  rcases hP with ⟨hbound, hpositive, hnegative, E, hE, hcover⟩
  have hlr (m : ℕ) : P.left m < P.right m := (hbound m).2.1
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  have hwp (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Icc (P.left m) (P.right m)) :
      0 < D.w p.1 :=
    hD.2.2.2.2.1 p.1
      ⟨(hbound m).1.trans_le hp.1, hp.2.trans_lt (hbound m).2.2⟩
  unfold N04PartA
  refine ⟨isOpen_univ, subset_univ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz hsector m p hp hnormal
    exact ⟨rfl, rfl⟩
  · intro m
    refine ⟨hlr m, by norm_num, ?_⟩
    intro r hr
    exact ⟨(hbound m).1.trans hr.1, hr.2.trans (hbound m).2.2⟩
  · exact hpositive
  · exact hnegative
  · exact ⟨E, hE.measure_zero volume, hcover⟩
  · intro z hz hsector m
    refine ⟨n04UnitChart_mapsTo (hlr m) (P.reversed m),
      n04UnitInverseChart_mapsTo (hlr m) (P.reversed m), ?_, ?_,
      (contDiff_n04UnitChart (P.left m) (P.right m) (P.reversed m)).contDiffOn,
      (contDiff_n04UnitInverseChart (P.left m) (P.right m) (P.reversed m)).contDiffOn,
      ?_, ?_⟩
    · intro p hp
      exact n04UnitInverseChart_chart (hlr m) (P.reversed m) p
    · intro p hp
      exact n04UnitChart_inverseChart (hlr m) (P.reversed m) p
    · intro p hp
      exact (contDiffAt_n04LiouvilleHeight (p := p) hw (hlr m)
        (hwp m p ⟨hp.1.1.le, hp.1.2.le⟩)).contDiffWithinAt
    · intro p hp
      exact ⟨n04LiouvilleHeight_pos (p := p) (hlr m) (hwp m p ⟨hp.1.1.le, hp.1.2.le⟩),
        n04UnitChart_planeJacobian_ne_zero (hlr m) (P.reversed m) p,
        n04UnitChart_lift (P.left m) (P.right m) (P.reversed m) Real.pi p,
        n04LiouvilleHeight_lift D.w (P.left m) (P.right m) Real.pi p⟩
  · intro z hz hsector m p hp
    exact ⟨(contDiff_n04UnitChart (P.left m) (P.right m) (P.reversed m)).contDiffAt,
      contDiffAt_n04LiouvilleHeight (p := p) hw (hlr m) (hwp m p hp),
      n04UnitChart_planeJacobian_ne_zero (hlr m) (P.reversed m) p,
      n04LiouvilleHeight_pos (p := p) (hlr m) (hwp m p hp)⟩
  · intro z hz hsector m p hp
    exact ⟨n04UnitChart_reflection (P.left m) (P.right m) (P.reversed m) p,
      n04LiouvilleHeight_reflection D.w (P.left m) (P.right m) p,
      n04UnitChart_planeJacobian_reflection (P.left m) (P.right m) (P.reversed m) p⟩
  · intro z hz hsector m p hp
    exact n04UnitInverseChart_reflection (P.left m) (P.right m) (P.reversed m) p

/-- The named negative pairs retain their physical cut and the common unit
canonical radius. This is only the static cut-pair clause of Part B. -/
theorem n04CanonicalAtlas_cutPairs {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {P : N04PieceData}
    (hP : N04NegativeCutPairs C P) :
    ∀ m,
      (n04CanonicalAtlas D S C L P).positive ((n04CanonicalAtlas D S C L P).cutPair m).1 = false ∧
      (n04CanonicalAtlas D S C L P).positive ((n04CanonicalAtlas D S C L P).cutPair m).2 = false ∧
      (n04CanonicalAtlas D S C L P).physicalLeft ((n04CanonicalAtlas D S C L P).cutPair m).1 = C.left m ∧
      (n04CanonicalAtlas D S C L P).physicalRight ((n04CanonicalAtlas D S C L P).cutPair m).2 = C.right m ∧
      (n04CanonicalAtlas D S C L P).physicalRight ((n04CanonicalAtlas D S C L P).cutPair m).1 =
        (n04CanonicalAtlas D S C L P).physicalLeft ((n04CanonicalAtlas D S C L P).cutPair m).2 ∧
      0 < (n04CanonicalAtlas D S C L P).cutRadius m ∧
      (n04CanonicalAtlas D S C L P).left ((n04CanonicalAtlas D S C L P).cutPair m).1 = 0 ∧
      (n04CanonicalAtlas D S C L P).left ((n04CanonicalAtlas D S C L P).cutPair m).2 = 0 ∧
      (n04CanonicalAtlas D S C L P).right ((n04CanonicalAtlas D S C L P).cutPair m).1 =
        (n04CanonicalAtlas D S C L P).cutRadius m ∧
      (n04CanonicalAtlas D S C L P).right ((n04CanonicalAtlas D S C L P).cutPair m).2 =
        (n04CanonicalAtlas D S C L P).cutRadius m := by
  intro m
  rcases hP m with ⟨hpos₁, hpos₂, hrev₁, hrev₂, hleft, hright, hcut₁, hcut₂⟩
  exact ⟨hpos₁, hpos₂, hleft, hright, hcut₁.trans hcut₂.symm, by norm_num,
    rfl, rfl, rfl, rfl⟩

end ContinuousFlexibility.Analysis
