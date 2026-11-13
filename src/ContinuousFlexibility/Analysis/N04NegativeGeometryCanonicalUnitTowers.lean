import ContinuousFlexibility.Analysis.N04NegativeGeometryInverseTowers
import ContinuousFlexibility.Analysis.N04NegativeGeometrySpatialRegularity

/-!
# Actual negative inverse and pulled height on the canonical unit strip

The same fixed affine unit map is applied to the constructed root-strip
towers. The typed atlas identities then identify the resulting functions
with the stored inverse and its pulled height, without changing the
reference normalization or the parameter neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency true

/-- Affine pullback by the literal canonical unit point. -/
def n04NegativeGeometry_canonicalUnitJointTower
    {X F : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {S : PhysicalSpacesData} (K : CanonicalData S) (k : ℕ)
    {U : Set X} {Ω : Set PolarPoint} {f : X × PolarPoint → F}
    (hU : IsOpen U) (J : SmoothDirections (U ×ˢ Ω) f)
    (hmap : MapsTo (canonicalUnitPoint K k) unitStrip Ω) :
    SmoothDirections (U ×ˢ unitStrip)
      (fun x : X × PolarPoint => f (x.1, canonicalUnitPoint K k x.2)) := by
  let Q : PolarPoint →L[ℝ] PolarPoint :=
    ((K.right k - K.left k) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let P : (X × PolarPoint) →L[ℝ] X × PolarPoint :=
    (ContinuousLinearMap.fst ℝ X PolarPoint).prod
      (Q.comp (ContinuousLinearMap.snd ℝ X PolarPoint))
  let c : X × PolarPoint := (0, (K.left k, 0))
  have hpoint (x : X × PolarPoint) :
      c + P x = (x.1, canonicalUnitPoint K k x.2) := by
    simp only [c, P, Q, canonicalUnitPoint, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_apply, smul_eq_mul,
      Prod.mk_add_mk, zero_add]
  have hMaps : MapsTo (fun x => c + P x) (U ×ˢ unitStrip) (U ×ˢ Ω) := by
    intro x hx
    rw [hpoint]
    exact ⟨hx.1, hmap hx.2⟩
  exact (J.compAffine P c (hU.prod (isOpen_Ioo.prod isOpen_univ)) hMaps).congrOn
    (fun x _ => congrArg f (hpoint x))

namespace N04RealizationStart

variable (W : N04RealizationStart)

theorem negativeCanonicalUnit_mapsTo
    (e : ℕ ≃ N04PieceIndex W.D) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) :
    MapsTo (canonicalUnitPoint (W.A e) k) unitStrip
      (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ) := by
  have hA := n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field e
  have hf := n04bTypedAtlasData_negative_fields
    (C := W.C) (L := W.L) (z := (W.C.referenceState, 0)) e
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field)
    (n04bActualNegativeHeight W.hT W.hS W.through03 W.field)
    (n04bActualNegativeInverse W.hT W.hS W.through03 W.field)
    (n04bActualReferenceCut W.through03) k m side hi
  have hcan : canonicalOpen W.S (W.A e) k =
      Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ) := hf.2.1
  rw [← hcan]
  exact (n04NegativeGeometry_affine_unitPoint ((W.A e).left k) ((W.A e).right k)
    (hA.referenceBounds k).2.1).2.1

/-- The actual inverse at the same normalized canonical point. -/
def negativeInverseUnitJointTower
    (e : ℕ ≃ N04PieceIndex W.D) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) :
    SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ unitStrip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        (W.A e).inverseChart (liftSectorParameter W.S W.C x.1) k
          (canonicalUnitPoint (W.A e) k x.2)) := by
  apply (n04NegativeGeometry_canonicalUnitJointTower (W.A e) k
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
    (W.negativeInverseJointTower m side)
    (W.negativeCanonicalUnit_mapsTo e k m side hi)).congrOn
  intro x hx
  have hf := n04bTypedAtlasData_negative_fields
    (C := W.C) (L := W.L) (z := liftSectorParameter W.S W.C x.1) e
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field)
    (n04bActualNegativeHeight W.hT W.hS W.through03 W.field)
    (n04bActualNegativeInverse W.hT W.hS W.through03 W.field)
    (n04bActualReferenceCut W.through03) k m side hi
  exact (congrFun hf.2.2.2.2.1 (canonicalUnitPoint (W.A e) k x.2)).symm

private theorem negativePulledHeight_eq_actual
    (e : ℕ ≃ N04PieceIndex W.D) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) (z : AnnularState W.S × ℝ) (q : PolarPoint) :
    (W.A e).height z k ((W.A e).inverseChart z k q) =
      n04bActualNegativeHeight W.hT W.hS W.through03 W.field z m side
        (n04bActualNegativeInverse W.hT W.hS W.through03 W.field z m side q) := by
  have hf := n04bTypedAtlasData_negative_fields
    (C := W.C) (L := W.L) (z := z) e
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field)
    (n04bActualNegativeHeight W.hT W.hS W.through03 W.field)
    (n04bActualNegativeInverse W.hT W.hS W.through03 W.field)
    (n04bActualReferenceCut W.through03) k m side hi
  exact (congrFun hf.2.2.2.2.2 ((W.A e).inverseChart z k q)).trans
    (congrArg (n04bActualNegativeHeight W.hT W.hS W.through03 W.field z m side)
      (congrFun hf.2.2.2.2.1 q))

/-- The same typed negative height pulled back by the same typed inverse. -/
def negativePulledHeightJointTower
    (e : ℕ ≃ N04PieceIndex W.D) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) :
    SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ unitStrip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        (W.A e).height (liftSectorParameter W.S W.C x.1) k
          ((W.A e).inverseChart (liftSectorParameter W.S W.C x.1) k
            (canonicalUnitPoint (W.A e) k x.2))) := by
  let J : SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ unitStrip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualNegativeHeight W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side
          (n04bActualNegativeInverse W.hT W.hS W.through03 W.field
            (liftSectorParameter W.S W.C x.1) m side (canonicalUnitPoint (W.A e) k x.2))) :=
    n04NegativeGeometry_canonicalUnitJointTower (W.A e) k
      (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
      (W.negativePulledHeightRootJointTower m side)
      (W.negativeCanonicalUnit_mapsTo e k m side hi)
  exact J.congrOn (fun x _ =>
    (W.negativePulledHeight_eq_actual e k m side hi
      (liftSectorParameter W.S W.C x.1) (canonicalUnitPoint (W.A e) k x.2)).symm)

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativePulledHeightJointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativePulledHeightJointTower
