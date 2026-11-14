module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryJacobianTowers
public import ContinuousFlexibility.Analysis.N04NegativeGeometrySpatialRegularity

/-!
# The six physical negative geometry atoms on the fixed unit strip

The fixed physical unit map takes the reference half into its original
component. Affine pullback of the actual joint chart, height and Jacobian
towers therefore gives the literal six physical atoms of the gauge atlas.
The two inverse-coordinate atoms are treated on their canonical domain.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

def negativePhysicalGeometryAtom : Atom → Prop
  | .chartRadial | .chartAngleDefect | .height | .heightInverse
  | .jacobian | .jacobianInverse => True
  | _ => False

/-- The physical unit pullback is a single affine substitution in the
joint variables, retaining the original parameter neighborhood. -/
def n04NegativeGeometry_physicalUnitJointTower
    {X F : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {S : PhysicalSpacesData} (K : CanonicalData S) (k : ℕ)
    {U : Set X} {Ω : Set PolarPoint} {f : X × PolarPoint → F}
    (hU : IsOpen U) (J : SmoothDirections (U ×ˢ Ω) f)
    (hmap : MapsTo (physicalUnitPoint K k) unitStrip Ω) :
    SmoothDirections (U ×ˢ unitStrip)
      (fun x : X × PolarPoint => f (x.1, physicalUnitPoint K k x.2)) := by
  let Q : PolarPoint →L[ℝ] PolarPoint :=
    ((K.physicalRight k - K.physicalLeft k) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let P : (X × PolarPoint) →L[ℝ] X × PolarPoint :=
    (ContinuousLinearMap.fst ℝ X PolarPoint).prod
      (Q.comp (ContinuousLinearMap.snd ℝ X PolarPoint))
  let c : X × PolarPoint := (0, (K.physicalLeft k, 0))
  have hpoint (x : X × PolarPoint) :
      c + P x = (x.1, physicalUnitPoint K k x.2) := by
    simp only [c, P, Q, physicalUnitPoint, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_apply, smul_eq_mul,
      Prod.mk_add_mk, zero_add]
  have hMaps : MapsTo (fun x => c + P x) (U ×ˢ unitStrip) (U ×ˢ Ω) := by
    intro x hx
    change c + P x ∈ U ×ˢ Ω
    rw [hpoint]
    exact ⟨hx.1, hmap hx.2⟩
  exact (J.compAffine P c (hU.prod (isOpen_Ioo.prod isOpen_univ)) hMaps).congrOn
    (fun x _ => congrArg f (hpoint x))

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

namespace N04RealizationStart

variable (W : N04RealizationStart)

set_option diagnostics true in
/-- The literal six physical atoms have joint parameter and unit-point
towers. The typed negative index and all normalizations are unchanged. -/
def negativePhysicalAtomJointTower
    (e : ℕ ≃ N04PieceIndex W.D) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) (a : Atom) (ha : negativePhysicalGeometryAtom a) :
    SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ unitStrip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        atom W.D W.U W.S W.C W.L (W.A e)
          (liftSectorParameter W.S W.C x.1) k a x.2) := by
  let K := W.A e
  let U := sectorNeighborhood W.S W.base W.ε W.ε
  have hU : IsOpen U := sectorNeighborhood_isOpen W.S W.base W.ε W.ε
  have hA := n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field e
  have hmap : MapsTo (physicalUnitPoint K k) unitStrip
      (Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) := by
    intro p hp
    apply n04NegativeGeometry_referenceHalf_subset_component
      W.hT W.hS W.through03 W.field e k m side hi
    exact (n04NegativeGeometry_affine_unitPoint (K.physicalLeft k) (K.physicalRight k)
      (hA.referenceBounds k).1).2.1 hp
  have hchart (z : StateDirections W.S × ℝ) :
      K.chart (liftSectorParameter W.S W.C z) k =
        n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side :=
    (n04bTypedAtlasData_negative_fields
      (C := W.C) (L := W.L) (z := liftSectorParameter W.S W.C z) e
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field)
      (n04bActualNegativeHeight W.hT W.hS W.through03 W.field)
      (n04bActualNegativeInverse W.hT W.hS W.through03 W.field)
      (n04bActualReferenceCut W.through03) k m side hi).2.2.2.1
  have hheight (z : StateDirections W.S × ℝ) :
      K.height (liftSectorParameter W.S W.C z) k =
        n04bActualNegativeHeight W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side :=
    (n04bTypedAtlasData_negative_fields
      (C := W.C) (L := W.L) (z := liftSectorParameter W.S W.C z) e
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field)
      (n04bActualNegativeHeight W.hT W.hS W.through03 W.field)
      (n04bActualNegativeInverse W.hT W.hS W.through03 W.field)
      (n04bActualReferenceCut W.through03) k m side hi).2.2.2.2.2
  let JC := n04NegativeGeometry_physicalUnitJointTower K k hU
    (W.negativeChartJointTower m side) hmap
  let JH := n04NegativeGeometry_physicalUnitJointTower K k hU
    (W.negativeHeightJointTower m side) hmap
  let JHI := n04NegativeGeometry_physicalUnitJointTower K k hU
    (W.negativeHeightInverseJointTower m side) hmap
  let JJ := n04NegativeGeometry_physicalUnitJointTower K k hU
    (W.negativeAbsJacobianJointTower m side) hmap
  let JJI := n04NegativeGeometry_physicalUnitJointTower K k hU
    (W.negativeJacobianInverseJointTower m side) hmap
  cases a <;> simp only [negativePhysicalGeometryAtom] at ha
  · apply (JC.comp_contDiff isOpen_univ
      (((contDiff_fst.sub contDiff_const).div_const (K.right k - K.left k)) :
        ContDiff ℝ ∞ (fun p : PolarPoint =>
          (p.1 - K.left k) / (K.right k - K.left k))).contDiffOn
      (fun _ _ => mem_univ _)).congrOn
    intro x hx
    exact congrArg (fun f : PolarPoint → PolarPoint =>
      ((f (physicalUnitPoint K k x.2)).1 - K.left k) / (K.right k - K.left k))
      (hchart x.1).symm
  · let L : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint)
    let Jθ : SmoothDirections (U ×ˢ unitStrip)
        (fun x : (StateDirections W.S × ℝ) × PolarPoint => L x) :=
      smoothDirectionsLinearOn L (hU.prod (isOpen_Ioo.prod isOpen_univ))
    apply ((smoothDirectionsProd JC Jθ).comp_contDiff isOpen_univ
      ((contDiff_fst.snd.sub contDiff_snd) :
        ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => p.1.2 - p.2)).contDiffOn
      (fun _ _ => mem_univ _)).congrOn
    intro x hx
    exact congrArg (fun f : PolarPoint → PolarPoint =>
      (f (physicalUnitPoint K k x.2)).2 - x.2.2) (hchart x.1).symm
  · apply JH.congrOn
    intro x hx
    exact (congrFun (hheight x.1) (physicalUnitPoint K k x.2)).symm
  · apply JHI.congrOn
    intro x hx
    exact congrArg (fun t : ℝ => t⁻¹)
      (congrFun (hheight x.1) (physicalUnitPoint K k x.2)).symm
  · apply JJ.congrOn
    intro x hx
    exact congrArg (fun f : PolarPoint → PolarPoint =>
      |planeJacobian f (physicalUnitPoint K k x.2)|) (hchart x.1).symm
  · apply JJI.congrOn
    intro x hx
    exact congrArg (fun f : PolarPoint → PolarPoint =>
      |planeJacobian f (physicalUnitPoint K k x.2)|⁻¹) (hchart x.1).symm

end N04RealizationStart

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

def negativePhysicalAtomJointTower
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m)
    (a : Atom) (ha : negativePhysicalGeometryAtom a) :
    SmoothDirections (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε ×ˢ unitStrip)
      (fun x : (StateDirections G.W.S × ℝ) × PolarPoint => G.atomFamily η a x.1 m x.2) := by
  classical
  have hnegative := (G.neg_iff_inl η m).mp hm
  let j := hnegative.choose
  have hi := hnegative.choose_spec
  have hk : G.X.e₀ (G.negativeIndex j) = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  have haux : a ≠ .auxiliaryColumn := by
    intro he
    subst a
    cases ha
  apply (G.W.negativePhysicalAtomJointTower G.X.e₀ (G.negativeIndex j) j.1 j.2 hk a ha).congrOn
  intro x hx
  exact (congrFun (G.negative_atomFamily η x.1 m j hi a haux) x.2).symm

def negativePhysicalAtomMixedRegularity
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m)
    (a : Atom) (ha : negativePhysicalGeometryAtom a) :
    MixedJetRegularity (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε) unitStrip
      (fun z => G.atomFamily η a z m) :=
  n04Realization_jointMixedRegularity (G.negativePhysicalAtomJointTower η m hm a ha)
    (sectorNeighborhood_isOpen G.W.S G.W.base G.W.ε G.W.ε)
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex G.W.S G.W.base G.W.ε G.W.ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativePhysicalAtomMixedRegularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativePhysicalAtomMixedRegularity
