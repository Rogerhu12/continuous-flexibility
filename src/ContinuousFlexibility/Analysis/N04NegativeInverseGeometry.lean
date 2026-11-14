module

public import ContinuousFlexibility.Analysis.N04NegativeInverseContinuity
public import ContinuousFlexibility.Analysis.N04NegativeGeometryHeightTowers
public import ContinuousFlexibility.Analysis.N04NegativeGeometryPlanarParameterInverse
public import ContinuousFlexibility.Analysis.N04NegativeInverseImplicitIdentification
public import ContinuousFlexibility.Analysis.N04NegativeGeometrySpatialRegularity
public import ContinuousFlexibility.Analysis.N04RealizationLeadNegativeSplit
public import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph

/-!
# The actual negative inverse on fixed parameter and canonical domains

The forward chart is considered on its entire original physical component.
The actual inverse takes its values there even when the physical half-cut
moves with the state.  All identities concern the stored chosen functions.
No regularity of a different representative is substituted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable (W : N04RealizationStart)

/-- Every finite affine state slice of the stored inverse is jointly smooth.
The implicit theorem uses the fixed whole component, and therefore remains
valid at points whose moving physical half differs from the reference half. -/
theorem negativeInverse_contDiffOn_finiteAffine
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (m : ℕ) (side : Bool) (z₀ : StateDirections W.S × ℝ)
    (L : P →L[ℝ] (StateDirections W.S × ℝ)) :
    ContDiffOn ℝ ∞ (fun x : P × PolarPoint =>
      n04bActualNegativeInverse W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C (z₀ + L x.1)) m side x.2)
      (((fun p => z₀ + L p) ⁻¹' sectorNeighborhood W.S W.base W.ε W.ε) ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ)) := by
  apply n04NegativeGeometry_inverse_contDiffOn_finiteAffine
    (W.negativeChartJointTower m side)
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
    (isOpen_Ioo.prod isOpen_univ) (isOpen_Ioo.prod isOpen_univ)
    (fun x hx => W.negativeChart_jacobian_ne_zero m side hx.1 hx.2)
    (fun z hz => W.negativeChart_injOn_component m side hz)
    (fun x hx => W.negativeInverse_maps_component m side hx.1 hx.2)
    (fun x hx => W.negativeInverse_right m side hx.1 hx.2)

/-- The actual chosen inverse has one all-order joint directional tower
on the original sector neighborhood and its fixed canonical root strip. -/
def negativeInverseJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualNegativeInverse W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side x.2) :=
  n04NegativeInverse_jointTower (W.negativeChartJointTower m side)
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
    (isOpen_Ioo.prod isOpen_univ) (isOpen_Ioo.prod isOpen_univ)
    (W.negativeInverse_continuousOn m side)
    (fun x hx => W.negativeChart_jacobian_ne_zero m side hx.1 hx.2)
    (fun z hz => W.negativeChart_injOn_component m side hz)
    (fun x hx => W.negativeInverse_maps_component m side hx.1 hx.2)
    (fun x hx => W.negativeInverse_right m side hx.1 hx.2)

/-- Composition of the actual height tower with the actual inverse point.
The graph retains the original sector parameter, so every derivative
differentiates both the height and its moving argument. -/
def negativePulledHeightJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualNegativeHeight W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side
          (n04bActualNegativeInverse W.hT W.hS W.through03 W.field
            (liftSectorParameter W.S W.C x.1) m side x.2)) := by
  letI : LocallyConvexSpace ℝ (StateDirections W.S × ℝ) :=
    (sectorPairGrading_withSeminorms W.S).toLocallyConvexSpace
  let J := W.negativeInverseJointTower m side
  let P := smoothDirectionsLinearOn
    (ContinuousLinearMap.fst ℝ (StateDirections W.S × ℝ) PolarPoint) J.open_domain
  exact smoothDirections_realCompTVS (smoothDirectionsProd P J)
    (W.negativeHeightJointTower m side)
    (fun x hx => ⟨hx.1, W.negativeInverse_maps_component m side hx.1 hx.2⟩)

end ContinuousFlexibility.Analysis.N04RealizationStart

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- Affine canonical unit normalization of a genuine joint tower. -/
def n04NegativeInverse_canonicalUnitJointTower
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
  have hmap' : MapsTo (fun x => c + P x) (U ×ˢ unitStrip) (U ×ˢ Ω) := by
    intro x hx
    change c + P x ∈ U ×ˢ Ω
    rw [hpoint]
    exact ⟨hx.1, hmap hx.2⟩
  exact (J.compAffine P c (hU.prod (isOpen_Ioo.prod isOpen_univ)) hmap').congrOn
    (fun x _ => congrArg f (hpoint x))

namespace N04RealizationStart

variable (W : N04RealizationStart)

/-- The canonical unit point of a typed negative half lands in its exact
root strip, before applying its actual inverse. -/
theorem negativeCanonicalUnit_mapsTo
    (e : ℕ ≃ N04PieceIndex W.D) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) :
    MapsTo (canonicalUnitPoint (W.A e) k) unitStrip
      (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ)) := by
  let K := W.A e
  have hA := n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field e
  have hcan : canonicalOpen W.S K k =
      Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ) :=
    (n04bTypedAtlasData_negative_fields
    (C := W.C) (L := W.L) (z := (W.C.referenceState, 0)) e
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field)
    (n04bActualNegativeHeight W.hT W.hS W.through03 W.field)
    (n04bActualNegativeInverse W.hT W.hS W.through03 W.field)
    (n04bActualReferenceCut W.through03) k m side hi).2.1
  have hm : MapsTo (canonicalUnitPoint K k) unitStrip (canonicalOpen W.S K k) :=
    (n04NegativeGeometry_affine_unitPoint (K.left k) (K.right k)
      (hA.referenceBounds k).2.1).2.1
  intro p hp
  exact hcan ▸ hm hp

/-- Both actual normalized inverse atoms have genuine joint towers. -/
def negativeInverseAtomJointTower
    (e : ℕ ≃ N04PieceIndex W.D) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) (a : Atom) (ha : atomIsNegativeInverse a) :
    SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ unitStrip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        atom W.D W.U W.S W.C W.L (W.A e)
          (liftSectorParameter W.S W.C x.1) k a x.2) := by
  let K := W.A e
  have hU := sectorNeighborhood_isOpen W.S W.base W.ε W.ε
  let J := n04NegativeInverse_canonicalUnitJointTower K k hU
    (W.negativeInverseJointTower m side) (W.negativeCanonicalUnit_mapsTo e k m side hi)
  have hinverse (z : StateDirections W.S × ℝ) :
      K.inverseChart (liftSectorParameter W.S W.C z) k =
        n04bActualNegativeInverse W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side :=
    (n04bTypedAtlasData_negative_fields
      (C := W.C) (L := W.L) (z := liftSectorParameter W.S W.C z) e
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field)
      (n04bActualNegativeHeight W.hT W.hS W.through03 W.field)
      (n04bActualNegativeInverse W.hT W.hS W.through03 W.field)
      (n04bActualReferenceCut W.through03) k m side hi).2.2.2.2.1
  cases a <;> simp only [atomIsNegativeInverse] at ha
  · apply (J.comp_contDiff isOpen_univ
      (((contDiff_fst.sub contDiff_const).div_const (K.physicalRight k - K.physicalLeft k)) :
        ContDiff ℝ ∞ (fun p : PolarPoint =>
          (p.1 - K.physicalLeft k) / (K.physicalRight k - K.physicalLeft k))).contDiffOn
      (fun _ _ => mem_univ _)).congrOn
    intro x hx
    change (_ - K.physicalLeft k) / (K.physicalRight k - K.physicalLeft k) =
      ((K.inverseChart (liftSectorParameter W.S W.C x.1) k (canonicalUnitPoint K k x.2)).1 -
        K.physicalLeft k) / (K.physicalRight k - K.physicalLeft k)
    exact congrArg (fun p : PolarPoint =>
      (p.1 - K.physicalLeft k) / (K.physicalRight k - K.physicalLeft k))
      (congrFun (hinverse x.1) (canonicalUnitPoint K k x.2)).symm
  · let L : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint)
    let Jθ : SmoothDirections
        (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ unitStrip)
        (fun x : (StateDirections W.S × ℝ) × PolarPoint => L x) :=
      smoothDirectionsLinearOn L (hU.prod (isOpen_Ioo.prod isOpen_univ))
    apply ((smoothDirectionsProd J Jθ).comp_contDiff isOpen_univ
      ((contDiff_fst.snd.sub contDiff_snd) :
        ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => p.1.2 - p.2)).contDiffOn
      (fun _ _ => mem_univ _)).congrOn
    intro x hx
    change _ - x.2.2 =
      (K.inverseChart (liftSectorParameter W.S W.C x.1) k (canonicalUnitPoint K k x.2)).2 - x.2.2
    exact congrArg (fun p : PolarPoint => p.2 - x.2.2)
      (congrFun (hinverse x.1) (canonicalUnitPoint K k x.2)).symm

end N04RealizationStart

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

def negativeInverseAtomJointTower
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m)
    (a : Atom) (ha : atomIsNegativeInverse a) :
    SmoothDirections (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε ×ˢ unitStrip)
      (fun x : (StateDirections G.W.S × ℝ) × PolarPoint => G.atomFamily η a x.1 m x.2) := by
  let data : ∃ j : ℕ × Bool, G.e m = .inl j := (G.neg_iff_inl η m).mp hm
  let j : ℕ × Bool := data.choose
  have hi : G.e m = .inl j := data.choose_spec
  have hk : G.X.e₀ (G.negativeIndex j) = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  have haux : a ≠ .auxiliaryColumn := by
    intro he
    subst a
    cases ha
  apply (G.W.negativeInverseAtomJointTower G.X.e₀ (G.negativeIndex j) j.1 j.2 hk a ha).congrOn
  intro x hx
  exact (congrFun (G.negative_atomFamily η x.1 m j hi a haux) x.2).symm

def negativeInverseAtomMixedRegularity
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m)
    (a : Atom) (ha : atomIsNegativeInverse a) :
    MixedJetRegularity (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε) unitStrip
      (fun z => G.atomFamily η a z m) :=
  n04Realization_jointMixedRegularity (G.negativeInverseAtomJointTower η m hm a ha)
    (sectorNeighborhood_isOpen G.W.S G.W.base G.W.ε G.W.ε)
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex G.W.S G.W.base G.W.ε G.W.ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))

/-- The retained pulled height is the actual height at the actual inverse
point, with the original typed canonical normalization. -/
theorem negativePulledHeight_actual
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (z : Parameter G.W.S)
    (m : ℕ) (j : ℕ × Bool) (hi : G.e m = .inl j) (q : PolarPoint) :
    G.pulledHeight η z m q =
      n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C z) j.1 j.2
        (n04bActualNegativeInverse G.W.hT G.W.hS G.W.through03 G.W.field
          (liftSectorParameter G.W.S G.W.C z) j.1 j.2
          (canonicalUnitPoint (G.W.A G.X.e₀) (G.negativeIndex j) q)) := by
  let k := G.negativeIndex j
  let K := G.W.A G.X.e₀
  have hk : G.X.e₀ k = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  have hf := n04bTypedAtlasData_negative_fields
    (C := G.W.C) (L := G.W.L) (z := liftSectorParameter G.W.S G.W.C z) G.X.e₀
    (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualNegativeInverse G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualReferenceCut G.W.through03) k j.1 j.2 hk
  have hheight : K.height (liftSectorParameter G.W.S G.W.C z) k =
      n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C z) j.1 j.2 := hf.2.2.2.2.2
  have hinverse : K.inverseChart (liftSectorParameter G.W.S G.W.C z) k =
      n04bActualNegativeInverse G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C z) j.1 j.2 := hf.2.2.2.2.1
  exact (G.negative_pulledHeight η z m j hi q).trans
    ((congrFun hheight
      (K.inverseChart (liftSectorParameter G.W.S G.W.C z) k
        (canonicalUnitPoint K k q))).trans
      (congrArg (n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C z) j.1 j.2)
        (congrFun hinverse (canonicalUnitPoint K k q))))

def negativePulledHeightJointTower
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m) :
    SmoothDirections (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε ×ˢ unitStrip)
      (fun x : (StateDirections G.W.S × ℝ) × PolarPoint => G.pulledHeight η x.1 m x.2) := by
  let data : ∃ j : ℕ × Bool, G.e m = .inl j := (G.neg_iff_inl η m).mp hm
  let j : ℕ × Bool := data.choose
  have hi : G.e m = .inl j := data.choose_spec
  let k := G.negativeIndex j
  have hk : G.X.e₀ k = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  apply (n04NegativeInverse_canonicalUnitJointTower (G.W.A G.X.e₀) k
    (sectorNeighborhood_isOpen G.W.S G.W.base G.W.ε G.W.ε)
    (G.W.negativePulledHeightJointTower j.1 j.2)
    (G.W.negativeCanonicalUnit_mapsTo G.X.e₀ k j.1 j.2 hk)).congrOn
  intro x hx
  exact (G.negativePulledHeight_actual η x.1 m j hi x.2).symm

def negativePulledHeightMixedRegularity
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m) :
    MixedJetRegularity (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε) unitStrip
      (fun z => G.pulledHeight η z m) :=
  n04Realization_jointMixedRegularity (G.negativePulledHeightJointTower η m hm)
    (sectorNeighborhood_isOpen G.W.S G.W.base G.W.ε G.W.ε)
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex G.W.S G.W.base G.W.ε G.W.ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))

theorem negativePulledHeight_period
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : StateDirections G.W.S × ℝ}
    (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) {q : PolarPoint} (hq : q ∈ unitStrip) :
    G.pulledHeight η z m (q + (0, Real.pi)) = G.pulledHeight η z m q := by
  let data : ∃ j : ℕ × Bool, G.e m = .inl j := (G.neg_iff_inl η m).mp hm
  let j : ℕ × Bool := data.choose
  have hi : G.e m = .inl j := data.choose_spec
  let k := G.negativeIndex j
  have hk : G.X.e₀ k = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  let H : PolarPoint → ℝ := fun p =>
    n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field
      (liftSectorParameter G.W.S G.W.C z) j.1 j.2
      (n04bActualNegativeInverse G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C z) j.1 j.2 p)
  have hshift : canonicalUnitPoint (G.W.A G.X.e₀) k (q + (0, Real.pi)) =
      canonicalUnitPoint (G.W.A G.X.e₀) k q + (0, Real.pi) := by
    simp only [canonicalUnitPoint, Prod.fst_add, Prod.snd_add, add_zero, Prod.mk_add_mk]
  calc
    G.pulledHeight η z m (q + (0, Real.pi)) =
        H (canonicalUnitPoint (G.W.A G.X.e₀) k (q + (0, Real.pi))) :=
      G.negativePulledHeight_actual η z m j hi (q + (0, Real.pi))
    _ = H (canonicalUnitPoint (G.W.A G.X.e₀) k q + (0, Real.pi)) :=
      congrArg H hshift
    _ = H (canonicalUnitPoint (G.W.A G.X.e₀) k q) :=
      G.W.negativePulledHeight_period j.1 j.2 hz
        (G.W.negativeCanonicalUnit_mapsTo G.X.e₀ k j.1 j.2 hk hq)
    _ = G.pulledHeight η z m q := (G.negativePulledHeight_actual η z m j hi q).symm

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInverseJointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInverseJointTower

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverseAtomMixedRegularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverseAtomMixedRegularity

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativePulledHeightMixedRegularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativePulledHeightMixedRegularity
