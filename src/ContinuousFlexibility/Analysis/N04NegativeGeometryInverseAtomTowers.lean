import ContinuousFlexibility.Analysis.N04NegativeGeometryCanonicalUnitTowers

/-!
# Current negative inverse atoms and pulled-height mixed regularity

The actual inverse-point tower gives both normalized inverse-coordinate
atoms. The actual pulled-height tower and the retained-negative-atlas
identities give the current gauge families for every auxiliary column.
All mixed regularity comes from these same joint towers.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

def negativeInverseGeometryAtom : Atom → Prop
  | .inverseRadial | .inverseAngleDefect => True
  | _ => False

namespace N04RealizationStart

variable (W : N04RealizationStart)

/-- The two literal inverse-coordinate atoms use the original canonical
unit point and the original physical normalization length. -/
def negativeInverseAtomJointTower
    (e : ℕ ≃ N04PieceIndex W.D) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) (a : Atom) (ha : negativeInverseGeometryAtom a) :
    SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ unitStrip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        atom W.D W.U W.S W.C W.L (W.A e)
          (liftSectorParameter W.S W.C x.1) k a x.2) := by
  let K := W.A e
  let J := W.negativeInverseUnitJointTower e k m side hi
  have hO : IsOpen (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ unitStrip) :=
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε).prod
      (isOpen_Ioo.prod isOpen_univ)
  cases a <;> simp only [negativeInverseGeometryAtom] at ha
  · exact J.comp_contDiff isOpen_univ
      (((contDiff_fst.sub contDiff_const).div_const
        (K.physicalRight k - K.physicalLeft k)) :
        ContDiff ℝ ∞ (fun p : PolarPoint =>
          (p.1 - K.physicalLeft k) / (K.physicalRight k - K.physicalLeft k))).contDiffOn
      (fun _ _ => mem_univ _)
  · let L : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint)
    let Jθ := smoothDirectionsLinearOn L hO
    exact (smoothDirectionsProd J Jθ).comp_contDiff isOpen_univ
      ((contDiff_fst.snd.sub contDiff_snd) :
        ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => p.1.2 - p.2)).contDiffOn
      (fun _ _ => mem_univ _)

end N04RealizationStart

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

def negativeInverseAtomJointTower
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m)
    (a : Atom) (ha : negativeInverseGeometryAtom a) :
    SmoothDirections (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε ×ˢ unitStrip)
      (fun x : (StateDirections G.W.S × ℝ) × PolarPoint => G.atomFamily η a x.1 m x.2) := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
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
    (a : Atom) (ha : negativeInverseGeometryAtom a) :
    MixedJetRegularity (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε) unitStrip
      (fun z => G.atomFamily η a z m) :=
  n04Realization_jointMixedRegularity (G.negativeInverseAtomJointTower η m hm a ha)
    (sectorNeighborhood_isOpen G.W.S G.W.base G.W.ε G.W.ε)
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex G.W.S G.W.base G.W.ε G.W.ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))

/-- The gauge's literal pulled height, independent of the auxiliary
column on a retained negative piece. -/
def negativePulledHeightJointTower
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m) :
    SmoothDirections (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε ×ˢ unitStrip)
      (fun x : (StateDirections G.W.S × ℝ) × PolarPoint => G.pulledHeight η x.1 m x.2) := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  have hk : G.X.e₀ (G.negativeIndex j) = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  apply (G.W.negativePulledHeightJointTower G.X.e₀ (G.negativeIndex j) j.1 j.2 hk).congrOn
  intro x hx
  exact (G.negative_pulledHeight η x.1 m j hi x.2).symm

def negativePulledHeightMixedRegularity
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m) :
    MixedJetRegularity (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε) unitStrip
      (fun z => G.pulledHeight η z m) :=
  n04Realization_jointMixedRegularity (G.negativePulledHeightJointTower η m hm)
    (sectorNeighborhood_isOpen G.W.S G.W.base G.W.ε G.W.ε)
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex G.W.S G.W.base G.W.ε G.W.ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverseAtomMixedRegularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverseAtomMixedRegularity

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativePulledHeightMixedRegularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativePulledHeightMixedRegularity
