module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryTravelTower
public import ContinuousFlexibility.Analysis.JointMixedTransportCalculus
public import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Mixed spatial towers of the same stored travel chart

A fixed linear projection treats both coordinates together. The actual
radial and angular tower operations are iterated on the one strip tower;
no derivative order selects another chart, inverse, or neighborhood.
Freezing the physical point then gives the genuine parameter tower of
each actual mixed derivative. Its diagonal jets are exactly the spatial
mixed jets of the original joint tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

local instance n04NegativeGeometryActualTravelMixedStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hfield : N04bFieldRegularity D S C L base ε)
  (χ : ℕ → ℝ → ℝ)
  (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hcoeff : L.coefficients = returnCorrectedCoefficients D S C χ)
  (hflow : L.minusFlow = returnCorrectedMinusFlow S C χ)
  (hdiscFull : ∀ z ∈ stateNeighborhood S C base ε, ∀ m (p : PolarPoint),
    p.1 ∈ tsupport (deriv (χ m)) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
  (A : PolarPoint →L[ℝ] ℝ) (m : ℕ) (l h : ℝ)
  (hl : C.left m < l) (hh : h < C.right m)

/-- Either stored coordinate is obtained by taking `A` to be a projection. -/
def N01Properties.n04NegativeGeometryActualTravelScalar_stripJointTower :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        A (n04bActualTravelChart S C L (liftSectorParameter S C x.1) m x.2)) :=
  solveSmoothDirectionsPostcomp
    (hN.n04NegativeGeometryActualTravelChart_stripJointTower hS hT hfield χ hχ hχrange
      hcoeff hflow hdiscFull m l h hl hh) A

/-- All spatial orders are obtained from that same scalar strip tower. -/
def N01Properties.n04NegativeGeometryActualTravelMixed_stripJointTower (a b : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint => mixedDerivative a b
        (fun p => A (n04bActualTravelChart S C L (liftSectorParameter S C x.1) m p)) x.2) := by
  let J := hN.n04NegativeGeometryActualTravelScalar_stripJointTower hS hT hfield χ hχ hχrange
    hcoeff hflow hdiscFull A m l h hl hh
  have hV : IsOpen (Ioo l h ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hc : Convex ℝ (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ (univ : Set ℝ))) :=
    (sectorNeighborhood_convex S base ε ε).prod ((convex_Ioo l h).prod convex_univ)
  have hf (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
      ContDiffOn ℝ ∞
        (fun p => A (n04bActualTravelChart S C L (liftSectorParameter S C z) m p))
        (Ioo l h ×ˢ univ) := J.spatial_value_contDiffOn hV z hz
  have hzero : ∀ b : ℕ,
      SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
        (fun x : (StateDirections S × ℝ) × PolarPoint => mixedDerivative 0 b
          (fun p => A (n04bActualTravelChart S C L (liftSectorParameter S C x.1) m p)) x.2) := by
    intro b
    induction b with
    | zero =>
        apply J.congrOn
        intro x hx
        simp only [mixedDerivative, iteratedDeriv_zero]
    | succ b ih =>
        apply (ih.spatialAngularTower hV hc).congrOn
        intro x hx
        exact angularPartial_mixedDerivative_of_contDiffOn hV (hf x.1 hx.1) 0 b hx.2
  induction a with
  | zero => exact hzero b
  | succ a ih =>
      apply (ih.spatialRadialTower hV hc).congrOn
      intro x hx
      exact radialPartial_mixedDerivative_of_contDiffOn hV (hf x.1 hx.1) a b hx.2

/-- The genuine parameter tower at any fixed point of the original strip. -/
def N01Properties.n04NegativeGeometryActualTravelMixed_pointTower (a b : ℕ)
    (p : PolarPoint) (hp : p ∈ Ioo l h ×ˢ (univ : Set ℝ)) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun x => mixedDerivative a b
        (fun q => A (n04bActualTravelChart S C L (liftSectorParameter S C x) m q)) p) :=
  (hN.n04NegativeGeometryActualTravelMixed_stripJointTower hS hT hfield χ hχ hχrange
    hcoeff hflow hdiscFull A m l h hl hh a b).freezeSpatial
      (sectorNeighborhood_isOpen S base ε ε) p hp

/-- Any other genuine point tower of the same scalar agrees in every slot. -/
theorem N01Properties.n04NegativeGeometryActualTravelMixed_pointTower_eq
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ Ioo l h ×ˢ (univ : Set ℝ))
    (K : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun x => mixedDerivative a b
        (fun q => A (n04bActualTravelChart S C L (liftSectorParameter S C x) m q)) p))
    (k : ℕ) (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε)
    (v : Fin k → StateDirections S × ℝ) :
    K.D k x v =
      (hN.n04NegativeGeometryActualTravelMixed_stripJointTower hS hT hfield χ hχ hχrange
        hcoeff hflow hdiscFull A m l h hl hh a b).D k (x, p)
          (fun i => (v i, (0 : PolarPoint))) :=
  (hN.n04NegativeGeometryActualTravelMixed_stripJointTower hS hT hfield χ hχ hχrange
    hcoeff hflow hdiscFull A m l h hl hh a b).pointTower_eq_jointJet
      (sectorNeighborhood_isOpen S base ε ε) p hp K k x hx v

/-- Mixed differentiation of the actual value and of the original joint
jets gives the same diagonal parameter jets, at the same physical point. -/
theorem N01Properties.n04NegativeGeometryActualTravelMixed_diagonal
    (k a b : ℕ) (x w : StateDirections S × ℝ)
    (hx : x ∈ sectorNeighborhood S base ε ε)
    {p : PolarPoint} (hp : p ∈ Ioo l h ×ˢ (univ : Set ℝ)) :
    (hN.n04NegativeGeometryActualTravelMixed_stripJointTower hS hT hfield χ hχ hχrange
      hcoeff hflow hdiscFull A m l h hl hh a b).D k (x, p)
        (fun _ => (w, (0 : PolarPoint))) =
      jointMixedDiagonal
        (hN.n04NegativeGeometryActualTravelScalar_stripJointTower hS hT hfield χ hχ hχrange
          hcoeff hflow hdiscFull A m l h hl hh) k a b x w p := by
  let J := hN.n04NegativeGeometryActualTravelScalar_stripJointTower hS hT hfield χ hχ hχrange
    hcoeff hflow hdiscFull A m l h hl hh
  let K := hN.n04NegativeGeometryActualTravelMixed_stripJointTower hS hT hfield χ hχ hχrange
    hcoeff hflow hdiscFull A m l h hl hh a b
  have hU := sectorNeighborhood_isOpen S base ε ε
  have hV : IsOpen (Ioo l h ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hc : Convex ℝ (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ (univ : Set ℝ))) :=
    (sectorNeighborhood_convex S base ε ε).prod ((convex_Ioo l h).prod convex_univ)
  have hz : x + (0 : ℝ) • w ∈ sectorNeighborhood S base ε ε := by
    simpa only [zero_smul, add_zero] using hx
  have hK : iteratedDeriv k (fun t : ℝ => mixedDerivative a b
      (fun q => A (n04bActualTravelChart S C L (liftSectorParameter S C (x + t • w)) m q)) p) 0 =
        K.D k (x, p) (fun _ => (w, (0 : PolarPoint))) := by
    simpa only [jointMixedDiagonal, mixedDerivative, iteratedDeriv_zero, zero_smul, add_zero]
      using jointMixedDiagonal_eq_iteratedDeriv K hU hV hc k 0 0 x w hz hp
  have hJ := jointMixedDiagonal_eq_iteratedDeriv J hU hV hc k a b x w hz hp
  simp only [zero_smul, add_zero] at hJ
  exact hK.symm.trans hJ

end ContinuousFlexibility.Statements
