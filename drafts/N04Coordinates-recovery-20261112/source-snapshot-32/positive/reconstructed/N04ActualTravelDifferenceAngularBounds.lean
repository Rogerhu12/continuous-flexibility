import ContinuousFlexibility.Analysis.N04ActualTravelStripTower
import ContinuousFlexibility.Analysis.N04TravelCircleUniformBounds
import ContinuousFlexibility.Analysis.N04bReferenceActualTravel
import ContinuousFlexibility.Analysis.N01TransportAngularInterpolation

/-!
# Pure angular bounds for the actual first-integral difference

The reference slice is subtracted from the already constructed joint
tower. Its exact optical formula cancels the affine part of the same
circle decoder. Selector-uniform interpolation consequently retains
the original sample-height factor at every angular order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

local instance n04ActualAngularDifferenceStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hfield : N04bFieldRegularity D S C L base ε)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hcoeff : L.coefficients = returnCorrectedCoefficients D S C χ)
  (hflow : L.minusFlow = returnCorrectedMinusFlow S C χ)
  (hdiscFull : ∀ z ∈ stateNeighborhood S C base ε, ∀ m (p : PolarPoint),
    p.1 ∈ tsupport (deriv (χ m)) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

/-- One actual difference tower, formed before selecting any derivative
order. The reference uses exactly the same stored flow and left chart. -/
def NonlinearPropertiesThrough03.n04ActualMinusFirstIntegralDifference_stripJointTower
    (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        n04bMinusFirstIntegral
          (fun q => L.minusFlow (liftSectorParameter S C x.1) m q.1 q.2)
          (stateLeftChart S (liftSectorParameter S C x.1).1 m) x.2 -
        n04bMinusFirstIntegral (fun q => L.minusFlow (C.referenceState, 0) m q.1 q.2)
          (stateLeftChart S C.referenceState m) x.2) := by
  let V : (StateDirections S × ℝ) × PolarPoint → ℝ := fun x =>
    n04bMinusFirstIntegral
      (fun q => L.minusFlow (liftSectorParameter S C x.1) m q.1 q.2)
      (stateLeftChart S (liftSectorParameter S C x.1).1 m) x.2
  let J : SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ)) V :=
    hN.1.1.n04ActualMinusFirstIntegral_stripJointTower hS hT hfield χ hχ hχrange
      hcoeff hflow hdiscFull m l h hl hh
  have hzero : (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε := by
    change sectorGrading S base (0 : StateDirections S) < ε ∧ |(0 : ℝ)| < ε
    simpa only [map_zero, abs_zero] using And.intro hN.1.1.2.1 hN.1.1.2.1
  let P : ((StateDirections S × ℝ) × PolarPoint) →L[ℝ]
      (StateDirections S × ℝ) × PolarPoint :=
    (0 : ((StateDirections S × ℝ) × PolarPoint) →L[ℝ] (StateDirections S × ℝ)).prod
      (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) PolarPoint)
  have hP (x : (StateDirections S × ℝ) × PolarPoint) :
      (0 : (StateDirections S × ℝ) × PolarPoint) + P x = (0, x.2) :=
    (zero_add (P x)).trans rfl
  have hmap : MapsTo (fun x => (0 : (StateDirections S × ℝ) × PolarPoint) + P x)
      (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ)) := by
    intro x hx
    rw [hP]
    exact ⟨hzero, hx.2⟩
  let K := J.compAffine P 0 J.open_domain hmap
  let A : PolarPoint →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  apply (solveSmoothDirectionsPostcomp (smoothDirectionsProd J K) A).congrOn
  intro x hx
  change V x - V (0 + P x) = _
  rw [hP]
  change V x - n04bMinusFirstIntegral
      (fun q => L.minusFlow (C.referenceState + 0, 0) m q.1 q.2)
      (stateLeftChart S (C.referenceState + 0) m) x.2 = _
  rw [add_zero]

variable
  (hflowSlope : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)

include hN hS hT hfield hflow hχrange hflowSlope hl hh in
/-- Any already fixed genuine tower of this actual difference has the
same pure angular estimate. The common low order precedes every spatial
order and selector, while the material factor remains exactly H^(3/4). -/
theorem NonlinearPropertiesThrough03.n04ActualMinusFirstIntegralDifference_angular_interpolation
    (J : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        n04bMinusFirstIntegral
          (fun q => L.minusFlow (liftSectorParameter S C x.1) m q.1 q.2)
          (stateLeftChart S (liftSectorParameter S C x.1).1 m) x.2 -
        n04bMinusFirstIntegral (fun q => L.minusFlow (C.referenceState, 0) m q.1 q.2)
          (stateLeftChart S C.referenceState m) x.2))
    (nmax : ℕ) :
    let p := pairGrading (sectorGrading S) realGrading
    ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m x, x ∈ sectorNeighborhood S base ε ε →
        ∀ w, p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint,
        y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) n 0 b x w y| ≤
          K * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            (1 + p (N + B + 1) x + p (N + B + 1) w) ^
              ((b : ℝ) / ((N : ℝ) + 1)) := by
  let I := {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)}
  let rsel : I → ℕ → ℝ := Subtype.val
  have hrsel (i : I) (m : ℕ) : rsel i m ∈ Icc (C.left m) (C.right m) := i.property m
  have hcover (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (l m) (h m)) :
      ∃ i : I, rsel i m = r :=
    hN.1.1.closedRadiusSelector_cover m r
      ⟨((hl m).trans hr.1).le, (hr.2.trans (hh m)).le⟩
  have hg := hN.1.1.uniformSmoothFamilyOn_n04MinusFirstIntegralCircle
    hS hT hflowSlope χ hχrange rsel hrsel
  have hp := sectorPairGrading_monotone S
  have hIp : HasInterpolation (pairGrading (sectorGrading S) realGrading) :=
    hasInterpolation_of_hasSmoothing hp
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  apply hg.realized_strip_angular_interpolation hp hIp (hS.2.1 (3 / 4 : ℝ))
    ((material_circle_sample_weights_pos hT hN.1.1.1.1).2) l h rsel hcover J _ nmax
  intro i m hr x hx θ
  have href := (n04b_reference_firstIntegrals hN.1.1.2.2.1 hT hS hN hfield
    m (hrsel i m) θ).1
  rw [href]
  have hd := hN.1.1.n04MinusFirstIntegralCircle_decode
    hS hT χ hχrange (rsel i) (hrsel i) x hx m θ
  simpa only [hflow] using hd.symm

end ContinuousFlexibility.Statements
