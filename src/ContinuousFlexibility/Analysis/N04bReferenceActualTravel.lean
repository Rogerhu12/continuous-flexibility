module

public import ContinuousFlexibility.Analysis.N04bActualTravelChart
public import ContinuousFlexibility.Analysis.N04bReferenceTravelCut

/-!
# The actual reference travel chart is the radial optical chart

The field construction supplies the actual reference characteristic flow,
before canonical coordinates are introduced. Its literal chosen angular
inverse is the opposite translation. The actual normalized first integrals
therefore give the optical travel and the unchanged angular coordinate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04b_referenceState_sector
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) :
    stateSector S C.referenceState := by
  have hκ : C.referenceState.2.2.1 = 0 := href.2.2.2.1
  have hh : C.referenceState.2.2.2 = 0 := href.2.2.2.2.1
  constructor
  · intro m θ φ
    simp only [hκ, map_zero, Pi.zero_apply]
  · intro m θ
    simp only [hh, map_zero, Pi.zero_apply, neg_zero]

theorem n04b_referenceState_leftChart
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) (m : ℕ) (θ : ℝ) :
    stateLeftChart S C.referenceState m θ = θ := by
  have hh : C.referenceState.2.2.2 = 0 := href.2.2.2.2.1
  simp only [stateLeftChart, hh, map_zero, Pi.zero_apply, add_zero]

/-- The raw reference-flow output is exactly the existing optical-travel
function, including both physical component endpoints. -/
theorem n04b_referenceMinusFlow_eq_optical
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hfield : N04bFieldRegularity D S C L base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    L.minusFlow (C.referenceState, 0) m r θ =
      θ - opticalTravel D.w (C.left m) r :=
  hfield.reference_flow m r hr θ

/-- The chosen inverse of the actual reference flow is the actual
opposite optical translation. -/
theorem n04b_referenceMinusFlow_inverse
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hfield : N04bFieldRegularity D S C L base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    Function.invFun (L.minusFlow (C.referenceState, 0) m r) θ =
      θ + opticalTravel D.w (C.left m) r := by
  let f := L.minusFlow (C.referenceState, 0) m r
  have hf (η : ℝ) : f η = η - opticalTravel D.w (C.left m) r :=
    n04b_referenceMinusFlow_eq_optical hfield m hr η
  have hinj : Function.Injective f := by
    intro a b hab
    rw [hf a, hf b] at hab
    linarith only [hab]
  have he : f (θ + opticalTravel D.w (C.left m) r) = θ := by
    rw [hf]
    ring
  have hi := Function.leftInverse_invFun hinj
    (θ + opticalTravel D.w (C.left m) r)
  rw [he] at hi
  exact hi

theorem n04b_reference_firstIntegrals
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (href : referenceStateConditions D S C)
    (hfield : N04bFieldRegularity D S C L base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    n04bMinusFirstIntegral (fun p => L.minusFlow (C.referenceState, 0) m p.1 p.2)
        (stateLeftChart S C.referenceState m) (r, θ) =
      θ + opticalTravel D.w (C.left m) r ∧
    n04bPlusFirstIntegral (fun p => L.minusFlow (C.referenceState, 0) m p.1 p.2)
        (stateLeftChart S C.referenceState m) (r, θ) =
      θ - opticalTravel D.w (C.left m) r := by
  have hm (η : ℝ) :
      n04bMinusFirstIntegral (fun p => L.minusFlow (C.referenceState, 0) m p.1 p.2)
          (stateLeftChart S C.referenceState m) (r, η) =
        η + opticalTravel D.w (C.left m) r := by
    change stateLeftChart S C.referenceState m
      (Function.invFun (L.minusFlow (C.referenceState, 0) m r) η) = _
    rw [n04b_referenceMinusFlow_inverse hfield m hr η,
      n04b_referenceState_leftChart href]
  refine ⟨hm θ, ?_⟩
  change -n04bMinusFirstIntegral
    (fun p => L.minusFlow (C.referenceState, 0) m p.1 p.2)
    (stateLeftChart S C.referenceState m) (r, -θ) = _
  rw [hm (-θ)]
  ring

/-- The literal travel chart used in the state-dependent construction
specializes to the actual radial optical travel at the reference state. -/
theorem n04b_reference_actualTravelChart
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (href : referenceStateConditions D S C)
    (hfield : N04bFieldRegularity D S C L base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    n04bActualTravelChart S C L (C.referenceState, 0) m (r, θ) =
      (opticalTravel D.w (C.left m) r, θ) := by
  have h := n04b_reference_firstIntegrals href hfield m hr θ
  simp only [n04bActualTravelChart, n04bCharacteristicTravelChart,
    characteristicTravelChart, h.1, h.2]
  apply Prod.ext <;> dsimp only <;> ring

end ContinuousFlexibility.Analysis
