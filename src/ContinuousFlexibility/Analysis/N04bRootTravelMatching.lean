import ContinuousFlexibility.Analysis.N04bPhysicalRootCoordinates
import ContinuousFlexibility.Analysis.N04bActualTravelChart

/-!
# Matching the actual root coordinates to the global travel strip

The left root uses the actual left angular label directly. At the right
root the terminal normalization changes the minus label by minus travel
and the plus label by plus travel. Thus the same global angle is retained,
while the inward root travel is the complement of the global travel.
These are identities of the actual stored-flow inverses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Both actual global first integrals agree with the left root function. -/
theorem n04b_left_root_firstIntegral_matching
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {z : AnnularState S × ℝ} {m : ℕ}
    {ρ : ℝ} {d c₀ : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ (stateLeftChart S z.1 m)
      (fun θ x => L.minusFlow z m (C.left m + x) θ) ρ (-1) G)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ρ) (θ : ℝ) :
    n04bMinusFirstIntegral (fun p => L.minusFlow z m p.1 p.2)
        (stateLeftChart S z.1 m) (C.left m + x, θ) =
      rootCharacteristicCoordinate G (-1) (x, θ) ∧
    n04bPlusFirstIntegral (fun p => L.minusFlow z m p.1 p.2)
        (stateLeftChart S z.1 m) (C.left m + x, θ) =
      rootCharacteristicCoordinate G 1 (x, θ) := by
  constructor
  · exact H.stored_footpoint x hx θ
  · change -stateLeftChart S z.1 m
      (Function.invFun (L.minusFlow z m (C.left m + x)) (-θ)) = _
    rw [H.stored_footpoint x hx (-θ)]
    simp only [rootCharacteristicCoordinate, neg_one_mul, one_mul,
      H.reflection x (x ^ (3 / 2 : ℝ)) θ, neg_neg]

/-- The left physical root travel is literally the global actual travel. -/
theorem n04b_left_root_travel_matching
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {z : AnnularState S × ℝ} {m : ℕ}
    {ρ : ℝ} {d c₀ : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ (stateLeftChart S z.1 m)
      (fun θ x => L.minusFlow z m (C.left m + x) θ) ρ (-1) G)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ρ) (θ : ℝ) :
    n04bActualTravelChart S C L z m (C.left m + x, θ) =
      characteristicTravelChart (rootCharacteristicCoordinate G 1)
        (rootCharacteristicCoordinate G (-1)) (x, θ) := by
  have h := n04b_left_root_firstIntegral_matching H hx θ
  simp only [n04bActualTravelChart, n04bCharacteristicTravelChart,
    characteristicTravelChart, h.1, h.2]

/-- The right root's actual normalized labels have the precise travel
shifts imposed by the N03 endpoint return identity. -/
theorem n04b_right_root_firstIntegral_matching
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    {ρ : ℝ} (hspan : C.left m < C.right m - ρ)
    {d c₀ : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ (rightChartCandidate S C z m)
      (n04bRightRootFlow C L z m) ρ 1 G)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ρ) (θ : ℝ) :
    rootCharacteristicCoordinate G 1 (x, θ) =
      n04bMinusFirstIntegral (fun p => L.minusFlow z m p.1 p.2)
        (stateLeftChart S z.1 m) (C.right m - x, θ) - C.travel m ∧
    rootCharacteristicCoordinate G (-1) (x, θ) =
      n04bPlusFirstIntegral (fun p => L.minusFlow z m p.1 p.2)
        (stateLeftChart S z.1 m) (C.right m - x, θ) + C.travel m := by
  let F : ℝ → ℝ := L.minusFlow z m (C.right m)
  let f : ℝ → ℝ := L.minusFlow z m (C.right m - x)
  let P : ℝ → ℝ := fun η => n04bRightRootFlow C L z m η x
  have hregular := n04b_actualMinusFlow_regular h03 hS hT hfield hz hs m
  have hr : C.right m - x ∈ Icc (C.left m) (C.right m) :=
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hfbij : Function.Bijective f :=
    ⟨(hregular.strictMono hr).injective, hregular.surjective Real.pi_ne_zero hr⟩
  have hFbij : Function.Bijective F :=
    (n04b_corrected_return_geometry hT hS h03 hz hs m).2.2.2.1
  have hPinj : Function.Injective P := by
    intro a b he
    have hi : Function.invFun F a = Function.invFun F b := hfbij.1 he
    calc
      a = F (Function.invFun F a) := (Function.rightInverse_invFun hFbij.2 a).symm
      _ = F (Function.invFun F b) := congrArg F hi
      _ = b := Function.rightInverse_invFun hFbij.2 b
  have hinverse (η : ℝ) :
      Function.invFun P η = F (Function.invFun f η) := by
    have hv : P (F (Function.invFun f η)) = η := by
      change f (Function.invFun F (F (Function.invFun f η))) = η
      rw [Function.leftInverse_invFun hFbij.1]
      exact Function.rightInverse_invFun hfbij.2 η
    have hi := Function.leftInverse_invFun hPinj (F (Function.invFun f η))
    rw [hv] at hi
    exact hi
  have hminus (η : ℝ) :
      rootCharacteristicCoordinate G 1 (x, η) =
        n04bMinusFirstIntegral (fun p => L.minusFlow z m p.1 p.2)
          (stateLeftChart S z.1 m) (C.right m - x, η) - C.travel m := by
    have he := H.stored_footpoint x hx η
    change rightChartCandidate S C z m (Function.invFun P η) = _ at he
    rw [hinverse η] at he
    have hreturn := (h03.2.2.2.2.2.1 z hz hs m (Function.invFun f η)).2.2.2.1
    exact he.symm.trans hreturn
  refine ⟨hminus θ, ?_⟩
  have hreflect : rootCharacteristicCoordinate G (-1) (x, θ) =
      -rootCharacteristicCoordinate G 1 (x, -θ) := by
    simpa only [rootCharacteristicCoordinate, neg_one_mul, one_mul, neg_neg] using
      H.reflection x (x ^ (3 / 2 : ℝ)) (-θ)
  rw [hreflect, hminus (-θ)]
  change -(_ - C.travel m) = -_ + C.travel m
  ring

/-- The right physical root travel is the complement of the global
travel; its angular coordinate is exactly the same global angle. -/
theorem n04b_right_root_travel_matching
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    {ρ : ℝ} (hspan : C.left m < C.right m - ρ)
    {d c₀ : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ (rightChartCandidate S C z m)
      (n04bRightRootFlow C L z m) ρ 1 G)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ρ) (θ : ℝ) :
    characteristicTravelChart (rootCharacteristicCoordinate G 1)
        (rootCharacteristicCoordinate G (-1)) (x, θ) =
      (C.travel m - (n04bActualTravelChart S C L z m (C.right m - x, θ)).1,
        (n04bActualTravelChart S C L z m (C.right m - x, θ)).2) := by
  have h := n04b_right_root_firstIntegral_matching hT hS h03 hfield hz hs m hspan H hx θ
  simp only [characteristicTravelChart, h.1, h.2,
    n04bActualTravelChart, n04bCharacteristicTravelChart]
  apply Prod.ext <;> dsimp only <;> ring

end ContinuousFlexibility.Analysis
