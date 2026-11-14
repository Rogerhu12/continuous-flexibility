module

public import ContinuousFlexibility.Analysis.N01cActualFlowSpeedOuterBounds
public import ContinuousFlexibility.Analysis.N01cActualFlowForcingComposition

/-!
# The actual singleton linear speed jet

The all-angle singleton forcing choice has no parameter slots. Its
zeroth state jet is therefore the actual first angular derivative of the
cosine speed, with the genuine compact-time derivative as its multiplier.
Further angular derivatives do not change that multiplier.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
  (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
    r ∈ Icc (C.left i) (C.right i) →
      0 < twoRootDivided (componentOpticalSquare D S C i z)
        (C.left i) (C.right i) r)
  (m : ℕ) {d : ℕ} (x : AnnularState S × ℝ)
  (hx : x ∈ stateNeighborhood S C base ε)
  (L : (Fin d → ℝ) →L[ℝ] (AnnularState S × ℝ))

/-- Every angular jet of the actual singleton outer field is exactly a
positive angular jet of the actual cosine speed. -/
theorem ordinaryFlowSpeedOuterJet_angle_coe_apply
    (J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m))
    (t : ℝ) (b : ℕ) (θ : ℝ) :
    ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L
        (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice b
          (θ : AddCircle Real.pi) =
      deriv (circleFlowCompactTime 0 Real.pi) t *
        iteratedDeriv (b + 1)
          (fun η => componentCosineSpeed D S C m
            (x, (circleFlowCompactTime 0 Real.pi t, η))) θ := by
  have he := ordinaryFlowSpeedOuterJet_eq_stateJet hS hT hA hB hpos m x hx L J
    (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice b θ
  change ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L
      (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice b
        (θ : AddCircle Real.pi) =
    deriv (circleFlowCompactTime 0 Real.pi) t *
      (smoothDirections_angularStateSlice (J.jet (circleFlowCompactTime 0 Real.pi t))
        (1 + b) θ).D 0 x Fin.elim0 at he
  have hv := smoothDirections_D_zero_apply
    (smoothDirections_angularStateSlice (J.jet (circleFlowCompactTime 0 Real.pi t))
      (1 + b) θ) hx (Fin.elim0 : Fin 0 → AnnularState S × ℝ)
  calc
    _ = deriv (circleFlowCompactTime 0 Real.pi) t *
        (smoothDirections_angularStateSlice (J.jet (circleFlowCompactTime 0 Real.pi t))
          (1 + b) θ).D 0 x Fin.elim0 := he
    _ = deriv (circleFlowCompactTime 0 Real.pi) t *
        iteratedDeriv (1 + b)
          (fun η => componentCosineSpeed D S C m
            (x, (circleFlowCompactTime 0 Real.pi t, η))) θ :=
      congrArg (fun u : ℝ => deriv (circleFlowCompactTime 0 Real.pi) t * u) hv
    _ = _ := by rw [Nat.add_comm 1 b]

/-- In particular the original outer field is the actual first angular
speed derivative, without introducing any order-dependent loss. -/
theorem ordinaryFlowSpeedOuterField_angle_eq
    (J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m))
    (t θ : ℝ) :
    ordinaryFlowSpeedOuterField hS hT hA hB hpos m x hx L
        (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice θ =
      deriv (circleFlowCompactTime 0 Real.pi) t *
        deriv (fun η => componentCosineSpeed D S C m
          (x, (circleFlowCompactTime 0 Real.pi t, η))) θ := by
  simpa only [ordinaryFlowSpeedOuterJet_coe_apply, iteratedDeriv_zero,
    Nat.zero_add, iteratedDeriv_one] using
      ordinaryFlowSpeedOuterJet_angle_coe_apply hS hT hA hB hpos m x hx L J t 0 θ

end ContinuousFlexibility.Statements
