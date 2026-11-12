import ContinuousFlexibility.Analysis.N01cActualFlowVariationEnvelope
import ContinuousFlexibility.Analysis.N01cActualFlowNormalization

/-!
# Strong induction for the actual positive angular flow derivatives

The highest unknown satisfies its actual scalar linear variational
equation. Every nonconstant lower factor has strictly smaller positive
state order. Its normalized estimate is therefore available from strong
induction. The speed head, the derivative defect, the low geometry, and
the interpolation base were all fixed before this induction.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem n01_ordinaryFlowAngularOrderBounds_of_actual_lowGeometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base₀ loss d₀ normLoss : ℕ} {ε ε₀ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
      r ∈ Icc (C.left i) (C.right i) →
        0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε)
    (hε2 : ε ≤ 1 / 2)
    (hNorm : FlowPolynomialNormalization
      (pairGrading (stateGrading S) realGrading) base normLoss)
    (hB₀ : N01PartB D S C base₀ ε₀)
    (hGs : ∀ z ∈ stateNeighborhood S C base₀ ε₀, ∀ i,
      ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C i (z, p)))
    (hQ : OrdinaryFlowZeroAngularGrowth hS hT hA hB₀ hGs loss d₀)
    (hsub : stateNeighborhood S C base ε ⊆ stateNeighborhood S C base₀ ε₀)
    (c M Mlin : ℝ) (hc : 0 < c) (hM : 0 ≤ M)
    (hgeometry : ∀ N, ∀ u : OrdinaryFlowVariationInput D S C base ε N, ∀ t : ℝ,
      (∀ θ, c ≤ deriv
        (ordinaryFlowFiniteAngle u.component u.state u.mem u.plot t) θ) ∧
      u.defectNorm hS hT hA hB hpos 3 t ≤ M)
    (hlinear : ∀ n, ∀ u : OrdinaryFlowVariationInput D S C base ε (n + 1),
      (u.data hS hT hA hB hpos).coefficientSize 1 ≤ Mlin) :
    ∀ N : ℕ, 0 < N →
      OrdinaryFlowAngularOrderBound hS hT hA hB hpos loss N := by
  have hhead := n01_ordinaryFlowForcingHead_bounds hS hT hA hε hB hpos hE hSpeed
    hB₀ hGs hQ hsub c M hc hM hgeometry
  have hcoefficient := n01_ordinaryFlowCoefficient_highBounds hS hT hA hB hpos
    (hhead 1 (by norm_num))
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro hN
      cases N with
      | zero => omega
      | succ n =>
          have hIH : ∀ k, k < n + 1 → 0 < k →
              OrdinaryFlowAngularOrderBound hS hT hA hB hpos loss k :=
            fun k hk hkp => ih k hk hkp
          have hraw := n01_ordinaryFlowVariation_unitBall_bounds
            hS hT hA hB hpos hE Mlin hlinear hcoefficient n hIH
            (hhead (n + 1) (Nat.succ_pos n))
          exact n01_ordinaryFlowAngularOrderBound_of_unitPolynomial
            (loss := loss) (degree := 2 * (n + 1) + 5)
            hS hT hA hB hpos hE hε2 hNorm hraw

end ContinuousFlexibility.Blueprint
