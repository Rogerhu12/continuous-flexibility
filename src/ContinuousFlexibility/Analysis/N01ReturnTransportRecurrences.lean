import ContinuousFlexibility.Analysis.N01ReturnTransportSpatialTowers
import ContinuousFlexibility.Analysis.JointMixedTransportCalculus
import ContinuousFlexibility.Analysis.ScalarTransportSystemBounds

/-!
# The actual N01 correction satisfies the finite transport system

The parameter map may retain an independent circle residual.  The
identities therefore apply both to that independent residual and to
the residual of the supplied N02 operator.  The cutoff and the two
inverse maps are precisely those in the existing correction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

local instance n01ReturnTransportRecurrencesStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {U : Set E} (hU : IsOpen U) (hUc : Convex ℝ U)
  (σ : E → StateDirections S × ℝ)
  (hσ : MapsTo σ U (sectorNeighborhood S base ε ε))
  (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m)

include hN hS hT hU hUc hσ hl hh in
/-- The inverse-flow angular slope obeys the actual variational
transport equation at every mixed parameter/spatial order. -/
theorem N01Properties.returnFlowInverseSlope_diagonal_recurrence
    (hdisc : ∀ x ∈ U, ∀ p : PolarPoint, p.1 ∈ Ioo l h →
      0 < (originalCoefficients D S C (liftSectorParameter S C (σ x))).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C (σ x))).a p *
          (originalCoefficients D S C (liftSectorParameter S C (σ x))).c p)
    (JA : SmoothDirections (U ×ˢ (Ioo l h ×ˢ univ))
      (fun x : E × PolarPoint => returnFlowInverseSlope S C
        (liftSectorParameter S C (σ x.1)) m x.2))
    (JL : SmoothDirections (U ×ˢ (Ioo l h ×ˢ univ))
      (fun x : E × PolarPoint => minusCharacteristicSpeed
        (originalCoefficients D S C (liftSectorParameter S C (σ x.1))) x.2))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) (p : PolarPoint) (hp : p.1 ∈ Ioo l h) :
    jointMixedDiagonal JA n (a + 1) b x w p =
      diagonalJetProduct
        (fun k i j (_ : Unit) => jointMixedDiagonal JL k i (j + 1) x w p)
        (fun k i j (_ : Unit) => jointMixedDiagonal JA k i j x w p) n a b () -
      diagonalJetProduct
        (fun k i j (_ : Unit) => jointMixedDiagonal JL k i j x w p)
        (fun k i j (_ : Unit) => jointMixedDiagonal JA k i (j + 1) x w p) n a b () := by
  have hV : IsOpen (Ioo l h ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hc := hUc.prod ((convex_Ioo l h).prod (convex_univ : Convex ℝ (univ : Set ℝ)))
  apply jointMixedDiagonal_variational_transport JA JL hU hV hc _ n a b x w hx ⟨hp, mem_univ _⟩
  intro y hy q hq
  exact hN.returnFlowInverseSlope_transport_of_discriminant hS hT
    (liftSectorParameter_mem_stateNeighborhood (hσ hy) le_rfl)
    (hN.2.2.1.liftSectorParameter_sector (σ y)) m q
    ⟨hl.trans hq.1.1, hq.1.2.trans hh⟩ (hdisc y hy q hq.1)

variable (hR : N02Properties D T S C R base ε)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)

include hN hS hT hU hUc hσ hl hh hR hχ hχrange in
/-- The same finite recurrence holds for any supplied residual field
`ρ x`, including the independent input and the actual N02 residual. -/
theorem N01Properties.returnCorrectionPulledDisplacement_diagonal_recurrence
    (ρ : E → CircleSpace S)
    (JZ : SmoothDirections (U ×ˢ (Ioo l h ×ˢ univ))
      (fun x : E × PolarPoint => returnCorrectionPulledDisplacementLinear S C χ
        (liftSectorParameter S C (σ x.1)) m x.2 (ρ x.1)))
    (JT : SmoothDirections (U ×ˢ (Ioo l h ×ˢ univ))
      (fun x : E × PolarPoint =>
        minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C (σ x.1))) x.2 +
          deriv (χ m) x.2.1 * returnFlowInverseSlope S C
            (liftSectorParameter S C (σ x.1)) m x.2 *
              returnCorrectionPulledDisplacementLinear S C χ
                (liftSectorParameter S C (σ x.1)) m x.2
                  (R.residual (liftSectorParameter S C (σ x.1)))))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) (p : PolarPoint) (hp : p.1 ∈ Ioo l h) :
    jointMixedDiagonal JZ n (a + 1) b x w p =
      -diagonalJetProduct
        (fun k i j (_ : Unit) => jointMixedDiagonal JT k i j x w p)
        (fun k i j (_ : Unit) => jointMixedDiagonal JZ k i (j + 1) x w p) n a b () := by
  have hV : IsOpen (Ioo l h ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hc := hUc.prod ((convex_Ioo l h).prod (convex_univ : Convex ℝ (univ : Set ℝ)))
  apply jointMixedDiagonal_transport JZ JT hU hV hc _ n a b x w hx ⟨hp, mem_univ _⟩
  intro y hy q hq
  have ht := hN.returnCorrectionPulledDisplacementLinear_transport_actual hS hT
    (liftSectorParameter_mem_stateNeighborhood (hσ hy) le_rfl)
    (hN.2.2.1.liftSectorParameter_sector (σ y)) hR χ m (hχ m) (hχrange m)
    (ρ y) q ⟨hl.trans hq.1.1, hq.1.2.trans hh⟩
  exact ht.trans (by ring)

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint}
  {f g h t : E × PolarPoint → ℝ}

/-- Nested finite products are derivatives of the actual triple
product, with the same order of factors used in `χ' A Z`. -/
theorem jointMixedDiagonal_triple_mul
    (JF : SmoothDirections (U ×ˢ V) f) (JG : SmoothDirections (U ×ˢ V) g)
    (JH : SmoothDirections (U ×ˢ V) h) (JT : SmoothDirections (U ×ˢ V) t)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (heq : ∀ x ∈ U, ∀ p ∈ V, t (x, p) = f (x, p) * g (x, p) * h (x, p))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) (p : PolarPoint) (hp : p ∈ V) :
    jointMixedDiagonal JT n a b x w p =
      diagonalJetProduct
        (diagonalJetProduct
          (fun k i j (_ : Unit) => jointMixedDiagonal JF k i j x w p)
          (fun k i j (_ : Unit) => jointMixedDiagonal JG k i j x w p))
        (fun k i j (_ : Unit) => jointMixedDiagonal JH k i j x w p) n a b () := by
  have hout := jointMixedDiagonal_mul (JF.mul JG) JH JT hU hV hc heq n a b x w hx hp
  rw [hout]
  unfold diagonalJetProduct
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [jointMixedDiagonal_mul JF JG (JF.mul JG) hU hV hc
    (fun _ _ _ _ => rfl) k i j x w hx hp]

/-- The actual corrected transport speed has exactly the finite
polynomial jet used in the radial induction. -/
theorem jointMixedDiagonal_add_triple_mul
    {c : E × PolarPoint → ℝ}
    (JL : SmoothDirections (U ×ˢ V) f) (JC : SmoothDirections (U ×ˢ V) c)
    (JA : SmoothDirections (U ×ˢ V) g) (JZ : SmoothDirections (U ×ˢ V) h)
    (JT : SmoothDirections (U ×ˢ V) t)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (heq : ∀ x ∈ U, ∀ p ∈ V,
      t (x, p) = f (x, p) + c (x, p) * g (x, p) * h (x, p))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) (p : PolarPoint) (hp : p ∈ V) :
    jointMixedDiagonal JT n a b x w p = jointMixedDiagonal JL n a b x w p +
      diagonalJetProduct
        (diagonalJetProduct
          (fun k i j (_ : Unit) => jointMixedDiagonal JC k i j x w p)
          (fun k i j (_ : Unit) => jointMixedDiagonal JA k i j x w p))
        (fun k i j (_ : Unit) => jointMixedDiagonal JZ k i j x w p) n a b () := by
  let Jprod := (JC.mul JA).mul JZ
  have hsum := jointMixedDiagonal_add JL Jprod JT hV heq n a b x w hx hp
  have hprod := jointMixedDiagonal_triple_mul JC JA JZ Jprod hU hV hc
    (fun _ _ _ _ => rfl) n a b x w hx p hp
  exact hsum.trans (congrArg (jointMixedDiagonal JL n a b x w p + ·) hprod)

end ContinuousFlexibility.Analysis
