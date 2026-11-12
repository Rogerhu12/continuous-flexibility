import ContinuousFlexibility.Analysis.CoupledDerivativeIdentity

/-!
# Assembling the exact N10 error identity

The independent error formulas and their regularity supply the remaining
data. The two genuine line derivatives follow from the recovered N09
increment and the actual N08 residual tower.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {G : ScalarInverseData S}
  {P : ResidualData S} {B : ControlColumnData S}
  {N : ControlInverseData S} {V : CoupledInverseData S} {Q : QuadraticErrorData S}
  {base loss : ℕ} {ε q0 : ℝ}

theorem coupled_N10Properties_of_independent_errors
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h3 : N03Properties D T S C R L base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (h9 : N09Properties D T S C R G B N V base ε q0)
    (hscalar : ∀ z ∈ coupledNeighborhood S C base ε q0, stateSector S z.1 →
      ∀ r y : ResidualSpace S, ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode (Q.Q z r y).1.val p =
        z.2 * angularPartial (fun t => residualErrorCoefficient D S C z t *
          (S.height (3 / 4 : ℝ)).decode r.1.val t *
          angularPartial (heightPairField S (V.V z y).1) t) p +
        (S.height (3 / 4 : ℝ)).decode ((L.error z r.2.val (V.V z y).1).val) p)
    (hcircle : ∀ z ∈ coupledNeighborhood S C base ε q0, stateSector S z.1 →
      ∀ r y : ResidualSpace S, ∀ m θ,
      (S.circle (3 / 4 : ℝ)).decode (Q.Q z r y).2.val m θ =
        circleChartError S C z r.2.val
          (R.inverse (y.2.val - z.2 • B.heightRow z (V.V z y).1 -
            B.circleColumn z (V.V z y).2.2.1)) m θ)
    (hcompat : ∀ z ∈ coupledNeighborhood S C base ε q0, stateSector S z.1 →
      ∀ r y : ResidualSpace S,
      physicalSourceIntegral D ((S.height (3 / 4 : ℝ)).decode (Q.Q z r y).1.val) = 0)
    (htame : SmoothTameOn
      (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
        (residualGrading S)) (residualGrading S)
      ((sectorNeighborhood S base ε q0 ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × ResidualSpace S) × ResidualSpace S =>
        Q.Q (liftSectorParameter S C z.1.1) z.1.2 z.2)) :
    N10Properties D S C R L P B V Q base ε q0 := by
  have hderiv : ∀ z ∈ coupledNeighborhood S C base ε q0, stateSector S z.1 →
      ∀ y : ResidualSpace S,
      HasProjectiveLineDerivAt (fun x => jointResidual S P (x, z.2))
        (y + Q.Q z (jointResidual S P z) y) z.1 (V.V z y) := by
    intro z hz hs y
    have hz0 : z ∈ stateNeighborhood S C base ε := ⟨hz.1, hz.2.trans_le h9.2.1⟩
    exact coupled_recovered_hasLineDerivAt_ambient hT hS h1 h2 h3 hG h8 h9 hz hs y
      (Q.Q z (jointResidual S P z) y)
      (coupled_actualError_scalar_identity h8 hz0 hs y (hscalar z hz hs _ y))
      (coupled_actualError_circle_identity hS h2 h8 hz0 hs y (hcircle z hz hs _ y))
  refine ⟨hscalar, hcircle, hcompat, hderiv, ?_, htame⟩
  intro z hz y
  have hd := hderiv (liftSectorParameter S C z)
    (coupled_liftSectorParameter_mem_coupledNeighborhood hz)
    (h1.2.2.1.liftSectorParameter_sector z) y
  exact coupled_recovered_sector_derivative h9 hz y
    (Q.Q (liftSectorParameter S C z) (sectorJointResidual S C P z) y) hd

end ContinuousFlexibility.Statements
