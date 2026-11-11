import ContinuousFlexibility.Blueprint.Statements

/-!
# Recovering the actual equations from the coupled residual

The Nash--Moser problem is expressed in the source and even-circle spaces.
The identities in N08 identify its zero with the scalar and return equations,
and the equivalence in N02 supplies both actual characteristic-return equations.
This module also checks the sector and neighborhood when passing from the
linear sector coordinates back to the affine state coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

/-- The reference state belongs to the constant-control, odd-chart sector. -/
theorem referenceStateConditions.stateSector
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (h : referenceStateConditions D S C) : stateSector S C.referenceState := by
  obtain ⟨_, _, _, hκ, hh, _⟩ := h
  constructor
  · intro m θ φ
    simp only [hκ, map_zero, Pi.zero_apply]
  · intro m θ
    simp only [hh, map_zero, Pi.zero_apply, neg_zero]

/-- Translation by the reference state preserves the linear sector. -/
theorem referenceStateConditions.liftSectorParameter_sector
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (h : referenceStateConditions D S C) (z : StateDirections S × ℝ) :
    stateSector S (liftSectorParameter S C z).1 := by
  exact (stateSectorSubmodule S).add_mem h.stateSector z.1.property

/-- The restricted parameter neighborhood maps into the geometric neighborhood. -/
theorem liftSectorParameter_mem_stateNeighborhood
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {base : ℕ}
    {ε q0 : ℝ} {z : StateDirections S × ℝ}
    (hz : z ∈ sectorNeighborhood S base ε q0) (hq0 : q0 ≤ ε) :
    liftSectorParameter S C z ∈ stateNeighborhood S C base ε := by
  constructor
  · simpa only [liftSectorParameter, add_sub_cancel_left, sectorGrading,
      Seminorm.comp_apply, Submodule.subtype_apply] using hz.1
  · exact hz.2.trans_le hq0

/-- At a zero of the coupled residual its genuine scalar field vanishes. -/
theorem N08Properties.scalarResidual_eq_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
    {base loss : ℕ} {ε : ℝ}
    (h : N08Properties D T S C R G P B base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (hzero : jointResidual S P z = 0) :
    ∀ p ∈ annularOpen D, scalarResidualField D S C z p = 0 := by
  have hscalar : P.scalar z = 0 := congrArg Prod.fst hzero
  intro p hp
  rw [← h.2.2.1 z hz hs p hp, hscalar]
  simp only [ZeroMemClass.coe_zero, map_zero, Pi.zero_apply]

/-- At a zero of the coupled residual the genuine return residual vanishes. -/
theorem N08Properties.returnResidual_eq_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
    {base loss : ℕ} {ε : ℝ}
    (h : N08Properties D T S C R G P B base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (hzero : jointResidual S P z = 0) :
    R.residual z = 0 := by
  have hcircle : P.circle z = 0 := congrArg Prod.snd hzero
  rw [← h.2.2.2.1 z hz hs, hcircle]
  exact ZeroMemClass.coe_zero

/-- The coupled inverse has zero normalization row.  Its two scalar-inverse
terms combine to one scalar-inverse value by linearity, so no unproved
linearity assertion about the integral defining `referenceRow` is used. -/
theorem N09Properties.referenceRow_coupledInverse_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {G : ScalarInverseData S}
    {B : ControlColumnData S} {N : ControlInverseData S} {V : CoupledInverseData S}
    {base : ℕ} {ε q0 : ℝ}
    (h : N09Properties D T S C R G B N V base ε q0)
    (hG : ScalarInverseProperties D S C L G base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ coupledNeighborhood S C base ε q0)
    (hs : stateSector S z.1) (y : ResidualSpace S) :
    referenceRow D (heightPairField S (V.V z y).1) = 0 := by
  have hnear : z ∈ stateNeighborhood S C base ε := ⟨hz.1, hz.2.trans_le h.2.1⟩
  have hvalue : ((V.V z y).1, (V.V z y).2.1) =
      G.G z (y.1 - B.heightColumn z (controlSolution S B G N z y)) := by
    calc
      _ = G.G z y.1 - G.G z (B.heightColumn z (controlSolution S B G N z y)) :=
        (h.2.2.2.2.1 z hz hs y).2.2.1
      _ = _ := (map_sub (G.G z) _ _).symm
  have hrow := (hG.1 z hnear hs
    (y.1 - B.heightColumn z (controlSolution S B G N z y))).1
  rw [← hvalue] at hrow
  exact hrow

/-- N02 turns the vanishing circle residual into both actual return equations. -/
theorem N02Properties.returnEquations_of_residual_eq_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base : ℕ} {ε : ℝ}
    (h : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (hzero : R.residual z = 0) :
    ∀ m θ,
      rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ) =
        stateLeftChart S z.1 m θ - C.travel m ∧
      rightChartCandidate S C z m (-C.minusFlow z m (C.right m) (-θ)) =
        stateLeftChart S z.1 m θ + C.travel m :=
  (h.2.2.1 z hz hs).mp hzero

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

/-- A normalized nonzero-parameter zero supplies the frozen pointwise branch
statement, with exactly the same reference, spaces and geometric data. -/
theorem pointBranchStatement_of_jointResidual_zero
    {A : RadialReference} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData A.val T) (hS : IsPhysicalSpaces A.val T S)
    (hN01 : N01Properties A.val T S C base loss ε)
    (hN02 : N02Properties A.val T S C R base ε)
    (hN08 : N08Properties A.val T S C R G P B base loss ε)
    {x : AnnularState S} {q : ℝ} (hq : q ≠ 0)
    (hnear : (x, q) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S x) (hrow : referenceRow A.val (stateU S x) = 1)
    (hzero : jointResidual S P (x, q) = 0) : PointBranchStatement := by
  have hscalar := hN08.scalarResidual_eq_zero hnear hsector hzero
  have hcircle := hN08.returnResidual_eq_zero hnear hsector hzero
  exact ⟨A, T, S, hT, hS, C, R, base, loss, ε, hN01, x, q, hq,
    hnear, hsector, hrow, hscalar, hcircle,
    hN02.returnEquations_of_residual_eq_zero hnear hsector hcircle⟩

end ContinuousFlexibility.Blueprint
