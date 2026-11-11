import ContinuousFlexibility.Analysis.CoupledActualErrorIdentity

/-!
# Exact derivative identity for the recovered state

The scalar and circle computations identify the value of the same genuine
first jet. The conclusion is the actual ambient line derivative required
by N10, and affine transport gives its sector-coordinate version.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coupled_lineDerivAt_value_eq
    {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {f : X → Y} {a b : Y} {x v : X}
    (hab : a = b) (hd : HasProjectiveLineDerivAt f a x v) :
    HasProjectiveLineDerivAt f b x v :=
  (congrArg (fun d : Y => HasProjectiveLineDerivAt f d x v) hab).mp hd

private theorem coupled_lineDerivAt_direction_eq
    {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {f : X → Y} {df : Y} {x v w : X}
    (hvw : v = w) (hd : HasProjectiveLineDerivAt f df x v) :
    HasProjectiveLineDerivAt f df x w :=
  (congrArg (fun d : X => HasProjectiveLineDerivAt f df x d) hvw).mp hd

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {G : ScalarInverseData S}
  {P : ResidualData S} {B : ControlColumnData S}
  {N : ControlInverseData S} {V : CoupledInverseData S}
  {base loss : ℕ} {ε q0 : ℝ}

theorem coupled_recovered_hasLineDerivAt
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h3 : N03Properties D T S C R L base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (h9 : N09Properties D T S C R G B N V base ε q0)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε q0)
    (y e : ResidualSpace S)
    (heScalar : ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode e.1.val p =
        z.2 * scalarCorrectionError
          (residualErrorCoefficient D S C (liftSectorParameter S C z))
          (scalarResidualField D S C (liftSectorParameter S C z))
          (heightPairField S (V.V (liftSectorParameter S C z) y).1) p +
        (S.height (3 / 4 : ℝ)).decode
          ((L.error (liftSectorParameter S C z) (R.residual (liftSectorParameter S C z))
            (V.V (liftSectorParameter S C z) y).1).val) p)
    (heCircle : e.2.val = R.error (liftSectorParameter S C z)
      (R.residual (liftSectorParameter S C z))
      (R.inverse (y.2.val - z.2 • B.heightRow (liftSectorParameter S C z)
        (V.V (liftSectorParameter S C z) y).1 - B.circleColumn (liftSectorParameter S C z)
          (V.V (liftSectorParameter S C z) y).2.2.1))) :
    HasProjectiveLineDerivAt (fun x => jointResidual S P (x, z.2)) (y + e)
      (liftSectorParameter S C z).1 (V.V (liftSectorParameter S C z) y) := by
  have hres : SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (residualGrading S) (sectorNeighborhood S base ε ε) (sectorJointResidual S C P) :=
    h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P) :=
    hres.choose
  let v : StateDirections S := ⟨V.V (liftSectorParameter S C z) y,
    (h9.2.2.2.2.1 _ (coupled_liftSectorParameter_mem_coupledNeighborhood hz)
      (h1.2.2.1.liftSectorParameter_sector z) y).1⟩
  have hvalue : projectiveJetHeadLinear J.D 0 z Fin.elim0 (v, 0) = y + e := by
    apply Prod.ext
    · exact coupled_recovered_scalar_firstJet hT hS h1 h3 hG h8 h9 J hz y e.1 heScalar
    · exact coupled_recovered_circle_firstJet hT hS h1 h2 h8 h9 J hz y e.2 heCircle
  have hd := coupled_joint_first_derivative J
    (show z ∈ sectorNeighborhood S base ε ε from ⟨hz.1, hz.2.trans_le h9.2.1⟩) v
  exact coupled_lineDerivAt_value_eq hvalue hd

/-- The recovered direction used by the sector operator is precisely the
direction included in the ambient derivative. -/
theorem coupled_recovered_sector_derivative
    (h9 : N09Properties D T S C R G B N V base ε q0)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε q0)
    (y e : ResidualSpace S)
    (hd : HasProjectiveLineDerivAt (fun x => jointResidual S P (x, z.2)) (y + e)
      (liftSectorParameter S C z).1 (V.V (liftSectorParameter S C z) y)) :
    HasProjectiveLineDerivAt (fun x : StateDirections S =>
      sectorJointResidual S C P (x, z.2)) (y + e) z.1 (V.sectorV z y) := by
  have hval : (V.sectorV z y).val = V.V (liftSectorParameter S C z) y :=
    h9.2.2.2.2.2.1 z hz y
  have hdir : HasProjectiveLineDerivAt (fun x => jointResidual S P (x, z.2)) (y + e)
      (C.referenceState + z.1.val) (V.sectorV z y).val := by
    exact coupled_lineDerivAt_direction_eq hval.symm hd
  exact (coupled_lineDerivAt_affine_iff (stateSectorSubmodule S).subtype C.referenceState
    (f := fun x => jointResidual S P (x, z.2))).mpr hdir

/-- Every sector state in the coupled neighborhood has the same exact
ambient line derivative, via its translated sector coordinates. -/
theorem coupled_recovered_hasLineDerivAt_ambient
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h3 : N03Properties D T S C R L base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (h9 : N09Properties D T S C R G B N V base ε q0)
    {z : AnnularState S × ℝ} (hz : z ∈ coupledNeighborhood S C base ε q0)
    (hs : stateSector S z.1) (y e : ResidualSpace S)
    (heScalar : ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode e.1.val p =
        z.2 * scalarCorrectionError (residualErrorCoefficient D S C z)
          (scalarResidualField D S C z) (heightPairField S (V.V z y).1) p +
        (S.height (3 / 4 : ℝ)).decode ((L.error z (R.residual z) (V.V z y).1).val) p)
    (heCircle : e.2.val = R.error z (R.residual z)
      (R.inverse (y.2.val - z.2 • B.heightRow z (V.V z y).1 -
        B.circleColumn z (V.V z y).2.2.1))) :
    HasProjectiveLineDerivAt (fun x => jointResidual S P (x, z.2)) (y + e)
      z.1 (V.V z y) := by
  let d : StateDirections S := ⟨z.1 - C.referenceState,
    (stateSectorSubmodule S).sub_mem hs h1.2.2.1.stateSector⟩
  let a : StateDirections S × ℝ := (d, z.2)
  have ha : a ∈ sectorNeighborhood S base ε q0 := ⟨hz.1, hz.2⟩
  have hlift : liftSectorParameter S C a = z := by
    apply Prod.ext
    · change C.referenceState + (z.1 - C.referenceState) = z.1
      exact (add_sub_assoc C.referenceState z.1 C.referenceState).symm.trans
        (add_sub_cancel_left C.referenceState z.1)
    · rfl
  have hd := coupled_recovered_hasLineDerivAt hT hS h1 h2 h3 hG h8 h9 ha y e
    (by simpa only [hlift] using heScalar)
    (by simpa only [hlift] using heCircle)
  simpa only [hlift] using hd

end ContinuousFlexibility.Statements
