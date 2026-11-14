module

public import ContinuousFlexibility.Analysis.CoupledFirstJetColumns

/-!
# The recovered increment in the genuine first jet

The height equation, the two control columns, and the chart equation
identify one and the same first directional derivative. The error entries
are independent source and even-circle values with the exact physical
formulas; no differentiability of a proposed formal linearization is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {G : ScalarInverseData S}
  {P : ResidualData S} {B : ControlColumnData S}
  {N : ControlInverseData S} {V : CoupledInverseData S}
  {base loss : ℕ} {ε q0 : ℝ}

theorem coupled_liftSectorParameter_mem_coupledNeighborhood
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε q0) :
    liftSectorParameter S C z ∈ coupledNeighborhood S C base ε q0 := by
  refine ⟨?_, hz.2⟩
  simpa only [liftSectorParameter, add_sub_cancel_left, sectorGrading,
    Seminorm.comp_apply, Submodule.subtype_apply] using hz.1

private theorem coupled_firstJet_map_four
    {X E : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup E] [Module ℝ E]
    (Φ : X →ₗ[ℝ] E) {v a b c d : X} (hv : v = a + b + c + d) :
    Φ v = Φ a + Φ b + Φ c + Φ d := by
  rw [hv, map_add, map_add, map_add]

private theorem coupled_firstJet_four_evaluations
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {U : Set (StateDirections S × ℝ)}
    (J : SmoothDirections U (sectorJointResidual S C P))
    (z : StateDirections S × ℝ) (v : StateDirections S)
    (out : ResidualSpace S →ₗ[ℝ] E) :
    out (projectiveJetHeadLinear J.D 0 z Fin.elim0 (v, 0)) =
      out (projectiveJetHeadLinear J.D 0 z Fin.elim0
        (coupledSectorHeightDirection S v.val.1, 0)) +
      out (projectiveJetHeadLinear J.D 0 z Fin.elim0
        (coupledSectorNuDirection S v.val.2.1, 0)) +
      out (projectiveJetHeadLinear J.D 0 z Fin.elim0
        (coupledSectorKappaDirection S v.val.2.2.1 v.property.1, 0)) +
      out (projectiveJetHeadLinear J.D 0 z Fin.elim0
        (coupledSectorChartDirection S v.val.2.2.2 v.property.2, 0)) := by
  let Φ : StateDirections S →ₗ[ℝ] E := out.comp
    ((projectiveJetHeadLinear J.D 0 z Fin.elim0).toLinearMap.comp
      (LinearMap.inl ℝ (StateDirections S) ℝ))
  exact coupled_firstJet_map_four Φ (coupled_sector_direction_decomposition v)

private theorem coupled_scalar_numeric_recovery {a e n k rhs : ℝ}
    (h : a + e + n + k = rhs) : a + e + n + k + 0 = rhs := by
  simpa only [add_zero] using h

/-- Scalar recovery is identified in the original source space by actual
point evaluations on the annulus. -/
theorem coupled_recovered_scalar_firstJet
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h3 : N03Properties D T S C R L base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (h9 : N09Properties D T S C R G B N V base ε q0)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε q0)
    (y : ResidualSpace S) (e : S.Source)
    (he : ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode e.val p =
        z.2 * scalarCorrectionError
          (residualErrorCoefficient D S C (liftSectorParameter S C z))
          (scalarResidualField D S C (liftSectorParameter S C z))
          (heightPairField S (V.V (liftSectorParameter S C z) y).1) p +
        (S.height (3 / 4 : ℝ)).decode
          ((L.error (liftSectorParameter S C z) (R.residual (liftSectorParameter S C z))
            (V.V (liftSectorParameter S C z) y).1).val) p) :
    (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (⟨V.V (liftSectorParameter S C z) y,
        (h9.2.2.2.2.1 _ (coupled_liftSectorParameter_mem_coupledNeighborhood hz)
          (h1.2.2.1.liftSectorParameter_sector z) y).1⟩, 0)).1 = y.1 + e := by
  let x := liftSectorParameter S C z
  have hx := coupled_liftSectorParameter_mem_coupledNeighborhood (C := C) hz
  have hs := h1.2.2.1.liftSectorParameter_sector z
  have hz0 : z ∈ sectorNeighborhood S base ε ε := ⟨hz.1, hz.2.trans_le h9.2.1⟩
  have hx0 := liftSectorParameter_mem_stateNeighborhood (C := C) hz h9.2.1
  let w := V.V x y
  have hr := h9.2.2.2.2.1 x hx hs y
  let v : StateDirections S := ⟨w, hr.1⟩
  apply coupled_source_ext hS
  intro p hp
  let out : ResidualSpace S →ₗ[ℝ] ℝ :=
    (coupledSourceEvaluation S p).comp (LinearMap.fst ℝ S.Source (EvenCircle S))
  have hsum := coupled_firstJet_four_evaluations J z v out
  change (coupledSourceEvaluation S p)
      (projectiveJetHeadLinear J.D 0 z Fin.elim0 (v, 0)).1 = _
  have hheight := coupled_scalar_height_firstJet_decode hT hS h1 h8.2.2.1 J hz0 w.1 hp
  have hnu := coupled_scalar_nu_firstJet h8 J hz0 w.2.1
  have hkappa := coupled_scalar_kappa_firstJet h1.2.2.1 h8 J hz0 w.2.2.1 hr.1.1
  have hchart := coupled_scalar_chart_firstJet_eq_zero hS h1.2.2.1 h8.2.2.1
    J hz0 w.2.2.2 hr.1.2
  have hN : (coupledSourceEvaluation S p)
      (projectiveJetHeadLinear J.D 0 z Fin.elim0
        (coupledSectorNuDirection S w.2.1, 0)).1 =
      w.2.1 * nuColumnField D S C x p := by
    calc
      _ = (coupledSourceEvaluation S p) (w.2.1 • B.nuColumn x) :=
        congrArg (coupledSourceEvaluation S p) hnu
      _ = w.2.1 • (coupledSourceEvaluation S p) (B.nuColumn x) :=
        (coupledSourceEvaluation S p).map_smul _ _
      _ = w.2.1 * nuColumnField D S C x p :=
        congrArg (w.2.1 * ·) (h8.2.2.2.2.2.2.1 x hx0 hs p hp)
  have hK : (coupledSourceEvaluation S p)
      (projectiveJetHeadLinear J.D 0 z Fin.elim0
        (coupledSectorKappaDirection S w.2.2.1 hr.1.1, 0)).1 =
      (coupledSourceEvaluation S p) (B.heightColumn x (controlSolution S B G N x y)) := by
    exact (congrArg (coupledSourceEvaluation S p) hkappa).trans
      (congrArg (fun u => (coupledSourceEvaluation S p) (B.heightColumn x u)) hr.2.1)
  have hC : (coupledSourceEvaluation S p)
      (projectiveJetHeadLinear J.D 0 z Fin.elim0
        (coupledSectorChartDirection S w.2.2.2 hr.1.2, 0)).1 = 0 :=
    (congrArg (coupledSourceEvaluation S p) hchart).trans (map_zero _)
  have hsolve := coupled_scalar_equation_with_return_error
    (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
    (G := G) (B := B) (N := N) (V := V) h3 hG h9 hx hs y e
    (fun p => z.2 * scalarCorrectionError (residualErrorCoefficient D S C x)
      (scalarResidualField D S C x) (heightPairField S w.1) p) he hp
  change (coupledSourceEvaluation S p)
      (projectiveJetHeadLinear J.D 0 z Fin.elim0 (v, 0)).1 =
    (coupledSourceEvaluation S p) (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (coupledSectorHeightDirection S w.1, 0)).1 +
    (coupledSourceEvaluation S p) (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (coupledSectorNuDirection S w.2.1, 0)).1 +
    (coupledSourceEvaluation S p) (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (coupledSectorKappaDirection S w.2.2.1 hr.1.1, 0)).1 +
    (coupledSourceEvaluation S p) (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (coupledSectorChartDirection S w.2.2.2 hr.1.2, 0)).1 at hsum
  exact hsum.trans ((congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (congrArg₂ (· + ·) hheight hN) hK) hC).trans
      (coupled_scalar_numeric_recovery hsolve))

private theorem coupled_circle_numeric_recovery
    {E : Type*} [AddCommGroup E] (y H C e : E) :
    H + 0 + C + ((y - H - C) + e) = y + e := by abel

/-- The true chart derivative fills exactly the circle row left by the
height and constant control columns, including its original error. -/
theorem coupled_recovered_circle_firstJet
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (h9 : N09Properties D T S C R G B N V base ε q0)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε q0)
    (y : ResidualSpace S) (e : EvenCircle S)
    (he : e.val = R.error (liftSectorParameter S C z) (R.residual (liftSectorParameter S C z))
      (R.inverse (y.2.val - z.2 • B.heightRow (liftSectorParameter S C z)
        (V.V (liftSectorParameter S C z) y).1 - B.circleColumn (liftSectorParameter S C z)
          (V.V (liftSectorParameter S C z) y).2.2.1))) :
    (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (⟨V.V (liftSectorParameter S C z) y,
        (h9.2.2.2.2.1 _ (coupled_liftSectorParameter_mem_coupledNeighborhood hz)
          (h1.2.2.1.liftSectorParameter_sector z) y).1⟩, 0)).2 = y.2 + e := by
  let x := liftSectorParameter S C z
  have hx := coupled_liftSectorParameter_mem_coupledNeighborhood (C := C) hz
  have hs := h1.2.2.1.liftSectorParameter_sector z
  have hz0 : z ∈ sectorNeighborhood S base ε ε := ⟨hz.1, hz.2.trans_le h9.2.1⟩
  let w := V.V x y
  let f := y.2.val - z.2 • B.heightRow x w.1 - B.circleColumn x w.2.2.1
  have hr := h9.2.2.2.2.1 x hx hs y
  let v : StateDirections S := ⟨w, hr.1⟩
  let out : ResidualSpace S →ₗ[ℝ] CircleSpace S :=
    (evenCircleSubmodule S).subtype.comp (LinearMap.snd ℝ S.Source (EvenCircle S))
  have hsum := coupled_firstJet_four_evaluations J z v out
  have hheight := coupled_circle_height_firstJet h1.2.2.1 h8 J hz0 w.1
  have hnu : (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (coupledSectorNuDirection S w.2.1, 0)).2.val = 0 :=
    congrArg Subtype.val (coupled_circle_nu_firstJet_eq_zero hT hS h1 h2
      h8.2.2.2.1 J hz0 w.2.1)
  have hkappa := coupled_circle_kappa_firstJet h1.2.2.1 h8 J hz0 w.2.2.1 hr.1.1
  have hchart0 := coupled_recovered_chart_derivative
    (D := D) (T := T) (S := S) (C := C) (R := R) (G := G) (B := B) (N := N)
    (V := V) h2 h9 hx hs y
  have hchart := coupled_circle_firstJet_of_return_derivative h1.2.2.1 h8.2.2.2.1
    J hz0 (coupledSectorChartDirection S w.2.2.2 hr.1.2)
    (f + R.error x (R.residual x) (R.inverse f)) hchart0
  have hchart' : (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (coupledSectorChartDirection S w.2.2.2 hr.1.2, 0)).2.val = f + e.val :=
    hchart.trans (congrArg (f + ·) he.symm)
  apply Subtype.ext
  change (projectiveJetHeadLinear J.D 0 z Fin.elim0 (v, 0)).2.val = y.2.val + e.val
  exact hsum.trans ((congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (congrArg₂ (· + ·) hheight hnu) hkappa) hchart').trans
      (coupled_circle_numeric_recovery y.2.val (z.2 • B.heightRow x w.1)
        (B.circleColumn x w.2.2.1) e.val))

end ContinuousFlexibility.Statements
