import ContinuousFlexibility.Analysis.CoupledControlCircleDerivative
import ContinuousFlexibility.Analysis.CoupledControlResponseSmooth
import ContinuousFlexibility.Analysis.CoupledPhysicalTameComposition
import ContinuousFlexibility.Analysis.CoupledNeighborhoodRestriction

/-!
# Smooth tame components of any N09 inverse

The component maps come from the sector-valued inverse in N09. The
constant control is lifted by its actual angular mean, and the circle
solution is formed by applying the given return inverse to the actual
remainder. No particular construction of the N09 inverse is required.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
  {N : ControlInverseData S} {V : CoupledInverseData S}
  {base loss : ℕ} {ε q0 : ℝ}

private theorem coupled_recoveredState_smoothTameOn
    (h9 : N09Properties D T S C R G B N V base ε q0) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (stateGrading S) (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        V.V (liftSectorParameter S C z.1) z.2) := by
  have h := solve_smoothTameOn_postcomp h9.2.2.2.2.2.2
    (stateSectorSubmodule S).subtypeL (r := stateGrading S) (B := 1) zero_le_one
    (fun n v => by change stateGrading S n v.val ≤ 1 * stateGrading S n v.val; rw [one_mul])
  exact smoothTameOn_congr h (fun z hz => h9.2.2.2.2.2.1 z.1 hz.1 z.2)

theorem coupled_recoveredHeight_smoothTameOn
    (h9 : N09Properties D T S C R G B N V base ε q0) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (heightPairGrading S) (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        (V.V (liftSectorParameter S C z.1) z.2).1) := by
  exact solve_smoothTameOn_postcomp (coupled_recoveredState_smoothTameOn h9)
    (ContinuousLinearMap.fst ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S)))
    (r := heightPairGrading S) (B := 1) zero_le_one (fun n x => by
      change heightPairGrading S n x.1 ≤ 1 * (heightPairGrading S n x.1 +
        pairGrading realGrading
          (pairGrading (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading) n x.2)
      rw [one_mul]
      exact le_add_of_nonneg_right (apply_nonneg _ _))

theorem coupled_recoveredKappa_smoothTameOn
    (h9 : N09Properties D T S C R G B N V base ε q0) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        (V.V (liftSectorParameter S C z.1) z.2).2.2.1) := by
  let K : AnnularState S →L[ℝ] CircleSpace S :=
    (ContinuousLinearMap.fst ℝ (CircleSpace S) (CircleSpace S)).comp
      ((ContinuousLinearMap.snd ℝ ℝ (CircleSpace S × CircleSpace S)).comp
        (ContinuousLinearMap.snd ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S))))
  have hK (x : AnnularState S) : K x = x.2.2.1 := by
    simp only [K, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
  have hb : ∀ n x, (S.circle (3 / 4 : ℝ)).grading n (K x) ≤ 1 * stateGrading S n x := by
    intro n x
    rw [hK, one_mul]
    change (S.circle (3 / 4 : ℝ)).grading n x.2.2.1 ≤ heightPairGrading S n x.1 +
      (realGrading n x.2.1 + ((S.circle (3 / 4 : ℝ)).grading n x.2.2.1 +
        (S.circle (3 / 4 : ℝ)).grading n x.2.2.2))
    exact (le_add_of_nonneg_right
      (apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) x.2.2.2)).trans
      ((le_add_of_nonneg_left (apply_nonneg (realGrading n) x.2.1)).trans
        (le_add_of_nonneg_left (apply_nonneg (heightPairGrading S n) x.1)))
  exact smoothTameOn_congr
    (solve_smoothTameOn_postcomp (coupled_recoveredState_smoothTameOn h9) K zero_le_one hb)
    (fun z _ => hK _)

def coupledRecoveredConstantComponent
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (C : NonlinearGeometryData S) (V : CoupledInverseData S)
    (z : StateDirections S × ℝ) (y : ResidualSpace S) : CoupledConstantCircle hM :=
  coupledConstantCircleProjection hM (V.V (liftSectorParameter S C z) y).2.2.1

theorem coupledRecoveredConstantComponent_val
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (h9 : N09Properties D T S C R G B N V base ε q0)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε q0)
    (y : ResidualSpace S) :
    (coupledRecoveredConstantComponent hM C V z y).val =
      (V.V (liftSectorParameter S C z) y).2.2.1 := by
  have hsector : stateSector S (V.V (liftSectorParameter S C z) y) := by
    rw [← h9.2.2.2.2.2.1 z hz y]
    exact (V.sectorV z y).property
  exact circleAngularMeanProjection_eq_self hM _ hsector.1

theorem coupled_recoveredConstantControl_smoothTameOn
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (h9 : N09Properties D T S C R G B N V base ε q0) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (coupledConstantCircleGrading hM) (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveredConstantComponent hM C V z.1 z.2) := by
  exact solve_smoothTameOn_postcomp (coupled_recoveredKappa_smoothTameOn h9)
    (coupledConstantCircleProjection hM) (r := coupledConstantCircleGrading hM)
    (B := 1) zero_le_one (fun n u => by
      change (S.circle (3 / 4 : ℝ)).grading n (coupledConstantCircleProjection hM u).val ≤ _
      rw [coupledConstantCircleProjection_val, one_mul]
      exact circleAngularMeanLinear_grading_le hM n u)

/-- The actual circle solution before the final chart increment is smooth
tame for any inverse satisfying N09. -/
theorem coupled_recoveredCircleSolution_smoothTameOn
    (hS : IsPhysicalSpaces D T S) (hRef : referenceStateConditions D S C)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (h9 : N09Properties D T S C R G B N V base ε q0) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        R.inverse (z.2.2.val - z.1.2 • B.heightRow (liftSectorParameter S C z.1)
          (V.V (liftSectorParameter S C z.1) z.2).1 -
          B.circleColumn (liftSectorParameter S C z.1)
            (V.V (liftSectorParameter S C z.1) z.2).2.2.1)) := by
  let hM := hS.2.1 (3 / 4 : ℝ)
  let U := sectorNeighborhood S base ε q0
  let p := pairGrading (sectorGrading S) realGrading
  let a := pairGrading p (residualGrading S)
  let c := (S.circle (3 / 4 : ℝ)).grading
  have hp : Monotone p := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have htp : WithSeminorms p := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  have hr : Monotone (residualGrading S) := tamePairGrading_monotone
    (fun _ _ h u => gradedSeminorm_monotone _ _ h u.val)
    (fun _ _ h u => gradedSeminorm_monotone _ _ h u.val)
  have htr : WithSeminorms (residualGrading S) := withSeminorms_pairGrading
    (coupled_sourceGrading_withSeminorms S)
    ((Topology.IsInducing.subtypeVal).withSeminorms
      (f := (evenCircleSubmodule S).subtype) (withSeminorms_graded _ _))
  have ha := tamePairGrading_monotone hp hr
  have hta := withSeminorms_pairGrading htp htr
  have htc : WithSeminorms c := withSeminorms_graded _ _
  have htph := withSeminorms_pairGrading htp (coupled_heightPairGrading_withSeminorms S)
  have htpk := withSeminorms_pairGrading htp (coupledConstantCircleGrading_withSeminorms hM)
  letI : LocallyConvexSpace ℝ ((StateDirections S × ℝ) × HeightPair S) :=
    htph.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ ((StateDirections S × ℝ) × CoupledConstantCircle hM) :=
    htpk.toLocallyConvexSpace
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    (hM.2.1 n).isComplete.completeSpace_coe
  have hU : IsOpen U := coupled_sectorNeighborhood_isOpen S base ε q0
  have hsub : U ⊆ sectorNeighborhood S base ε ε :=
    coupled_sectorNeighborhood_mono le_rfl le_rfl h9.2.1
  have hz : SmoothTameOn a p (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.1) :=
    smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
      (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) (ResidualSpace S))
      (scalar_pair_fst_isTame p (residualGrading S))
  have hy : SmoothTameOn a (residualGrading S) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.2) :=
    smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
      (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) (ResidualSpace S))
      (scalar_pair_snd_isTame p (residualGrading S))
  let LC : ResidualSpace S →L[ℝ] CircleSpace S :=
    (evenCircleSubmodule S).subtypeL.comp (ContinuousLinearMap.snd ℝ S.Source (EvenCircle S))
  have hyCircle : SmoothTameOn a c (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.2.2.val) := by
    exact solve_smoothTameOn_postcomp hy LC (r := c) (B := 1) zero_le_one (fun n y => by
      change c n y.2.val ≤ 1 * (S.sourceGrading n y.1 + c n y.2.val)
      rw [one_mul]
      exact le_add_of_nonneg_left (apply_nonneg (S.sourceGrading n) y.1))
  have hrow := smoothTameOn_mono (coupled_scaledHeightRow_smoothTameOn hRef h8)
    (hU.prod isOpen_univ) (Set.prod_mono hsub (subset_refl _))
  have hrowη := smoothTameOn_comp_generic ha hta htph
    (smoothTameOn_prodMk_generic ha hta hz (coupled_recoveredHeight_smoothTameOn h9)) hrow
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hcolumn := smoothTameOn_mono (coupled_constantCircleColumn_smoothTameOn hM hRef h8)
    (hU.prod isOpen_univ) (Set.prod_mono hsub (subset_refl _))
  have hcolumnκ := smoothTameOn_comp_generic ha hta htpk
    (smoothTameOn_prodMk_generic ha hta hz
      (coupled_recoveredConstantControl_smoothTameOn hM h9)) hcolumn
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hcolumnActual : SmoothTameOn a c (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        B.circleColumn (liftSectorParameter S C z.1)
          (V.V (liftSectorParameter S C z.1) z.2).2.2.1) := by
    apply smoothTameOn_congr hcolumnκ
    intro z hz
    exact congrArg (B.circleColumn (liftSectorParameter S C z.1))
      (coupledRecoveredConstantComponent_val hM h9 hz.1 z.2)
  have hrem := coupled_smoothTameOn_sub ha (coupled_smoothTameOn_sub ha hyCircle hrowη) hcolumnActual
  obtain ⟨li, bi, hi⟩ := h2.2.2.2.2.2.2.2.2.2.1
  let Inv : CircleSpace S →L[ℝ] CircleSpace S :=
    hi.toContinuousLinearMap htc htc (gradedSeminorm_monotone _ _)
  have hInv := smoothTameOn_comp_generic ha hta htc hrem
    (smoothTameOn_continuousLinear Inv hi) (fun _ _ => mem_univ _)
  apply smoothTameOn_congr hInv
  intro z hz
  exact IsTameLinear.toContinuousLinearMap_apply hi htc htc
    (gradedSeminorm_monotone _ _) _

end ContinuousFlexibility.Statements
