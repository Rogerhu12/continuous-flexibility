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

section GenericProjections

variable {X E F : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ E} {r : ℕ → Seminorm ℝ F}
  {U : Set X}

private theorem coupled_recovery_fst_smoothTameOn {f : X → E × F}
    (hf : SmoothTameOn p (pairGrading q r) U f) :
    SmoothTameOn p q U (fun x => (f x).1) := by
  exact solve_smoothTameOn_postcomp hf (ContinuousLinearMap.fst ℝ E F)
    (B := 1) zero_le_one (fun n y => by
      change q n y.1 ≤ 1 * (q n y.1 + r n y.2)
      simpa only [one_mul] using le_add_of_nonneg_right (apply_nonneg (r n) y.2))

private theorem coupled_recovery_snd_smoothTameOn {f : X → E × F}
    (hf : SmoothTameOn p (pairGrading q r) U f) :
    SmoothTameOn p r U (fun x => (f x).2) := by
  exact solve_smoothTameOn_postcomp hf (ContinuousLinearMap.snd ℝ E F)
    (B := 1) zero_le_one (fun n y => by
      change r n y.2 ≤ 1 * (q n y.1 + r n y.2)
      simpa only [one_mul] using le_add_of_nonneg_left (apply_nonneg (q n) y.1))

private theorem coupled_recovery_subtype_smoothTameOn
    (W : Submodule ℝ E) {f : X → W}
    (hf : SmoothTameOn p (fun n => (q n).comp W.subtype) U f) :
    SmoothTameOn p q U (fun x => (f x).val) := by
  exact solve_smoothTameOn_postcomp hf W.subtypeL (B := 1) zero_le_one (fun n y => by
    change q n y.val ≤ 1 * q n y.val
    exact le_of_eq (one_mul _).symm)

private theorem coupled_recovery_constant_projection_smoothTameOn
    {T : MaterialData} {γ : ℝ} {M : CircleModelData} (hM : IsCircleModel T γ M)
    {f : X → M.Space} (hf : SmoothTameOn p M.grading U f) :
    SmoothTameOn p (coupledConstantCircleGrading hM) U
      (fun x => coupledConstantCircleProjection hM (f x)) := by
  exact solve_smoothTameOn_postcomp hf (coupledConstantCircleProjection hM)
    (B := 1) zero_le_one (fun n u => by
      change M.grading n (coupledConstantCircleProjection hM u).val ≤ 1 * M.grading n u
      exact (coupled_circleAngularMeanProjection_grading_le hM n u).trans_eq
        (one_mul _).symm)

end GenericProjections

section GenericRecoveryComposition

variable {X Y E : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {bond : ∀ n, F (n + 1) →L[ℝ] F n}

private theorem coupled_recovery_parameterApply_smoothTameOn
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ E}
    {s : ℕ → Seminorm ℝ (ProjectiveLimit F bond)}
    (hp : Monotone p) (htp : WithSeminorms p)
    (htq : WithSeminorms q) (htr : WithSeminorms r)
    {U : Set X} {V : Set Y} {parameter : X → Y} {value : X → E}
    {f : Y × E → ProjectiveLimit F bond}
    (hz : SmoothTameOn p q U parameter) (hv : SmoothTameOn p r U value)
    (hf : SmoothTameOn (pairGrading q r) s (V ×ˢ univ) f)
    (hmap : MapsTo parameter U V) :
    SmoothTameOn p s U (fun x => f (parameter x, value x)) := by
  letI : IsTopologicalAddGroup X := htp.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := htp.continuousSMul
  letI : IsTopologicalAddGroup Y := htq.isTopologicalAddGroup
  letI : ContinuousSMul ℝ Y := htq.continuousSMul
  letI : IsTopologicalAddGroup E := htr.isTopologicalAddGroup
  letI : ContinuousSMul ℝ E := htr.continuousSMul
  have htqr := withSeminorms_pairGrading htq htr
  letI : LocallyConvexSpace ℝ (Y × E) := htqr.toLocallyConvexSpace
  exact smoothTameOn_comp_generic hp htp htqr
    (smoothTameOn_prodMk_generic hp htp hz hv) hf
    (fun x hx => ⟨hmap hx, mem_univ _⟩)

private theorem coupled_recovery_inverse_remainder_smoothTameOn
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ (ProjectiveLimit F bond)}
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q) (hq : Monotone q)
    {U : Set X} {f g h : X → ProjectiveLimit F bond}
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn p q U g) (hh : SmoothTameOn p q U h)
    (L : ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond)
    {loss base : ℕ} (hL : IsTameLinear q q L loss base) :
    SmoothTameOn p q U (fun x => L (f x - g x - h x)) := by
  have hrem := coupled_smoothTameOn_sub hp (coupled_smoothTameOn_sub hp hf hg) hh
  let LC : ProjectiveLimit F bond →L[ℝ] ProjectiveLimit F bond :=
    hL.toContinuousLinearMap htq htq hq
  have hmain := smoothTameOn_postcompose_generic hp htp htq hrem LC hL
  exact smoothTameOn_congr hmain
    (fun x _ => IsTameLinear.toContinuousLinearMap_apply hL htq htq hq _)

end GenericRecoveryComposition

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
  have h := coupled_recovery_subtype_smoothTameOn
    (q := stateGrading S) (stateSectorSubmodule S) h9.2.2.2.2.2.2
  exact smoothTameOn_congr h (fun z hz => h9.2.2.2.2.2.1 z.1 hz.1 z.2)

theorem coupled_recoveredHeight_smoothTameOn
    (h9 : N09Properties D T S C R G B N V base ε q0) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (heightPairGrading S) (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        (V.V (liftSectorParameter S C z.1) z.2).1) := by
  exact coupled_recovery_fst_smoothTameOn (coupled_recoveredState_smoothTameOn h9)

theorem coupled_recoveredKappa_smoothTameOn
    (h9 : N09Properties D T S C R G B N V base ε q0) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        (V.V (liftSectorParameter S C z.1) z.2).2.2.1) := by
  exact coupled_recovery_fst_smoothTameOn
    (coupled_recovery_snd_smoothTameOn
      (coupled_recovery_snd_smoothTameOn (coupled_recoveredState_smoothTameOn h9)))

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
  have hsector : stateSector S (V.V (liftSectorParameter S C z) y) :=
    (congrArg (stateSector S) (h9.2.2.2.2.2.1 z hz y)).mp (V.sectorV z y).property
  exact circleAngularMeanProjection_eq_self hM _ hsector.1

theorem coupled_recoveredConstantControl_smoothTameOn
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (h9 : N09Properties D T S C R G B N V base ε q0) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (coupledConstantCircleGrading hM) (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveredConstantComponent hM C V z.1 z.2) := by
  exact coupled_recovery_constant_projection_smoothTameOn hM
    (coupled_recoveredKappa_smoothTameOn h9)

private theorem coupled_recovery_gradings (S : PhysicalSpacesData) :
    Monotone (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S)) ∧
    WithSeminorms (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S)) ∧
    WithSeminorms (pairGrading (sectorGrading S) realGrading) := by
  have hp := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have htp := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  have hr : Monotone (residualGrading S) := tamePairGrading_monotone
    (fun _ _ h u => gradedSeminorm_monotone _ _ h u.val)
    (fun _ _ h u => gradedSeminorm_monotone _ _ h u.val)
  have htr : WithSeminorms (residualGrading S) := withSeminorms_pairGrading
    (coupled_sourceGrading_withSeminorms S)
    ((Topology.IsInducing.subtypeVal).withSeminorms
      (f := (evenCircleSubmodule S).subtype) (withSeminorms_graded _ _))
  exact ⟨tamePairGrading_monotone hp hr, withSeminorms_pairGrading htp htr, htp⟩

private theorem coupled_recovery_parameterProjection_smoothTameOn
    (S : PhysicalSpacesData) (base : ℕ) (ε q0 : ℝ) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (pairGrading (sectorGrading S) realGrading) (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.1) :=
  smoothTameOn_continuousLinear_on
    ((coupled_sectorNeighborhood_isOpen S base ε q0).prod isOpen_univ)
    (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) (ResidualSpace S))
    (scalar_pair_fst_isTame (pairGrading (sectorGrading S) realGrading) (residualGrading S))

private theorem coupled_recovery_circleInput_smoothTameOn
    (S : PhysicalSpacesData) (base : ℕ) (ε q0 : ℝ) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.2.2.val) := by
  have hy : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (residualGrading S) (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.2) :=
    smoothTameOn_continuousLinear_on
      ((coupled_sectorNeighborhood_isOpen S base ε q0).prod isOpen_univ)
      (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) (ResidualSpace S))
      (scalar_pair_snd_isTame (pairGrading (sectorGrading S) realGrading) (residualGrading S))
  exact coupled_recovery_subtype_smoothTameOn (evenCircleSubmodule S)
    (coupled_recovery_snd_smoothTameOn hy)

private theorem coupled_recovery_heightRow_smoothTameOn
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hRef : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (h9 : N09Properties D T S C R G B N V base ε q0) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        z.1.2 • B.heightRow (liftSectorParameter S C z.1)
          (V.V (liftSectorParameter S C z.1) z.2).1) := by
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    (hM.2.1 n).isComplete.completeSpace_coe
  let hg := coupled_recovery_gradings S
  have hU := coupled_sectorNeighborhood_isOpen S base ε q0
  have hsub : sectorNeighborhood S base ε q0 ⊆ sectorNeighborhood S base ε ε :=
    coupled_sectorNeighborhood_mono le_rfl le_rfl h9.2.1
  have hrow := smoothTameOn_mono (coupled_scaledHeightRow_smoothTameOn hRef h8)
    (hU.prod isOpen_univ) (Set.prod_mono hsub (subset_refl (univ : Set (HeightPair S))))
  exact coupled_recovery_parameterApply_smoothTameOn hg.1 hg.2.1 hg.2.2
    (coupled_heightPairGrading_withSeminorms S)
    (coupled_recovery_parameterProjection_smoothTameOn S base ε q0)
    (coupled_recoveredHeight_smoothTameOn h9) hrow (fun z hz => hz.1)

private theorem coupled_recovery_circleColumn_smoothTameOn
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hRef : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (h9 : N09Properties D T S C R G B N V base ε q0) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        B.circleColumn (liftSectorParameter S C z.1)
          (V.V (liftSectorParameter S C z.1) z.2).2.2.1) := by
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    (hM.2.1 n).isComplete.completeSpace_coe
  let hg := coupled_recovery_gradings S
  have hU := coupled_sectorNeighborhood_isOpen S base ε q0
  have hsub : sectorNeighborhood S base ε q0 ⊆ sectorNeighborhood S base ε ε :=
    coupled_sectorNeighborhood_mono le_rfl le_rfl h9.2.1
  have hcolumn := smoothTameOn_mono (coupled_constantCircleColumn_smoothTameOn hM hRef h8)
    (hU.prod isOpen_univ)
    (Set.prod_mono hsub (subset_refl (univ : Set (CoupledConstantCircle hM))))
  have hconstant := coupled_recovery_parameterApply_smoothTameOn hg.1 hg.2.1 hg.2.2
    (coupledConstantCircleGrading_withSeminorms hM)
    (coupled_recovery_parameterProjection_smoothTameOn S base ε q0)
    (coupled_recoveredConstantControl_smoothTameOn hM h9) hcolumn (fun z hz => hz.1)
  exact smoothTameOn_congr hconstant (fun z hz =>
    congrArg (B.circleColumn (liftSectorParameter S C z.1))
      (coupledRecoveredConstantComponent_val hM h9 hz.1 z.2))

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
  let hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    (hM.2.1 n).isComplete.completeSpace_coe
  let hg := coupled_recovery_gradings S
  let hinverse := h2.2.2.2.2.2.2.2.2.2.1
  let li : ℕ := hinverse.choose
  let hbase := hinverse.choose_spec
  let bi : ℕ := hbase.choose
  have hi : IsTameLinear (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading
      R.inverse li bi := hbase.choose_spec
  exact coupled_recovery_inverse_remainder_smoothTameOn hg.1 hg.2.1
    (withSeminorms_graded _ _) (gradedSeminorm_monotone _ _)
    (coupled_recovery_circleInput_smoothTameOn S base ε q0)
    (coupled_recovery_heightRow_smoothTameOn hM hRef h8 h9)
    (coupled_recovery_circleColumn_smoothTameOn hM hRef h8 h9) R.inverse hi

end ContinuousFlexibility.Statements
