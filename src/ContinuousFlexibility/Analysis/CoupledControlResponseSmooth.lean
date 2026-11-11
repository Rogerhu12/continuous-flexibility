import ContinuousFlexibility.Analysis.CoupledControlAlgebra
import ContinuousFlexibility.Analysis.CoupledTameComposition
import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Scalar.WeightedStateTopology

/-!
# Smooth dependence of the actual height response to a control

The source column and the scalar inverse are composed on their original
spaces. The two height components are retained, including the left
constant. Only the already prescribed Banach levels are completed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem coupled_controlGrading_monotone : Monotone controlGrading :=
  fun _ _ _ _ => le_rfl

theorem coupled_controlGrading_withSeminorms : WithSeminorms controlGrading := by
  apply (norm_withSeminorms ℝ ControlBanach).congr
  · intro n
    exact ⟨{()}, 1, by simp [controlGrading]⟩
  · intro u
    exact ⟨{0}, 1, by simp [controlGrading]⟩

theorem coupled_sourceGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms S.sourceGrading :=
  (Topology.IsInducing.subtypeVal).withSeminorms
    (f := S.Q.toLinearMap.ker.subtype) (withSeminorms_graded _ _)

theorem coupled_heightPairGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms (heightPairGrading S) :=
  withSeminorms_pairGrading (withSeminorms_graded _ _)
    weighted_realGrading_withSeminorms

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {G : ScalarInverseData S} {B : ControlColumnData S}
  {U : Set (StateDirections S × ℝ)}

/-- The literal response `fst (G (heightColumn u))` is a smooth tame family
on the same sector domain. Its input is the full control Banach space. -/
theorem coupled_controlHeightResponse_smoothTameOn
    (hS : IsPhysicalSpaces D T S) (hU : IsOpen U)
    (hcolumn : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading)
      S.sourceGrading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ControlBanach =>
        B.heightColumn (liftSectorParameter S C z.1) z.2))
    (hG : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) S.sourceGrading)
      (pairGrading (heightPairGrading S) realGrading) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × S.Source =>
        G.G (liftSectorParameter S C z.1) z.2)) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading)
      (heightPairGrading S) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ControlBanach =>
        controlHeightResponse S B G (liftSectorParameter S C z.1) z.2) := by
  let p : ℕ → Seminorm ℝ (StateDirections S × ℝ) :=
    pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have htp : WithSeminorms p := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  have hpc : Monotone (pairGrading p controlGrading) :=
    tamePairGrading_monotone hp coupled_controlGrading_monotone
  have htpc : WithSeminorms (pairGrading p controlGrading) :=
    withSeminorms_pairGrading htp coupled_controlGrading_withSeminorms
  have htps : WithSeminorms (pairGrading p S.sourceGrading) :=
    withSeminorms_pairGrading htp (coupled_sourceGrading_withSeminorms S)
  letI : LocallyConvexSpace ℝ ((StateDirections S × ℝ) × S.Source) :=
    htps.toLocallyConvexSpace
  letI : ∀ n, CompleteSpace ((S.height (3 / 4 : ℝ)).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 (3 / 4 : ℝ)) n
  have hfst : SmoothTameOn (pairGrading p controlGrading) p (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ControlBanach => z.1) :=
    smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
      (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) ControlBanach)
      (scalar_pair_fst_isTame p controlGrading)
  have hin := smoothTameOn_prodMk_generic hpc htpc hfst hcolumn
  let LH : (HeightPair S × ℝ) →L[ℝ] (S.height (3 / 4 : ℝ)).Space :=
    (ContinuousLinearMap.fst ℝ (S.height (3 / 4 : ℝ)).Space ℝ).comp
      (ContinuousLinearMap.fst ℝ (HeightPair S) ℝ)
  let LC : (HeightPair S × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (S.height (3 / 4 : ℝ)).Space ℝ).comp
      (ContinuousLinearMap.fst ℝ (HeightPair S) ℝ)
  have hLH : ∀ n y, (S.height (3 / 4 : ℝ)).grading n (LH y) ≤
      1 * pairGrading (heightPairGrading S) realGrading n y := by
    intro n y
    simp only [LH, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      pairGrading_apply, heightPairGrading, one_mul]
    exact (le_add_of_nonneg_right (apply_nonneg (realGrading n) y.1.2)).trans
      (le_add_of_nonneg_right (apply_nonneg (realGrading n) y.2))
  have hLC : ∀ n y, realGrading n (LC y) ≤
      1 * pairGrading (heightPairGrading S) realGrading n y := by
    intro n y
    simp only [LC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', pairGrading_apply, heightPairGrading, one_mul]
    exact (le_add_of_nonneg_left
      (apply_nonneg ((S.height (3 / 4 : ℝ)).grading n) y.1.1)).trans
      (le_add_of_nonneg_right (apply_nonneg (realGrading n) y.2))
  have hGH := solve_smoothTameOn_postcomp hG LH zero_le_one hLH
  have hGC := solve_smoothTameOn_postcomp hG LC zero_le_one hLC
  have hmap : MapsTo
      (fun z : (StateDirections S × ℝ) × ControlBanach =>
        (z.1, B.heightColumn (liftSectorParameter S C z.1) z.2))
      (U ×ˢ univ) (U ×ˢ univ) := fun z hz => ⟨hz.1, mem_univ _⟩
  have hH := smoothTameOn_comp_generic hpc htpc htps hin hGH hmap
  have hC := coupled_smoothTameOn_comp_banach hpc htpc htps hin hGC hmap
  have hpair := smoothTameOn_prodMk_generic hpc htpc hH hC
  apply smoothTameOn_congr hpair
  intro z hz
  simp only [Function.comp_def, LH, LC, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    controlHeightResponse_apply, Prod.eta]

end ContinuousFlexibility.Statements
