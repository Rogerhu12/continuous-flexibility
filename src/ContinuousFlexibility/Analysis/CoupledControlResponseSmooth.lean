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

section AbstractResponse

variable {X E Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {bond : ∀ n, F (n + 1) →L[ℝ] F n}

private theorem coupled_response_fst_smoothTameOn
    {p : ℕ → Seminorm ℝ X} {r : ℕ → Seminorm ℝ E} {s : ℕ → Seminorm ℝ Y}
    {q : ℕ → Seminorm ℝ (ProjectiveLimit F bond)}
    (hp : Monotone p) (htp : WithSeminorms p)
    (hr : Monotone r) (htr : WithSeminorms r) (hts : WithSeminorms s)
    {U : Set X} (hU : IsOpen U)
    {column : X → E → Y} {response : X → Y → (ProjectiveLimit F bond × ℝ) × ℝ}
    (hcolumn : SmoothTameOn (pairGrading p r) s (U ×ˢ univ)
      (fun z : X × E => column z.1 z.2))
    (hresponse : SmoothTameOn (pairGrading p s) (pairGrading (pairGrading q realGrading) realGrading)
      (U ×ˢ univ) (fun z : X × Y => response z.1 z.2)) :
    SmoothTameOn (pairGrading p r) (pairGrading q realGrading) (U ×ˢ univ)
      (fun z : X × E => (response z.1 (column z.1 z.2)).1) := by
  have hpr := tamePairGrading_monotone hp hr
  have htpr := withSeminorms_pairGrading htp htr
  have htps := withSeminorms_pairGrading htp hts
  letI : LocallyConvexSpace ℝ (X × Y) := htps.toLocallyConvexSpace
  have hfst : SmoothTameOn (pairGrading p r) p (U ×ˢ univ) (fun z : X × E => z.1) :=
    smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
      (ContinuousLinearMap.fst ℝ X E) (scalar_pair_fst_isTame p r)
  have hin := smoothTameOn_prodMk_generic hpr htpr hfst hcolumn
  let LH : ((ProjectiveLimit F bond × ℝ) × ℝ) →L[ℝ] ProjectiveLimit F bond :=
    (ContinuousLinearMap.fst ℝ (ProjectiveLimit F bond) ℝ).comp
      (ContinuousLinearMap.fst ℝ (ProjectiveLimit F bond × ℝ) ℝ)
  let LC : ((ProjectiveLimit F bond × ℝ) × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ProjectiveLimit F bond) ℝ).comp
      (ContinuousLinearMap.fst ℝ (ProjectiveLimit F bond × ℝ) ℝ)
  have hLH : ∀ n y, q n (LH y) ≤
      1 * pairGrading (pairGrading q realGrading) realGrading n y := by
    intro n y
    simp only [LH, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      pairGrading_apply, one_mul]
    exact (le_add_of_nonneg_right (apply_nonneg (realGrading n) y.1.2)).trans
      (le_add_of_nonneg_right (apply_nonneg (realGrading n) y.2))
  have hLC : ∀ n y, realGrading n (LC y) ≤
      1 * pairGrading (pairGrading q realGrading) realGrading n y := by
    intro n y
    simp only [LC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', pairGrading_apply, one_mul]
    exact (le_add_of_nonneg_left (apply_nonneg (q n) y.1.1)).trans
      (le_add_of_nonneg_right (apply_nonneg (realGrading n) y.2))
  have hH := smoothTameOn_comp_generic hpr htpr htps hin
    (solve_smoothTameOn_postcomp hresponse LH zero_le_one hLH)
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hC := coupled_smoothTameOn_comp_banach hpr htpr htps hin
    (solve_smoothTameOn_postcomp hresponse LC zero_le_one hLC)
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  apply smoothTameOn_congr (smoothTameOn_prodMk_generic hpr htpr hH hC)
  intro z hz
  simp only [Function.comp_def, LH, LC, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.eta]

end AbstractResponse

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
  letI : ∀ n, CompleteSpace ((S.height (3 / 4 : ℝ)).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 (3 / 4 : ℝ)) n
  have h := coupled_response_fst_smoothTameOn
    (p := pairGrading (sectorGrading S) realGrading)
    (r := controlGrading) (s := S.sourceGrading)
    (F := fun n => ↥((S.height (3 / 4 : ℝ)).level n))
    (bond := (S.height (3 / 4 : ℝ)).bond)
    (q := (S.height (3 / 4 : ℝ)).grading)
    (column := fun z u => B.heightColumn (liftSectorParameter S C z) u)
    (response := fun z f => G.G (liftSectorParameter S C z) f)
    (tamePairGrading_monotone (solve_sectorGrading_monotone S) weighted_realGrading_monotone)
    (withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms)
    coupled_controlGrading_monotone coupled_controlGrading_withSeminorms
    (coupled_sourceGrading_withSeminorms S) hU hcolumn hG
  apply smoothTameOn_congr h
  intro z hz
  exact (controlHeightResponse_apply B G (liftSectorParameter S C z.1) z.2).symm

end ContinuousFlexibility.Statements
