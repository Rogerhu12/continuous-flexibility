import ContinuousFlexibility.Analysis.SolveCircleProjection
import ContinuousFlexibility.Analysis.SolveSmoothing
import ContinuousFlexibility.Analysis.ProjectiveNewtonTameData
import ContinuousFlexibility.Statements.Nonlinear

/-!
# The sector state space used by the nonlinear iteration

The state grading defines the ordinary product topology. Angular averaging
and the odd projection provide a tame projection onto the sector, so its
closed subspace inherits smoothing from the physical height and circle models.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology NNReal
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

section PairMap

variable {E F G H : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
  [AddCommGroup H] [Module ℝ H]

/-- The product of tame linear maps for sum gradings has a single fixed
loss and base, just as the factors do. -/
theorem solve_isTameLinear_prodMap
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {r : ℕ → Seminorm ℝ G} {s : ℕ → Seminorm ℝ H}
    {L : E →ₗ[ℝ] G} {M : F →ₗ[ℝ] H} {l₁ l₂ b₁ b₂ : ℕ}
    (hp : Monotone p) (hq : Monotone q)
    (hL : IsTameLinear p r L l₁ b₁) (hM : IsTameLinear q s M l₂ b₂) :
    IsTameLinear (pairGrading p q) (pairGrading r s) (L.prodMap M)
      (max l₁ l₂) (max b₁ b₂) := by
  intro n hn
  obtain ⟨C, hC⟩ := hL n (le_of_max_le_left hn)
  obtain ⟨D, hD⟩ := hM n (le_of_max_le_right hn)
  refine ⟨C + D, fun x => ?_⟩
  change r n (L x.1) + s n (M x.2) ≤
    ((C + D : ℝ≥0) : ℝ) * (p (n + max l₁ l₂) x.1 + q (n + max l₁ l₂) x.2)
  have hc : r n (L x.1) ≤ (C : ℝ) * p (n + max l₁ l₂) x.1 :=
    (hC x.1).trans (mul_le_mul_of_nonneg_left
      (hp (Nat.add_le_add_left (le_max_left l₁ l₂) n) x.1) C.coe_nonneg)
  have hd : s n (M x.2) ≤ (D : ℝ) * q (n + max l₁ l₂) x.2 :=
    (hD x.2).trans (mul_le_mul_of_nonneg_left
      (hq (Nat.add_le_add_left (le_max_right l₁ l₂) n) x.2) D.coe_nonneg)
  have hpc := apply_nonneg (p (n + max l₁ l₂)) x.1
  have hqc := apply_nonneg (q (n + max l₁ l₂)) x.2
  rw [NNReal.coe_add]
  nlinarith only [hc, hd, mul_nonneg C.coe_nonneg hqc, mul_nonneg D.coe_nonneg hpc]

end PairMap

private theorem solve_realGrading_monotone : Monotone realGrading := fun _ _ _ _ => le_rfl

private theorem solve_realGrading_withSeminorms : WithSeminorms realGrading := by
  apply (norm_withSeminorms ℝ ℝ).congr
  · intro n
    exact ⟨{()}, 1, by simp [realGrading]⟩
  · intro u
    exact ⟨{0}, 1, by simp [realGrading]⟩

theorem solve_stateGrading_monotone (S : PhysicalSpacesData) : Monotone (stateGrading S) :=
  pairGrading_monotone
    (pairGrading_monotone (gradedSeminorm_monotone _ _) solve_realGrading_monotone)
    (pairGrading_monotone solve_realGrading_monotone
      (pairGrading_monotone (gradedSeminorm_monotone _ _) (gradedSeminorm_monotone _ _)))

theorem solve_stateGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms (stateGrading S) :=
  withSeminorms_pairGrading
    (withSeminorms_pairGrading (withSeminorms_graded _ _) solve_realGrading_withSeminorms)
    (withSeminorms_pairGrading solve_realGrading_withSeminorms
      (withSeminorms_pairGrading (withSeminorms_graded _ _) (withSeminorms_graded _ _)))

theorem solve_sectorGrading_monotone (S : PhysicalSpacesData) : Monotone (sectorGrading S) :=
  fun _ _ h x => solve_stateGrading_monotone S h x.val

theorem solve_sectorGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms (sectorGrading S) :=
  (Topology.IsInducing.subtypeVal).withSeminorms
    (f := (stateSectorSubmodule S).subtype) (solve_stateGrading_withSeminorms S)

theorem solve_state_hasSmoothing {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) :
    HasSmoothing (stateGrading S) :=
  hasSmoothing_pairGrading
    (hasSmoothing_pairGrading ((hS.2.2.2.1 (3 / 4 : ℝ)).2.1) hasSmoothing_realGrading)
    (hasSmoothing_pairGrading hasSmoothing_realGrading
      (hasSmoothing_pairGrading ((hS.2.2.2.2.1 (3 / 4 : ℝ)).2.1)
        ((hS.2.2.2.2.1 (3 / 4 : ℝ)).2.1)))

set_option diagnostics true in
/-- The physical sector is a tame direct summand, with the prescribed
constant control mode and odd chart mode. -/
theorem solve_sector_hasSmoothing {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) :
    HasSmoothing (sectorGrading S) := by
  have hparity := solve_parityProjection_data (D := D) (T := T) (S := S) hS (3 / 4 : ℝ)
  rcases hparity with ⟨even, odd, heven, hodd, hidem, hevenTame, hoddTame⟩
  rcases hoddTame with ⟨r, b, hoddTame⟩
  have hCM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
  have hmeanExists :
      ∃ mean : CircleSpace S →L[ℝ] CircleSpace S,
        (∀ u m θ φ, (S.circle (3 / 4 : ℝ)).decode (mean u) m θ =
          (S.circle (3 / 4 : ℝ)).decode (mean u) m φ) ∧
        (∀ u, (∀ m θ φ, (S.circle (3 / 4 : ℝ)).decode u m θ =
          (S.circle (3 / 4 : ℝ)).decode u m φ) → mean u = u) ∧
        IsTameLinear (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading
          mean.toLinearMap 0 0 :=
    ⟨circleAngularMeanProjection (T := T) (γ := 3 / 4) (S := S.circle (3 / 4)) hCM,
      circleAngularMeanProjection_constant hCM,
      circleAngularMeanProjection_eq_self hCM,
      circleAngularMeanProjection_isTame hCM⟩
  rcases hmeanExists with ⟨mean, hmean, hmeanFix, hmeanTame⟩
  let P : AnnularState S →L[ℝ] AnnularState S :=
    (ContinuousLinearMap.id ℝ (HeightPair S)).prodMap
      ((ContinuousLinearMap.id ℝ ℝ).prodMap (mean.prodMap odd))
  have hP (x : AnnularState S) : P x = (x.1, x.2.1, mean x.2.2.1, odd x.2.2.2) := by
    simp only [P, ContinuousLinearMap.coe_prodMap', Prod.map_apply',
      ContinuousLinearMap.id_apply]
  have hPmem (x : AnnularState S) : P x ∈ stateSectorSubmodule S := by
    have hstate : stateSector S (x.1, x.2.1, mean x.2.2.1, odd x.2.2.2) := by
      constructor
      · intro m θ φ
        exact hmean x.2.2.1 m θ φ
      · intro m θ
        change (S.circle (3 / 4 : ℝ)).decode (odd x.2.2.2) m (-θ) =
          -(S.circle (3 / 4 : ℝ)).decode (odd x.2.2.2) m θ
        rw [hodd, hodd, neg_neg]
        ring
    exact (congrArg (stateSector S) (hP x)).mpr hstate
  have hPid (x : AnnularState S) (hx : x ∈ stateSectorSubmodule S) : P x = x := by
    have hm := hmeanFix x.2.2.1 hx.1
    have ho : odd x.2.2.2 = x.2.2.2 := by
      apply hCM.2.2.2.2.2.1
      funext m θ
      rw [hodd, hx.2 m θ]
      ring
    exact (hP x).trans (Prod.ext rfl (Prod.ext rfl (Prod.ext hm ho)))
  have hpair := solve_isTameLinear_prodMap
    (gradedSeminorm_monotone _ _) (gradedSeminorm_monotone _ _)
    hmeanTame hoddTame
  have hrest := solve_isTameLinear_prodMap solve_realGrading_monotone
    (pairGrading_monotone (gradedSeminorm_monotone _ _) (gradedSeminorm_monotone _ _))
    (IsTameLinear.id realGrading) hpair
  have hfull := solve_isTameLinear_prodMap
    (pairGrading_monotone (gradedSeminorm_monotone _ _) solve_realGrading_monotone)
    (pairGrading_monotone solve_realGrading_monotone
      (pairGrading_monotone (gradedSeminorm_monotone _ _) (gradedSeminorm_monotone _ _)))
    (IsTameLinear.id (heightPairGrading S)) hrest
  have hPt : IsTameLinear (stateGrading S) (stateGrading S) P.toLinearMap r b := by
    simpa only [P, ContinuousLinearMap.coe_prodMap, ContinuousLinearMap.coe_id,
      Nat.zero_max] using hfull
  exact hasSmoothing_submodule_of_tame_projection (solve_stateGrading_monotone S)
    (stateSectorSubmodule S) P hPmem hPid hPt
    (solve_state_hasSmoothing (D := D) (T := T) (S := S) hS)

end ContinuousFlexibility.Analysis
