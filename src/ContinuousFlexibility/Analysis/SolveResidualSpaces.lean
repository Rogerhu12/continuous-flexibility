import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.ProjectiveLimitSubspace
import ContinuousFlexibility.Analysis.SolveSmoothing

/-!
# The actual residual space as a complete projective limit

The scalar component is the kernel of the compatibility functional and the
circle component is the even sector. Both are closed subspaces of the
physical projective limits. Their product has an exact projective realization;
the statement's sum grading and the resulting maximum grading differ by at
most a factor of two.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem solve_isClosed_evenCircle (hS : IsPhysicalSpaces D T S) :
    IsClosed (evenCircleSubmodule S : Set (CircleSpace S)) := by
  have hd := (hS.2.1 (3 / 4 : ℝ)).2.2.1
  change IsClosed {u : CircleSpace S | ∀ m θ,
    (S.circle (3 / 4 : ℝ)).decode u m (-θ) = (S.circle (3 / 4 : ℝ)).decode u m θ}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro m
  apply isClosed_iInter
  intro θ
  exact isClosed_eq ((continuous_apply (-θ)).comp ((continuous_apply m).comp hd))
    ((continuous_apply θ).comp ((continuous_apply m).comp hd))

/-- Levels for the actual two-component residual. -/
def SolveResidualLevel (S : PhysicalSpacesData) (n : ℕ) : Type :=
  subLevel (S.Q.toLinearMap.ker) n × subLevel (evenCircleSubmodule S) n

instance (S : PhysicalSpacesData) (n : ℕ) : NormedAddCommGroup (SolveResidualLevel S n) :=
  inferInstanceAs (NormedAddCommGroup
    (subLevel S.Q.toLinearMap.ker n × subLevel (evenCircleSubmodule S) n))

instance (S : PhysicalSpacesData) (n : ℕ) : NormedSpace ℝ (SolveResidualLevel S n) :=
  inferInstanceAs (NormedSpace ℝ
    (subLevel S.Q.toLinearMap.ker n × subLevel (evenCircleSubmodule S) n))

def solveResidualBond (S : PhysicalSpacesData) (n : ℕ) :
    SolveResidualLevel S (n + 1) →L[ℝ] SolveResidualLevel S n :=
  (subBond S.Q.toLinearMap.ker n).prodMap (subBond (evenCircleSubmodule S) n)

/-- The residual product is represented by the same actual weak graph
levels, followed by their closed scalar and parity subspaces. -/
def solveResidualEquiv (hS : IsPhysicalSpaces D T S) :
    ResidualSpace S ≃L[ℝ] ProjectiveLimit (SolveResidualLevel S) (solveResidualBond S) :=
  ((subspaceEquiv S.Q.toLinearMap.ker S.Q.isClosed_ker).prodCongr
    (subspaceEquiv (evenCircleSubmodule S) (solve_isClosed_evenCircle hS))).trans
    (prodEquiv (fun n => subLevel S.Q.toLinearMap.ker n) (subBond S.Q.toLinearMap.ker)
      (fun n => subLevel (evenCircleSubmodule S) n) (subBond (evenCircleSubmodule S)))

theorem solveResidualEquiv_grading (hS : IsPhysicalSpaces D T S)
    (n : ℕ) (y : ResidualSpace S) :
    gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n
        (solveResidualEquiv hS y) =
      max (S.sourceGrading n y.1)
        (((S.circle (3 / 4 : ℝ)).grading n) y.2.val) := by
  rw [solveResidualEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, gradedSeminorm_prodEquiv,
    gradedSeminorm_subspaceEquiv, gradedSeminorm_subspaceEquiv]
  rfl

theorem solveResidualEquiv_grading_le (hS : IsPhysicalSpaces D T S)
    (n : ℕ) (y : ResidualSpace S) :
    gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n
      (solveResidualEquiv hS y) ≤ residualGrading S n y := by
  rw [solveResidualEquiv_grading]
  change max _ _ ≤ _ + _
  exact max_le (le_add_of_nonneg_right (apply_nonneg _ _))
    (le_add_of_nonneg_left (apply_nonneg _ _))

theorem solve_residualGrading_le_two (hS : IsPhysicalSpaces D T S)
    (n : ℕ) (y : ResidualSpace S) :
    residualGrading S n y ≤
      2 * gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n
        (solveResidualEquiv hS y) := by
  rw [solveResidualEquiv_grading]
  change _ + _ ≤ 2 * max _ _
  linarith only [le_max_left (S.sourceGrading n y.1)
    (((S.circle (3 / 4 : ℝ)).grading n) y.2.val),
    le_max_right (S.sourceGrading n y.1) (((S.circle (3 / 4 : ℝ)).grading n) y.2.val)]

/-- The scalar compatibility subspace inherits smoothing from the actual
height model, through the projection already supplied in W02. -/
theorem solve_source_hasSmoothing (hS : IsPhysicalSpaces D T S) :
    HasSmoothing S.sourceGrading := by
  obtain ⟨P, _, hPker, hPid, r, b, hPt⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.1
  exact hasSmoothing_submodule_of_tame_projection
    (gradedSeminorm_monotone _ _) S.Q.toLinearMap.ker P
    (fun x => hPker x) (fun w hw => hPid w hw) hPt
    ((hS.2.2.2.1 (3 / 4 : ℝ)).2.1)

/-- The even residual circle sector uses its actual supplied parity
projection, retaining its fixed derivative loss. -/
theorem solve_even_hasSmoothing (hS : IsPhysicalSpaces D T S) :
    HasSmoothing (fun n => ((S.circle (3 / 4 : ℝ)).grading n).comp
      (evenCircleSubmodule S).subtype) := by
  obtain ⟨even, odd, heven, _, _, r, b, hPt, _⟩ :=
    hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (3 / 4 : ℝ)
  have hinj := (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  apply hasSmoothing_submodule_of_tame_projection (gradedSeminorm_monotone _ _)
    (evenCircleSubmodule S) even _ _ hPt
    ((hS.2.2.2.2.1 (3 / 4 : ℝ)).2.1)
  · intro u m θ
    rw [heven, heven, neg_neg]
    ring
  · intro u hu
    apply hinj
    funext m θ
    rw [heven, hu m θ]
    ring

theorem solve_residual_hasSmoothing (hS : IsPhysicalSpaces D T S) :
    HasSmoothing (residualGrading S) :=
  hasSmoothing_pairGrading (solve_source_hasSmoothing hS) (solve_even_hasSmoothing hS)

end ContinuousFlexibility.Analysis
