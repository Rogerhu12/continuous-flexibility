import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.ProjectiveLimitSubspace
import ContinuousFlexibility.Analysis.SolveSmoothing
import ContinuousFlexibility.Analysis.SolveCircleProjection

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

private theorem solveResidualEquiv_apply (hS : IsPhysicalSpaces D T S)
    (y : ResidualSpace S) :
    solveResidualEquiv hS y =
      prodEquiv (fun n => subLevel S.Q.toLinearMap.ker n) (subBond S.Q.toLinearMap.ker)
        (fun n => subLevel (evenCircleSubmodule S) n) (subBond (evenCircleSubmodule S))
        (subspaceEquiv S.Q.toLinearMap.ker S.Q.isClosed_ker y.1,
          subspaceEquiv (evenCircleSubmodule S) (solve_isClosed_evenCircle hS) y.2) := by
  unfold solveResidualEquiv
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply]

-- Keep later comparisons from unfolding the inverse of the bundled equivalence.
attribute [irreducible] solveResidualEquiv

theorem solveResidualEquiv_grading (hS : IsPhysicalSpaces D T S)
    (n : ℕ) (y : ResidualSpace S) :
    gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n
        (solveResidualEquiv hS y) =
      max (S.sourceGrading n y.1)
        (((S.circle (3 / 4 : ℝ)).grading n) y.2.val) := by
  have hsource :
      gradedSeminorm (fun k => subLevel S.Q.toLinearMap.ker k)
        (subBond S.Q.toLinearMap.ker) n
        (subspaceEquiv S.Q.toLinearMap.ker S.Q.isClosed_ker y.1) =
      S.sourceGrading n y.1 :=
    gradedSeminorm_subspaceEquiv S.Q.toLinearMap.ker S.Q.isClosed_ker y.1 n
  have hcircle :
      gradedSeminorm (fun k => subLevel (evenCircleSubmodule S) k)
        (subBond (evenCircleSubmodule S)) n
        (subspaceEquiv (evenCircleSubmodule S) (solve_isClosed_evenCircle hS) y.2) =
      ((S.circle (3 / 4 : ℝ)).grading n) y.2.val :=
    gradedSeminorm_subspaceEquiv (evenCircleSubmodule S)
      (solve_isClosed_evenCircle hS) y.2 n
  exact (congrArg (fun z =>
      gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n z)
      (solveResidualEquiv_apply hS y)).trans
    ((gradedSeminorm_prodEquiv
      (fun k => subLevel S.Q.toLinearMap.ker k) (subBond S.Q.toLinearMap.ker)
      (fun k => subLevel (evenCircleSubmodule S) k) (subBond (evenCircleSubmodule S)) n
      (subspaceEquiv S.Q.toLinearMap.ker S.Q.isClosed_ker y.1)
      (subspaceEquiv (evenCircleSubmodule S) (solve_isClosed_evenCircle hS) y.2)).trans
      (congrArg₂ max hsource hcircle))

private theorem solve_residualGrading_apply (n : ℕ) (y : ResidualSpace S) :
    residualGrading S n y = S.sourceGrading n y.1 +
      ((S.circle (3 / 4 : ℝ)).grading n) y.2.val := by
  simp only [residualGrading, pairGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Submodule.subtype_apply]

theorem solveResidualEquiv_grading_le (hS : IsPhysicalSpaces D T S)
    (n : ℕ) (y : ResidualSpace S) :
    gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n
      (solveResidualEquiv hS y) ≤ residualGrading S n y := by
  calc
    _ = max (S.sourceGrading n y.1)
        (((S.circle (3 / 4 : ℝ)).grading n) y.2.val) :=
      solveResidualEquiv_grading hS n y
    _ ≤ S.sourceGrading n y.1 + ((S.circle (3 / 4 : ℝ)).grading n) y.2.val :=
      max_le
        (le_add_of_nonneg_right
          (apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) y.2.val))
        (le_add_of_nonneg_left (apply_nonneg (S.sourceGrading n) y.1))
    _ = residualGrading S n y := (solve_residualGrading_apply n y).symm

theorem solve_residualGrading_le_two (hS : IsPhysicalSpaces D T S)
    (n : ℕ) (y : ResidualSpace S) :
    residualGrading S n y ≤
      2 * gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n
        (solveResidualEquiv hS y) := by
  calc
    residualGrading S n y =
        S.sourceGrading n y.1 + ((S.circle (3 / 4 : ℝ)).grading n) y.2.val :=
      solve_residualGrading_apply n y
    _ ≤ max (S.sourceGrading n y.1) (((S.circle (3 / 4 : ℝ)).grading n) y.2.val) +
        max (S.sourceGrading n y.1) (((S.circle (3 / 4 : ℝ)).grading n) y.2.val) :=
      add_le_add (le_max_left _ _) (le_max_right _ _)
    _ = 2 * max (S.sourceGrading n y.1)
        (((S.circle (3 / 4 : ℝ)).grading n) y.2.val) := (two_mul _).symm
    _ = 2 * gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n
        (solveResidualEquiv hS y) :=
      congrArg (fun t : ℝ => 2 * t) (solveResidualEquiv_grading hS n y).symm

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
  obtain ⟨even, odd, heven, _, _, ⟨r, b, hPt⟩, _⟩ :=
    solve_parityProjection_data hS (3 / 4 : ℝ)
  have hinj : Function.Injective (S.circle (3 / 4 : ℝ)).decode :=
    (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  have hmem (u : CircleSpace S) : even u ∈ evenCircleSubmodule S := by
    intro m θ
    calc
      (S.circle (3 / 4 : ℝ)).decode (even u) m (-θ) =
          ((S.circle (3 / 4 : ℝ)).decode u m (-θ) +
            (S.circle (3 / 4 : ℝ)).decode u m θ) / 2 := by
        simpa only [neg_neg] using heven u m (-θ)
      _ = ((S.circle (3 / 4 : ℝ)).decode u m θ +
          (S.circle (3 / 4 : ℝ)).decode u m (-θ)) / 2 :=
        congrArg (fun t : ℝ => t / 2) (add_comm _ _)
      _ = (S.circle (3 / 4 : ℝ)).decode (even u) m θ := (heven u m θ).symm
  have hfix (u : CircleSpace S) (hu : u ∈ evenCircleSubmodule S) : even u = u := by
    have hd : (S.circle (3 / 4 : ℝ)).decode (even u) =
        (S.circle (3 / 4 : ℝ)).decode u := by
      funext m θ
      calc
        (S.circle (3 / 4 : ℝ)).decode (even u) m θ =
            ((S.circle (3 / 4 : ℝ)).decode u m θ +
              (S.circle (3 / 4 : ℝ)).decode u m (-θ)) / 2 := heven u m θ
        _ = ((S.circle (3 / 4 : ℝ)).decode u m θ +
            (S.circle (3 / 4 : ℝ)).decode u m θ) / 2 :=
          congrArg (fun t : ℝ => ((S.circle (3 / 4 : ℝ)).decode u m θ + t) / 2)
            (hu m θ)
        _ = (S.circle (3 / 4 : ℝ)).decode u m θ := by ring
    exact hinj hd
  have hmono : Monotone (S.circle (3 / 4 : ℝ)).grading :=
    gradedSeminorm_monotone (fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond
  exact hasSmoothing_submodule_of_tame_projection
    (p := (S.circle (3 / 4 : ℝ)).grading) hmono
    (evenCircleSubmodule S) even hmem hfix hPt
    ((hS.2.2.2.2.1 (3 / 4 : ℝ)).2.1)

theorem solve_residual_hasSmoothing (hS : IsPhysicalSpaces D T S) :
    HasSmoothing (residualGrading S) :=
  hasSmoothing_pairGrading (solve_source_hasSmoothing hS) (solve_even_hasSmoothing hS)

end ContinuousFlexibility.Analysis
