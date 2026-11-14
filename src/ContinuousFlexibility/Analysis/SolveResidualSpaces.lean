module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.ProjectiveLimitSubspace
public import ContinuousFlexibility.Analysis.SolveSmoothing
public import ContinuousFlexibility.Analysis.SolveCircleProjection

/-!
# The actual residual space as a complete projective limit

The scalar component is the kernel of the compatibility functional and the
circle component is the even sector. Both are closed subspaces of the
physical projective limits. Their product has an exact projective realization;
the statement's sum grading and the resulting maximum grading differ by at
most a factor of two.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

section SubspaceProduct

universe u

variable {E F : ℕ → Type u}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  {e : ∀ n, E (n + 1) →L[ℝ] E n} {f : ∀ n, F (n + 1) →L[ℝ] F n}
  (W : Submodule ℝ (ProjectiveLimit E e)) (V : Submodule ℝ (ProjectiveLimit F f))
  (hW : IsClosed (W : Set (ProjectiveLimit E e)))
  (hV : IsClosed (V : Set (ProjectiveLimit F f)))

/-- Cache the product-level structures before any concrete graph is substituted. -/
private def SolveSubspaceProductLevel (n : ℕ) : Type u :=
  subLevel W n × subLevel V n

private instance solveSubspaceProductNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (SolveSubspaceProductLevel W V n) :=
  inferInstanceAs (NormedAddCommGroup (subLevel W n × subLevel V n))

private instance solveSubspaceProductNormedSpace (n : ℕ) :
    NormedSpace ℝ (SolveSubspaceProductLevel W V n) :=
  inferInstanceAs (NormedSpace ℝ (subLevel W n × subLevel V n))

private def solveSubspaceProductBond (n : ℕ) :
    SolveSubspaceProductLevel W V (n + 1) →L[ℝ] SolveSubspaceProductLevel W V n :=
  (subBond W n).prodMap (subBond V n)

/-- Assemble the product representation while its Banach levels remain abstract. -/
private def solveSubspaceProductEquiv : (W × V) ≃L[ℝ]
    ProjectiveLimit (SolveSubspaceProductLevel W V) (solveSubspaceProductBond W V) :=
  ((subspaceEquiv (E := E) (e := e) W hW).prodCongr
    (subspaceEquiv (E := F) (e := f) V hV)).trans
    (prodEquiv (fun n => subLevel W n) (subBond W)
      (fun n => subLevel V n) (subBond V))

private theorem solveSubspaceProductEquiv_apply (z : W × V) :
    solveSubspaceProductEquiv (E := E) (F := F) (e := e) (f := f) W V hW hV z =
      prodEquiv (fun n => subLevel W n) (subBond W)
        (fun n => subLevel V n) (subBond V)
        (subspaceEquiv (E := E) (e := e) W hW z.1,
          subspaceEquiv (E := F) (e := f) V hV z.2) := by
  dsimp +instances +unfoldPartialApp only [solveSubspaceProductEquiv, SolveSubspaceProductLevel,
    solveSubspaceProductBond, solveSubspaceProductNormedAddCommGroup,
    solveSubspaceProductNormedSpace]
  exact (ContinuousLinearEquiv.trans_apply
    ((subspaceEquiv (E := E) (e := e) W hW).prodCongr
      (subspaceEquiv (E := F) (e := f) V hV))
    (prodEquiv (fun k => subLevel W k) (subBond W)
      (fun k => subLevel V k) (subBond V)) z).trans
    (congrArg (prodEquiv (fun k => subLevel W k) (subBond W)
      (fun k => subLevel V k) (subBond V))
      (ContinuousLinearEquiv.prodCongr_apply
        (subspaceEquiv (E := E) (e := e) W hW)
        (subspaceEquiv (E := F) (e := f) V hV) z))

private theorem solveSubspaceProductEquiv_grading (n : ℕ) (z : W × V) :
    gradedSeminorm (SolveSubspaceProductLevel W V) (solveSubspaceProductBond W V) n
        (solveSubspaceProductEquiv (E := E) (F := F) (e := e) (f := f) W V hW hV z) =
      max (gradedSeminorm E e n z.1.val) (gradedSeminorm F f n z.2.val) := by
  dsimp +instances +unfoldPartialApp only [solveSubspaceProductEquiv, SolveSubspaceProductLevel,
    solveSubspaceProductBond, solveSubspaceProductNormedAddCommGroup,
    solveSubspaceProductNormedSpace]
  have hsource := gradedSeminorm_subspaceEquiv (E := E) (e := e) W hW z.1 n
  have hcircle := gradedSeminorm_subspaceEquiv (E := F) (e := f) V hV z.2 n
  have hprod := gradedSeminorm_prodEquiv
    (fun k => subLevel W k) (subBond W) (fun k => subLevel V k) (subBond V) n
    (subspaceEquiv (E := E) (e := e) W hW z.1)
    (subspaceEquiv (E := F) (e := f) V hV z.2)
  exact (congrArg (fun v => gradedSeminorm
      (SolveSubspaceProductLevel W V) (solveSubspaceProductBond W V) n v)
      (solveSubspaceProductEquiv_apply (E := E) (F := F) (e := e) (f := f)
        W V hW hV z)).trans
    (hprod.trans (congrArg₂ max hsource hcircle))

attribute [irreducible] solveSubspaceProductEquiv

end SubspaceProduct

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
  SolveSubspaceProductLevel
    (E := fun k => (S.height (3 / 4 : ℝ)).level k)
    (F := fun k => (S.circle (3 / 4 : ℝ)).level k)
    (e := (S.height (3 / 4 : ℝ)).bond) (f := (S.circle (3 / 4 : ℝ)).bond)
    S.Q.toLinearMap.ker (evenCircleSubmodule S) n

instance solveResidualLevelNormedAddCommGroup (S : PhysicalSpacesData) (n : ℕ) :
    NormedAddCommGroup (SolveResidualLevel S n) :=
  solveSubspaceProductNormedAddCommGroup
    (E := fun k => (S.height (3 / 4 : ℝ)).level k)
    (F := fun k => (S.circle (3 / 4 : ℝ)).level k)
    (e := (S.height (3 / 4 : ℝ)).bond) (f := (S.circle (3 / 4 : ℝ)).bond)
    S.Q.toLinearMap.ker (evenCircleSubmodule S) n

instance solveResidualLevelNormedSpace (S : PhysicalSpacesData) (n : ℕ) :
    NormedSpace ℝ (SolveResidualLevel S n) :=
  solveSubspaceProductNormedSpace
    (E := fun k => (S.height (3 / 4 : ℝ)).level k)
    (F := fun k => (S.circle (3 / 4 : ℝ)).level k)
    (e := (S.height (3 / 4 : ℝ)).bond) (f := (S.circle (3 / 4 : ℝ)).bond)
    S.Q.toLinearMap.ker (evenCircleSubmodule S) n

abbrev solveResidualBond (S : PhysicalSpacesData) (n : ℕ) :
    SolveResidualLevel S (n + 1) →L[ℝ] SolveResidualLevel S n :=
  solveSubspaceProductBond
    (E := fun k => (S.height (3 / 4 : ℝ)).level k)
    (F := fun k => (S.circle (3 / 4 : ℝ)).level k)
    (e := (S.height (3 / 4 : ℝ)).bond) (f := (S.circle (3 / 4 : ℝ)).bond)
    S.Q.toLinearMap.ker (evenCircleSubmodule S) n

/-- The residual product is represented by the same actual weak graph
levels, followed by their closed scalar and parity subspaces. -/
def solveResidualEquiv (hS : IsPhysicalSpaces D T S) :
    ResidualSpace S ≃L[ℝ] ProjectiveLimit (SolveResidualLevel S) (solveResidualBond S) :=
  solveSubspaceProductEquiv
    (E := fun n => (S.height (3 / 4 : ℝ)).level n)
    (F := fun n => (S.circle (3 / 4 : ℝ)).level n)
    (e := (S.height (3 / 4 : ℝ)).bond) (f := (S.circle (3 / 4 : ℝ)).bond)
    S.Q.toLinearMap.ker (evenCircleSubmodule S) S.Q.isClosed_ker
    (solve_isClosed_evenCircle (D := D) (T := T) (S := S) hS)

theorem solveResidualEquiv_grading (hS : IsPhysicalSpaces D T S)
    (n : ℕ) (y : ResidualSpace S) :
    gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n
        (solveResidualEquiv (D := D) (T := T) (S := S) hS y) =
      max (S.sourceGrading n y.1)
        (((S.circle (3 / 4 : ℝ)).grading n) y.2.val) := by
  have h := solveSubspaceProductEquiv_grading
    (E := fun k => (S.height (3 / 4 : ℝ)).level k)
    (F := fun k => (S.circle (3 / 4 : ℝ)).level k)
    (e := (S.height (3 / 4 : ℝ)).bond) (f := (S.circle (3 / 4 : ℝ)).bond)
    S.Q.toLinearMap.ker (evenCircleSubmodule S) S.Q.isClosed_ker
    (solve_isClosed_evenCircle (D := D) (T := T) (S := S) hS) n y
  dsimp +instances +unfoldPartialApp only [solveResidualEquiv, SolveResidualLevel, solveResidualBond,
    solveResidualLevelNormedAddCommGroup, solveResidualLevelNormedSpace,
    PhysicalSpacesData.sourceGrading, SobolevModelData.grading, CircleModelData.grading]
  simpa only [Seminorm.comp_apply, Submodule.subtype_apply] using h

-- Later comparisons only need the specialized grading theorem.
attribute [irreducible] solveResidualEquiv

private theorem solve_residualGrading_apply (n : ℕ) (y : ResidualSpace S) :
    residualGrading S n y = S.sourceGrading n y.1 +
      ((S.circle (3 / 4 : ℝ)).grading n) y.2.val := by
  simp only [residualGrading, pairGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Submodule.subtype_apply]

theorem solveResidualEquiv_grading_le (hS : IsPhysicalSpaces D T S)
    (n : ℕ) (y : ResidualSpace S) :
    gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n
      (solveResidualEquiv (D := D) (T := T) (S := S) hS y) ≤ residualGrading S n y := by
  calc
    _ = max (S.sourceGrading n y.1)
        (((S.circle (3 / 4 : ℝ)).grading n) y.2.val) :=
      solveResidualEquiv_grading (D := D) (T := T) (S := S) hS n y
    _ ≤ S.sourceGrading n y.1 + ((S.circle (3 / 4 : ℝ)).grading n) y.2.val :=
      max_le
        (le_add_of_nonneg_right
          (apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) y.2.val))
        (le_add_of_nonneg_left (apply_nonneg (S.sourceGrading n) y.1))
    _ = residualGrading S n y := (solve_residualGrading_apply (S := S) n y).symm

theorem solve_residualGrading_le_two (hS : IsPhysicalSpaces D T S)
    (n : ℕ) (y : ResidualSpace S) :
    residualGrading S n y ≤
      2 * gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n
        (solveResidualEquiv (D := D) (T := T) (S := S) hS y) := by
  calc
    residualGrading S n y =
        S.sourceGrading n y.1 + ((S.circle (3 / 4 : ℝ)).grading n) y.2.val :=
      solve_residualGrading_apply (S := S) n y
    _ ≤ max (S.sourceGrading n y.1) (((S.circle (3 / 4 : ℝ)).grading n) y.2.val) +
        max (S.sourceGrading n y.1) (((S.circle (3 / 4 : ℝ)).grading n) y.2.val) :=
      add_le_add (le_max_left _ _) (le_max_right _ _)
    _ = 2 * max (S.sourceGrading n y.1)
        (((S.circle (3 / 4 : ℝ)).grading n) y.2.val) := (two_mul _).symm
    _ = 2 * gradedSeminorm (SolveResidualLevel S) (solveResidualBond S) n
        (solveResidualEquiv (D := D) (T := T) (S := S) hS y) :=
      congrArg (fun t : ℝ => 2 * t)
        (solveResidualEquiv_grading (D := D) (T := T) (S := S) hS n y).symm

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
  have hparity :=
    solve_parityProjection_data (D := D) (T := T) (S := S) hS (3 / 4 : ℝ)
  rcases hparity with ⟨even, odd, heven, _, _, ⟨r, b, hPt⟩, _⟩
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
  hasSmoothing_pairGrading
    (solve_source_hasSmoothing (D := D) (T := T) (S := S) hS)
    (solve_even_hasSmoothing (D := D) (T := T) (S := S) hS)

end ContinuousFlexibility.Analysis
