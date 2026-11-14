module

public import ContinuousFlexibility.Analysis.SpacesCircleBandAnalysis

/-!
# The concrete circle tame retraction

The analysis map takes the actual joint material-weight/Fourier bands and
places their angular `L²` families in the prescribed physical Banach space.
The synthesis map takes all actual weighted derivatives of each band. The
complete band sum reconstructs every coordinate of the given closed-graph
projective limit. Analysis has loss zero and synthesis has loss one.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff

variable (T : MaterialData) (hM0 : ∀ m, 0 < T.M (T.sample m))
  (hM : ∀ m, 1 ≤ T.M (T.sample m))

/-- A circle analysis shell in the fixed Banach space from the statement. -/
def circleModelShellAnalysis (k : ℕ) :
    CircleJetProjectiveLimit T hM0 →L[ℝ] PhysicalModelBanach :=
  circleFamilyCylinderEmbedding.toContinuousLinearMap.comp (circleBandAnalysis T hM0 hM k)

theorem circleModelShellAnalysis_apply (k : ℕ) (u : CircleJetProjectiveLimit T hM0) :
    circleModelShellAnalysis T hM0 hM k u =
      circleFamilyCylinderEmbedding (circleBandAnalysis T hM0 hM k u) := rfl

theorem circleModelShellAnalysis_bound (s k : ℕ) (u : CircleJetProjectiveLimit T hM0) :
    ‖Real.exp ((s : ℝ) * (k : ℝ)) • circleModelShellAnalysis T hM0 hM k u‖ ≤
      2 * Analysis.gradedSeminorm (fun n => circleJetClosedSubmodule T n)
        (circleJetBond T hM0) s u := by
  rw [circleModelShellAnalysis_apply]
  calc
    ‖Real.exp ((s : ℝ) * (k : ℝ)) •
        circleFamilyCylinderEmbedding (circleBandAnalysis T hM0 hM k u)‖ =
        ‖circleFamilyCylinderEmbedding
          (Real.exp ((s : ℝ) * (k : ℝ)) • circleBandAnalysis T hM0 hM k u)‖ :=
      congrArg norm (circleFamilyCylinderEmbedding.map_smul
        (Real.exp ((s : ℝ) * (k : ℝ))) (circleBandAnalysis T hM0 hM k u)).symm
    _ = ‖Real.exp ((s : ℝ) * (k : ℝ)) • circleBandAnalysis T hM0 hM k u‖ :=
      circleFamilyCylinderEmbedding.norm_map _
    _ ≤ _ := circleBandAnalysis_bound T hM0 hM s k u

/-- A synthesis shell from the fixed model into an actual closed circle level. -/
def circleModelShellSynthesis (s k : ℕ) :
    PhysicalModelBanach →L[ℝ] circleJetClosedSubmodule T s :=
  (circleBandSynthesisLevel T hM hM0 s k).comp circleFamilyCylinderProjection

theorem circleModelShellSynthesis_apply (s k : ℕ) (v : PhysicalModelBanach) :
    circleModelShellSynthesis T hM0 hM s k v =
      circleBandSynthesisLevel T hM hM0 s k (circleFamilyCylinderProjection v) := rfl

theorem circleModelShellSynthesis_bound (s k : ℕ) (v : PhysicalModelBanach) :
    ‖circleModelShellSynthesis T hM0 hM s k v‖ ≤
      (circleBandSynthesisConstant s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) * ‖v‖ := by
  rw [circleModelShellSynthesis_apply]
  exact (circleBandSynthesisLevel_norm_le T hM hM0 s k _).trans
    (mul_le_mul_of_nonneg_left (circleFamilyCylinderProjection_norm_le v) (by positivity))

theorem circleModelShellSynthesis_compatible (s k : ℕ) (v : PhysicalModelBanach) :
    circleJetBond T hM0 s (circleModelShellSynthesis T hM0 hM (s + 1) k v) =
      circleModelShellSynthesis T hM0 hM s k v :=
  circleBandSynthesisLevel_compatible T hM hM0 s k (circleFamilyCylinderProjection v)

theorem circleModelShellSynthesis_analysis_coordinate (s k m : ℕ)
    (u : CircleJetProjectiveLimit T hM0) (j : CircleJetIndex s) :
    (circleModelShellSynthesis T hM0 hM s k (circleModelShellAnalysis T hM0 hM k u)).val m j =
      circleJetWeight T m j •
        circleBandJet (T.M (T.sample m)) (hM m) k (j.val 0).val
          (circleJetAngularDerivative u m 0) := by
  rw [circleModelShellSynthesis_apply, circleModelShellAnalysis_apply,
    circleFamilyCylinderProjection_embedding, circleBandSynthesisLevel_apply,
    circleBandAnalysis_apply, circleBandJet_comp_zero]

/-- Exponential source estimates make the genuine synthesis series converge
in every prescribed closed Banach level. -/
theorem circleModelShellSynthesis_summable (u : CircleJetProjectiveLimit T hM0) (s : ℕ) :
    Summable (fun k : ℕ =>
      circleModelShellSynthesis T hM0 hM s k (circleModelShellAnalysis T hM0 hM k u)) := by
  let E : ℕ → Type := fun n => circleJetClosedSubmodule T n
  let bond := circleJetBond T hM0
  let A := fun k => (circleModelShellAnalysis T hM0 hM k).toLinearMap
  let C : ℕ → ℝ≥0 := fun _ => 2
  have hA : ∀ (n k : ℕ) (x : Analysis.ProjectiveLimit E bond),
      ‖Real.exp ((n : ℝ) * k) • A k x‖ ≤ C n * Analysis.gradedSeminorm E bond (n + 0) x := by
    intro n k x
    exact circleModelShellAnalysis_bound T hM0 hM n k x
  let v := Analysis.shellAnalysisMap (Analysis.gradedSeminorm E bond) 0 A C hA
    (Analysis.withSeminorms_graded E bond) u
  have hP : ∀ n k b, ‖circleModelShellSynthesis T hM0 hM n k b‖ ≤
      (circleBandSynthesisConstant n : ℝ) * Real.exp (((n + 0 : ℕ) : ℝ) * k) * ‖b‖ := by
    intro n k b
    simpa only [Nat.add_zero] using circleModelShellSynthesis_bound T hM0 hM n k b
  have hs := Analysis.summable_shellSynthesis E 0 (circleModelShellSynthesis T hM0 hM)
    circleBandSynthesisConstant hP v s
  simp only [v, Analysis.shellAnalysisMap_raw, A] at hs
  exact hs

/-- Every weighted jet coordinate is reconstructed by the countable band
sum, in the norm topology of the actual closed level. -/
theorem circleModelShellSynthesis_coordinate_hasSum
    (u : CircleJetProjectiveLimit T hM0) (s m : ℕ) (j : CircleJetIndex s) :
    HasSum (fun k : ℕ =>
      (circleModelShellSynthesis T hM0 hM s k
        (circleModelShellAnalysis T hM0 hM k u)).val m j)
      (circleJetWeight T m j • circleJetAngularDerivative u m (j.val 0).val) := by
  obtain ⟨hg, hp, hj⟩ := circleJetRawSmooth_spec u m
  have h₀ : (circleJetAngularDerivative u m 0 : ℝ → ℝ) =ᵐ[angleMeasure]
      circleJetRawSmooth u m := by simpa only [iteratedDeriv_zero] using hj 0
  have hactual := (circleBandJet_hasSum_derivative (T.M (T.sample m)) (hM m)
    hg hp h₀ (j.val 0).val (hj (j.val 0).val)).const_smul (circleJetWeight T m j)
  exact hactual.congr_fun fun k =>
    circleModelShellSynthesis_analysis_coordinate T hM0 hM s k m u j

/-- The norm-convergent shell series is exactly the prescribed level. -/
theorem circleModelShellSynthesis_hasSum (u : CircleJetProjectiveLimit T hM0) (s : ℕ) :
    HasSum (fun k : ℕ =>
      circleModelShellSynthesis T hM0 hM s k (circleModelShellAnalysis T hM0 hM k u))
        (u.val s) := by
  have hs := circleModelShellSynthesis_summable T hM0 hM u s
  have he : (∑' k : ℕ,
      circleModelShellSynthesis T hM0 hM s k (circleModelShellAnalysis T hM0 hM k u)) =
        u.val s := by
    apply Subtype.ext
    apply lp.ext
    funext m
    apply (WithLp.ext_iff 2).mpr
    funext j
    let Q : circleJetClosedSubmodule T s →L[ℝ] AngleL2 :=
      (circleJetCoordinate s m j).comp (circleJetClosedSubmodule T s).subtypeL
    have hsum := Q.hasSum hs.hasSum
    exact (hsum.unique (circleModelShellSynthesis_coordinate_hasSum T hM0 hM u s m j)).trans
      (circleJet_level_eq_weighted_angular T hM0 u s m j).symm
  rw [← he]
  exact hs.hasSum

include hM in
/-- The canonical circle model is an actual tame retract of the fixed
exponential sequence model. The construction uses no additional analytic
hypotheses beyond the prescribed lower bound on the sampled weight. -/
theorem canonicalCircleModel_tameRetraction (γ : ℝ) :
    TameRetraction (canonicalCircleModelData T hM0 γ).grading modelGrading := by
  change TameRetraction
    (Analysis.gradedSeminorm (fun n => circleJetClosedSubmodule T n) (circleJetBond T hM0))
    (Analysis.exponentialSequenceSeminorm PhysicalModelBanach)
  apply Analysis.tameRetraction_of_shells
    (fun n => circleJetClosedSubmodule T n) (circleJetBond T hM0) 0 0
    (fun k => (circleModelShellAnalysis T hM0 hM k).toLinearMap) (fun _ => 2)
    (fun s k u => circleModelShellAnalysis_bound T hM0 hM s k u)
    (circleModelShellSynthesis T hM0 hM) circleBandSynthesisConstant
  · intro s k v
    simpa only [Nat.add_zero] using circleModelShellSynthesis_bound T hM0 hM s k v
  · exact circleModelShellSynthesis_compatible T hM0 hM
  · exact circleModelShellSynthesis_hasSum T hM0 hM

end ContinuousFlexibility.Statements
