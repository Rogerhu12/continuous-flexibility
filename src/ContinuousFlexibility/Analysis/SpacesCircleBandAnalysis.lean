import ContinuousFlexibility.Analysis.SpacesCircleBandSynthesis

/-!
# Circle analysis with a fixed loss of zero

The analysis coefficients are the actual bands of the order-zero angular
jets. The two pure order-`s` coordinates control their exponential weight:
one is the material weight and the other is the angular derivative.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff

/-- The pure material-weight coordinate in an order-`s` row. -/
def circleJetPureWeightIndex (s : ℕ) : CircleJetIndex s :=
  ⟨fun i => if i = 0 then 0 else ⟨s, Nat.lt_succ_self s⟩, by simp⟩

@[simp] theorem circleJetPureWeightIndex_order (s : ℕ) :
    ((circleJetPureWeightIndex s).val 0).val = 0 := by
  simp [circleJetPureWeightIndex]

@[simp] theorem circleJetPureWeightIndex_weight (s : ℕ) :
    ((circleJetPureWeightIndex s).val 1).val = s := by
  simp [circleJetPureWeightIndex]

variable (T : MaterialData) (hM0 : ∀ m, 0 < T.M (T.sample m))

/-- Each closed-graph coordinate is the stated weighted angular derivative,
as an equality of actual `L²` classes. -/
theorem circleJet_level_eq_weighted_angular (u : CircleJetProjectiveLimit T hM0)
    (s m : ℕ) (j : CircleJetIndex s) :
    (u.val s).val m j =
      circleJetWeight T m j • circleJetAngularDerivative u m (j.val 0).val := by
  have hW : circleJetWeight T m j ≠ 0 := pow_ne_zero _ (hM0 m).ne'
  have h := congrArg (fun v : AngleL2 => circleJetWeight T m j • v)
    (circleJetNormalizedDerivative_eq_angular u s m j)
  rw [circleJetNormalizedDerivative_apply, smul_smul, mul_inv_cancel₀ hW, one_smul] at h
  exact h

theorem circleJet_weighted_base_norm_le (u : CircleJetProjectiveLimit T hM0) (s m : ℕ) :
    ‖T.M (T.sample m) ^ s • circleJetAngularDerivative u m 0‖ ≤ ‖(u.val s).val m‖ := by
  have he := circleJet_level_eq_weighted_angular T hM0 u s m (circleJetPureWeightIndex s)
  simp only [circleJetWeight, circleJetPureWeightIndex_order,
    circleJetPureWeightIndex_weight] at he
  rw [← he]
  exact PiLp.norm_apply_le _ _

/-- The continuous family of the actual order-zero angular classes. -/
def circleJetBaseFamily : CircleJetProjectiveLimit T hM0 →L[ℝ] CircleModelBanach :=
  (Analysis.lpSpectralDiagonal
    (fun _ : ℕ => PiLp.proj (𝕜 := ℝ) 2 (fun _ : CircleJetIndex 0 => AngleL2)
      (circleJetPureAngularIndex 0))
    (C := 1) (by norm_num)
    (fun _ z => by
      simpa only [PiLp.proj_apply, one_mul] using
        PiLp.norm_apply_le z (circleJetPureAngularIndex 0))).comp
      ((circleJetClosedSubmodule T 0).subtypeL.comp
        (Analysis.projectiveCoordinate (fun s => circleJetClosedSubmodule T s)
          (circleJetBond T hM0) 0))

theorem circleJetBaseFamily_apply (u : CircleJetProjectiveLimit T hM0) (m : ℕ) :
    circleJetBaseFamily T hM0 u m = circleJetAngularDerivative u m 0 := rfl

variable (hM : ∀ m, 1 ≤ T.M (T.sample m))

/-- The actual angular spectral band, taken in every material row. -/
def circleBandFamily (k : ℕ) : CircleModelBanach →L[ℝ] CircleModelBanach :=
  Analysis.lpSpectralDiagonal (fun m => circleBandJet (T.M (T.sample m)) (hM m) k 0)
    (C := 1) (by norm_num)
    (fun m f => by simpa only [one_mul] using
      circleBandJet_zero_norm_le (T.M (T.sample m)) (hM m) k f)

theorem circleBandFamily_apply (k m : ℕ) (f : CircleModelBanach) :
    circleBandFamily T hM k f m =
      circleBandJet (T.M (T.sample m)) (hM m) k 0 (f m) := rfl

/-- Circle analysis coefficients in the natural family Banach space. -/
def circleBandAnalysis (k : ℕ) : CircleJetProjectiveLimit T hM0 →L[ℝ] CircleModelBanach :=
  (circleBandFamily T hM k).comp (circleJetBaseFamily T hM0)

theorem circleBandAnalysis_apply (k m : ℕ) (u : CircleJetProjectiveLimit T hM0) :
    circleBandAnalysis T hM0 hM k u m =
      circleBandJet (T.M (T.sample m)) (hM m) k 0 (circleJetAngularDerivative u m 0) := rfl

theorem circleBandAnalysis_row_bound (s k m : ℕ) (u : CircleJetProjectiveLimit T hM0) :
    ‖Real.exp ((s : ℝ) * (k : ℝ)) • circleBandAnalysis T hM0 hM k u m‖ ≤
      2 * ‖(u.val s).val m‖ := by
  obtain ⟨hg, hp, hj⟩ := circleJetRawSmooth_spec u m
  have h₀ : (circleJetAngularDerivative u m 0 : ℝ → ℝ) =ᵐ[angleMeasure]
      circleJetRawSmooth u m := by simpa only [iteratedDeriv_zero] using hj 0
  rw [circleBandAnalysis_apply]
  calc
    ‖Real.exp ((s : ℝ) * (k : ℝ)) •
        circleBandJet (T.M (T.sample m)) (hM m) k 0 (circleJetAngularDerivative u m 0)‖ ≤
        ‖T.M (T.sample m) ^ s • circleJetAngularDerivative u m 0‖ +
          ‖circleJetAngularDerivative u m s‖ :=
      circleBandJet_analysis_bound_of_smooth (T.M (T.sample m)) (hM m) k s hg hp h₀ (hj s)
    _ ≤ ‖(u.val s).val m‖ + ‖(u.val s).val m‖ :=
      add_le_add (circleJet_weighted_base_norm_le T hM0 u s m)
        (PiLp.norm_apply_le ((u.val s).val m) (circleJetPureAngularIndex s))
    _ = _ := by ring

/-- The complete family estimate has no derivative loss. -/
theorem circleBandAnalysis_bound (s k : ℕ) (u : CircleJetProjectiveLimit T hM0) :
    ‖Real.exp ((s : ℝ) * (k : ℝ)) • circleBandAnalysis T hM0 hM k u‖ ≤
      2 * Analysis.gradedSeminorm (fun n => circleJetClosedSubmodule T n)
        (circleJetBond T hM0) s u := by
  have hn : ‖Real.exp ((s : ℝ) * (k : ℝ)) • circleBandAnalysis T hM0 hM k u‖ ≤
      ‖(2 : ℝ) • (u.val s).val‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro m
    change ‖Real.exp ((s : ℝ) * (k : ℝ)) • circleBandAnalysis T hM0 hM k u m‖ ≤
      ‖(2 : ℝ) • (u.val s).val m‖
    calc
      ‖Real.exp ((s : ℝ) * (k : ℝ)) • circleBandAnalysis T hM0 hM k u m‖ ≤
          2 * ‖(u.val s).val m‖ := circleBandAnalysis_row_bound T hM0 hM s k m u
      _ = ‖(2 : ℝ) • (u.val s).val m‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    ‖Real.exp ((s : ℝ) * (k : ℝ)) • circleBandAnalysis T hM0 hM k u‖ ≤
        ‖(2 : ℝ) • (u.val s).val‖ := hn
    _ = 2 * ‖u.val s‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Analysis.norm_coordinate_le_graded (fun n => circleJetClosedSubmodule T n)
        (circleJetBond T hM0) le_rfl u) (by norm_num)

end ContinuousFlexibility.Statements
