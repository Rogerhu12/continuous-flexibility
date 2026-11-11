import ContinuousFlexibility.Analysis.NeighborhoodCircleCharts
import ContinuousFlexibility.Analysis.NeighborhoodStateBounds
import ContinuousFlexibility.Analysis.SpacesTraceCircleBounds
import ContinuousFlexibility.Analysis.StateKappaBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Uniform control of the actual left circle charts

The weighted circle evaluation estimate and the material envelope bound
give a single order-two grading bound for the angular derivative. Since
the reference chart coordinate is zero, one neighborhood controls every
left chart at once. Periodicity comes from the actual circle model and
oddness comes from the stated sector condition.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff ENNReal

/-- First derivatives of every decoded circle have one uniform order-two
bound, with no dependence on the circle index or evaluation point. -/
theorem circleModel_deriv_le_grading
    {D : ReferenceData} {T : MaterialData} {M : CircleModelData} {γ : ℝ}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    (hγ : 0 < γ) (hM : IsCircleModel T γ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : M.Space, ∀ m θ,
      |deriv (M.decode u m) θ| ≤ K * M.grading 2 u := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hPower, _⟩ := hT
  obtain ⟨H, hH, hHbound, _, _⟩ := hPower 0 γ hγ
  refine ⟨anglePairEvaluationConstant * H,
    mul_nonneg anglePairEvaluationConstant_nonneg hH.le, ?_⟩
  intro u m θ
  have hu : CircleMember T γ (M.decode u) := hM.2.2.2.1 u
  have hpos : 0 < T.H (T.sample m) := (hT.2.1 _ (hsample m)).2.1
  have hweight : T.H (T.sample m) ^ γ ≤ H := by
    simpa only [Real.rpow_zero, mul_one] using hHbound _ (hsample m)
  have hrow : ‖circleJetEncodeHilbert hu 2 m‖ ≤ M.grading 2 u := by
    calc
      ‖circleJetEncodeHilbert hu 2 m‖ ≤ ‖circleJetEncodeHilbert hu 2‖ :=
        lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ m
      _ = circleNorm T γ 2 (M.decode u) := circleJetEncodeHilbert_norm hu 2
      _ = ‖u.val 2‖ := (hM.2.2.2.2.2.2.2 u 2).symm
      _ ≤ M.grading 2 u := Analysis.norm_coordinate_le_graded _ _ le_rfl u
  have hw := spaces_circle_weighted_pointwise hu 2 m 1 0 (by norm_num) θ
  simp only [pow_zero, one_mul, iteratedDeriv_one, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hpos (-γ))] at hw
  rw [Real.rpow_neg hpos.le, ← div_eq_inv_mul] at hw
  have hd := (div_le_iff₀ (Real.rpow_pos_of_pos hpos γ)).mp hw
  calc
    |deriv (M.decode u m) θ| ≤
        (anglePairEvaluationConstant * ‖circleJetEncodeHilbert hu 2 m‖) *
          T.H (T.sample m) ^ γ := hd
    _ ≤ (anglePairEvaluationConstant * M.grading 2 u) * T.H (T.sample m) ^ γ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrow anglePairEvaluationConstant_nonneg)
        (Real.rpow_nonneg hpos.le γ)
    _ ≤ (anglePairEvaluationConstant * M.grading 2 u) * H :=
      mul_le_mul_of_nonneg_left hweight
        (mul_nonneg anglePairEvaluationConstant_nonneg (apply_nonneg _ _))
    _ = (anglePairEvaluationConstant * H) * M.grading 2 u := by ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem contDiff_stateLeftChart (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) : ContDiff ℝ ∞ (stateLeftChart S x m) := by
  have h := ((((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 x.2.2.2).1 m).1)
  exact contDiff_id.add h

theorem deriv_stateLeftChart (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) (θ : ℝ) :
    deriv (stateLeftChart S x m) θ =
      1 + deriv ((S.circle (3 / 4 : ℝ)).decode x.2.2.2 m) θ := by
  have h := ((((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 x.2.2.2).1 m).1)
  exact ((hasDerivAt_id θ).add (h.differentiable (by simp) θ).hasDerivAt).deriv

theorem stateLeftChart_lift (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) (θ : ℝ) :
    stateLeftChart S x m (θ + Real.pi) = stateLeftChart S x m θ + Real.pi := by
  have h := ((((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 x.2.2.2).1 m).2 θ)
  simp only [stateLeftChart, h]
  ring

theorem stateLeftChart_odd {x : AnnularState S} (hx : stateSector S x)
    (m : ℕ) (θ : ℝ) : stateLeftChart S x m (-θ) = -stateLeftChart S x m θ := by
  simp only [stateLeftChart, hx.2 m θ]
  ring

theorem neighborhoodStateGrading_chart_le (S : PhysicalSpacesData) (s : ℕ)
    (x : AnnularState S) :
    (S.circle (3 / 4 : ℝ)).grading s x.2.2.2 ≤ stateGrading S s x := by
  have hheight : 0 ≤ (S.height (3 / 4 : ℝ)).grading s x.1.1 + ‖x.1.2‖ :=
    add_nonneg (apply_nonneg ((S.height (3 / 4 : ℝ)).grading s) x.1.1)
      (norm_nonneg x.1.2)
  have hκ := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading s) x.2.2.1
  have htail : ‖x.2.1‖ + ((S.circle (3 / 4 : ℝ)).grading s x.2.2.1 +
      (S.circle (3 / 4 : ℝ)).grading s x.2.2.2) ≤ stateGrading S s x :=
    (le_add_of_nonneg_left hheight).trans_eq (neighborhoodStateGrading_apply S s x).symm
  exact ((le_add_of_nonneg_left hκ).trans
    (le_add_of_nonneg_left (norm_nonneg x.2.1))).trans htail

/-- The derivative defect is controlled by the distance from the actual
reference state, whose circle chart coordinate vanishes. -/
theorem stateLeftChart_deriv_sub_one_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : AnnularState S, ∀ m θ,
      |deriv (stateLeftChart S x m) θ - 1| ≤
        K * stateGrading S 2 (x - C.referenceState) := by
  obtain ⟨K, hK, hbound⟩ := circleModel_deriv_le_grading hT
    (materialSample_mem_radialCore hT hD.choose_spec.2.1)
    (by norm_num : (0 : ℝ) < 3 / 4) (hS.2.1 (3 / 4 : ℝ))
  refine ⟨K, hK, fun x m θ => ?_⟩
  have hz : C.referenceState.2.2.2 = 0 := href.2.2.2.2.1
  have hc : (S.circle (3 / 4 : ℝ)).grading 2 x.2.2.2 ≤
      stateGrading S 2 (x - C.referenceState) := by
    simpa only [Prod.snd_sub, hz, sub_zero] using
      neighborhoodStateGrading_chart_le S 2 (x - C.referenceState)
  rw [deriv_stateLeftChart hS]
  have he : 1 + deriv ((S.circle (3 / 4 : ℝ)).decode x.2.2.2 m) θ - 1 =
      deriv ((S.circle (3 / 4 : ℝ)).decode x.2.2.2 m) θ := by ring
  rw [he]
  exact (hbound x.2.2.2 m θ).trans (mul_le_mul_of_nonneg_left hc hK)

theorem stateLeftChart_strictMono_of_deriv_lower
    (x : AnnularState S) (m : ℕ)
    (h : ∀ θ, (1 / 2 : ℝ) ≤ deriv (stateLeftChart S x m) θ) :
    StrictMono (stateLeftChart S x m) :=
  strictMono_of_deriv_pos fun θ => lt_of_lt_of_le (by norm_num) (h θ)

/-- One positive radius controls the derivatives of all left charts. -/
theorem exists_stateNeighborhood_leftChart_deriv_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ stateNeighborhood S C 2 ε, ∀ m θ,
      (1 / 2 : ℝ) ≤ deriv (stateLeftChart S z.1 m) θ ∧
        deriv (stateLeftChart S z.1 m) θ ≤ 2 := by
  obtain ⟨K, hK, hbound⟩ := stateLeftChart_deriv_sub_one_le hD hT hS href
  have hKone : 0 < K + 1 := by linarith
  let ε : ℝ := 1 / (2 * (K + 1))
  have hε : 0 < ε := div_pos zero_lt_one (mul_pos (by norm_num) hKone)
  have hscale : (K + 1) * ε = (1 / 2 : ℝ) := by
    dsimp only [ε]
    field_simp [hKone.ne']
    <;> ring
  refine ⟨ε, hε, fun z hz m θ => ?_⟩
  have hg : 0 ≤ stateGrading S 2 (z.1 - C.referenceState) := apply_nonneg _ _
  have hsmall : K * stateGrading S 2 (z.1 - C.referenceState) ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ (K + 1) * stateGrading S 2 (z.1 - C.referenceState) :=
        mul_le_mul_of_nonneg_right (by linarith) hg
      _ ≤ (K + 1) * ε := (mul_lt_mul_of_pos_left hz.1 hKone).le
      _ = (1 / 2 : ℝ) := hscale
  have habs := abs_le.mp ((hbound z.1 m θ).trans hsmall)
  constructor <;> linarith only [habs.1, habs.2]

/-- The exact left-chart clause of the common neighborhood specification. -/
theorem exists_stateNeighborhood_leftChart_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ stateNeighborhood S C 2 ε,
      stateSector S z.1 → ∀ m θ,
        (1 / 2 : ℝ) ≤ deriv (stateLeftChart S z.1 m) θ ∧
        deriv (stateLeftChart S z.1 m) θ ≤ 2 ∧
        stateLeftChart S z.1 m (θ + Real.pi) = stateLeftChart S z.1 m θ + Real.pi ∧
        stateLeftChart S z.1 m (-θ) = -stateLeftChart S z.1 m θ := by
  obtain ⟨ε, hε, hbound⟩ := exists_stateNeighborhood_leftChart_deriv_bounds hD hT hS href
  exact ⟨ε, hε, fun z hz hsector m θ =>
    ⟨(hbound z hz m θ).1, (hbound z hz m θ).2,
      stateLeftChart_lift hS z.1 m θ, stateLeftChart_odd hsector m θ⟩⟩

end ContinuousFlexibility.Statements
