module

public import ContinuousFlexibility.Analysis.NeighborhoodCircleCharts
public import ContinuousFlexibility.Analysis.NeighborhoodStateBounds
public import ContinuousFlexibility.Analysis.SpacesTraceCircleBounds
public import ContinuousFlexibility.Analysis.StateKappaBounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Uniform control of the actual left circle charts

The weighted circle evaluation estimate and the material envelope bound
give a single order-two grading bound for the angular derivative. Since
the reference chart coordinate is zero, one neighborhood controls every
left chart at once. Periodicity comes from the actual circle model and
oddness comes from the stated sector condition.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff ENNReal

private theorem neighborhood_circle_unweight {d H γ B : ℝ}
    (hH : 0 < H) (h : |H ^ (-γ) * d| ≤ B) : |d| ≤ B * H ^ γ := by
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hH (-γ)),
    Real.rpow_neg hH.le, ← div_eq_inv_mul] at h
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hH γ)).mp h

private theorem neighborhood_circle_budget {d w L G K H : ℝ}
    (hK : 0 ≤ K) (hw : 0 ≤ w) (hG : 0 ≤ G)
    (hLG : L ≤ G) (hwH : w ≤ H) (hd : |d| ≤ (K * L) * w) :
    |d| ≤ (K * H) * G := by
  calc
    |d| ≤ (K * L) * w := hd
    _ ≤ (K * G) * w :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLG hK) hw
    _ ≤ (K * G) * H := mul_le_mul_of_nonneg_left hwH (mul_nonneg hK hG)
    _ = (K * H) * G := by ring

private theorem neighborhood_circleMember_deriv_le_weight
    {T : MaterialData} {γ : ℝ} {f : ℕ → ℝ → ℝ}
    (hf : CircleMember T γ f) (m : ℕ) (θ : ℝ) (hH : 0 < T.H (T.sample m)) :
    |deriv (f m) θ| ≤
      (anglePairEvaluationConstant * circleNorm T γ 2 f) * T.H (T.sample m) ^ γ := by
  have hw : |T.H (T.sample m) ^ (-γ) * deriv (f m) θ| ≤
      anglePairEvaluationConstant * ‖circleJetEncodeHilbert hf 2 m‖ := by
    simpa only [pow_zero, one_mul, iteratedDeriv_one] using
      spaces_circle_weighted_pointwise hf 2 m 1 0 (by norm_num) θ
  have hrow : ‖circleJetEncodeHilbert hf 2 m‖ ≤ circleNorm T γ 2 f :=
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (circleJetEncodeHilbert hf 2) m).trans_eq (circleJetEncodeHilbert_norm hf 2)
  exact neighborhood_circle_unweight hH
    (hw.trans (mul_le_mul_of_nonneg_left hrow anglePairEvaluationConstant_nonneg))

/-- First derivatives of every decoded circle have one uniform order-two
bound, with no dependence on the circle index or evaluation point. -/
theorem circleModel_deriv_le_grading
    {D : ReferenceData} {T : MaterialData} {M : CircleModelData} {γ : ℝ}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    (hγ : 0 < γ) (hM : IsCircleModel T γ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : M.Space, ∀ m θ,
      |deriv (M.decode u m) θ| ≤ K * M.grading 2 u := by
  have hPower := hT.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEnvelope := hPower 0 γ hγ
  let H : ℝ := hEnvelope.choose
  have hH : 0 < H := hEnvelope.choose_spec.1
  have hHbound : ∀ r ∈ Ioo D.a D.b, T.H r ^ γ * T.M r ^ (0 : ℝ) ≤ H :=
    hEnvelope.choose_spec.2.1
  refine ⟨anglePairEvaluationConstant * H,
    mul_nonneg anglePairEvaluationConstant_nonneg hH.le, ?_⟩
  intro u m θ
  have hu : CircleMember T γ (M.decode u) := hM.2.2.2.1 u
  have hpos : 0 < T.H (T.sample m) := (hT.2.1 _ (hsample m)).2.1
  have hweight : T.H (T.sample m) ^ γ ≤ H := by
    simpa only [Real.rpow_zero, mul_one] using hHbound _ (hsample m)
  have hnorm : circleNorm T γ 2 (M.decode u) ≤ M.grading 2 u :=
    (hM.2.2.2.2.2.2.2 u 2).symm.trans_le
      (Analysis.norm_coordinate_le_graded _ _ le_rfl u)
  exact neighborhood_circle_budget anglePairEvaluationConstant_nonneg
    (Real.rpow_nonneg hpos.le γ) (apply_nonneg (M.grading 2) u) hnorm hweight
    (neighborhood_circleMember_deriv_le_weight hu m θ hpos)

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

private theorem neighborhood_circleChart_defect {a d B : ℝ}
    (ha : a = 1 + d) (hd : |d| ≤ B) : |a - 1| ≤ B := by
  have he : a - 1 = d := by linarith only [ha]
  exact (congrArg abs he).trans_le hd

/-- The derivative defect is controlled by the distance from the actual
reference state, whose circle chart coordinate vanishes. -/
theorem stateLeftChart_deriv_sub_one_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : AnnularState S, ∀ m θ,
      |deriv (stateLeftChart S x m) θ - 1| ≤
        K * stateGrading S 2 (x - C.referenceState) := by
  have hex := circleModel_deriv_le_grading
    (D := D) (T := T) (M := S.circle (3 / 4 : ℝ)) (γ := (3 / 4 : ℝ)) hT
    (materialSample_mem_radialCore hT hD.choose_spec.2.1)
    (by norm_num : (0 : ℝ) < 3 / 4) (hS.2.1 (3 / 4 : ℝ))
  let K : ℝ := hex.choose
  have hK : 0 ≤ K := hex.choose_spec.1
  have hbound := hex.choose_spec.2
  refine ⟨K, hK, fun x m θ => ?_⟩
  have hz : C.referenceState.2.2.2 = 0 := href.2.2.2.2.1
  have hcoord : (x - C.referenceState).2.2.2 = x.2.2.2 := by
    simp only [Prod.snd_sub, hz, sub_zero]
  have hc : (S.circle (3 / 4 : ℝ)).grading 2 x.2.2.2 ≤
      stateGrading S 2 (x - C.referenceState) :=
    (congrArg ((S.circle (3 / 4 : ℝ)).grading 2) hcoord).symm.trans_le
      (neighborhoodStateGrading_chart_le S 2 (x - C.referenceState))
  exact neighborhood_circleChart_defect (deriv_stateLeftChart hS x m θ)
    ((hbound x.2.2.2 m θ).trans (mul_le_mul_of_nonneg_left hc hK))

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
