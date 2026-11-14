module

public import ContinuousFlexibility.Analysis.TameUniformGrowth
public import ContinuousFlexibility.Analysis.CircleInverseFamilyTame
public import ContinuousFlexibility.Analysis.CirclePositiveLiftDomain

/-!
# Uniform growth of the actual inverse and a common positive domain

The existing inverse operator is zero where its specified derivative
lower bound fails. Its true estimates therefore give a global value
growth bound for each fixed positive lower bound. A common open domain
with half the lower bound contains every lift satisfying the original
bound; this domain is independent of any subsequent radius selector.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

local instance circleInverseUniformGrowthPairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

private theorem uniformLowGrowth_of_linear_unit_bounds
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base loss : ℕ) (V : E → E →ₗ[ℝ] E) (P : E → Prop)
    (hzero : ∀ e, ¬P e → V e = 0)
    (hunit : ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ e ∈ {e | p base e ≤ K ∧ P e}, ∀ u : E, p base u ≤ 1 →
        p s (V e u) ≤ C * (1 + p (s + loss) e + p (s + loss) u)) :
    HasUniformLowGrowth (pairGrading p p) p (fun x : E × E => V x.1 x.2) := by
  classical
  refine ⟨base, loss, fun K hK s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hunit K hK s
  refine ⟨C * (1 + K), mul_nonneg hC (add_nonneg zero_le_one hK), fun x hx => ?_⟩
  have hxe : p base x.1 ≤ K :=
    (le_add_of_nonneg_right (apply_nonneg (p base) x.2)).trans hx
  have hxu : p base x.2 ≤ K :=
    (le_add_of_nonneg_left (apply_nonneg (p base) x.1)).trans hx
  by_cases hpos : P x.1
  · have hnorm := linearMap_oneHigh_bound_of_unitBall (V x.1)
      (p s) (p base) (p (s + loss)) hC
      (fun u hu => hc x.1 ⟨hxe, hpos⟩ u hu.le) x.2
    have hprod : (1 + p (s + loss) x.1) * p base x.2 ≤
        (1 + p (s + loss) x.1) * K :=
      mul_le_mul_of_nonneg_left hxu (add_nonneg zero_le_one (apply_nonneg _ _))
    have hsize : (1 + p (s + loss) x.1) * p base x.2 + p (s + loss) x.2 ≤
        (1 + K) * (1 + p (s + loss) x.1 + p (s + loss) x.2) := by
      nlinarith only [hprod, apply_nonneg (p (s + loss)) x.1,
        apply_nonneg (p (s + loss)) x.2, mul_nonneg hK (apply_nonneg (p (s + loss)) x.2)]
    exact hnorm.trans ((mul_le_mul_of_nonneg_left hsize hC).trans_eq
      (by rw [pairGrading_apply]; ring))
  · change p s (V x.1 x.2) ≤
      C * (1 + K) * (1 + pairGrading p p (s + loss) x)
    rw [hzero x.1 hpos, LinearMap.zero_apply, map_zero]
    exact mul_nonneg (mul_nonneg hC (add_nonneg zero_le_one hK))
      (add_nonneg zero_le_one (apply_nonneg _ _))

private theorem seminorm_self_sub_lt
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) {δ : ℝ} (hδ : 0 < δ) : p (x - x) < δ := by
  simpa only [sub_self, map_zero] using hδ

theorem uniformLowGrowth_circleInverseComposeLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a) :
    HasUniformLowGrowth (pairGrading S.grading S.grading) S.grading
      (fun x : S.Space × S.Space =>
        circleInverseComposeLinear hS hT hD hγ travel a ha x.1 x.2) := by
  classical
  let initialBase : ℕ := hinterp.choose
  let iloss : ℕ := hinterp.choose_spec.choose
  have hi := hinterp.choose_spec.choose_spec
  let base : ℕ := max initialBase (iloss + 2)
  have hbase : iloss + 2 ≤ base := le_max_right _ _
  have hib : initialBase ≤ base := le_max_left _ _
  exact uniformLowGrowth_of_linear_unit_bounds S.grading base (base + iloss + 2)
    (circleInverseComposeLinear hS hT hD hγ travel a ha)
    (fun e => ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ)
    (fun e he => dif_neg he)
    (fun K hK s => circleInverseComposeLinear_unit_growth
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ
      base iloss hbase (fun b c hb hc => hi base b c hib hb hc)
      travel a ha {e | S.grading base e ≤ K ∧
        ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ}
      K hK (fun e he => he.1) (fun e he => he.2) s)

private theorem circleInverseUniform_deriv_sub
    (hS : IsCircleModel T γ S) (e f : S.Space) (m : ℕ) (θ : ℝ) :
    deriv (S.decode (e - f) m) θ =
      deriv (S.decode e m) θ - deriv (S.decode f m) θ := by
  have he : HasDerivAt (S.decode e m) (deriv (S.decode e m) θ) θ :=
    (((hS.2.2.2.1 e).1 m).1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hf : HasDerivAt (S.decode f m) (deriv (S.decode f m) θ) θ :=
    (((hS.2.2.2.1 f).1 m).1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hfield : S.decode (e - f) m = fun t => S.decode e m t - S.decode f m t := by
    funext t
    exact congrFun (congrFun (S.decode.map_sub e f) m) t
  have hd : HasDerivAt (fun t => S.decode e m t - S.decode f m t)
      (deriv (S.decode e m) θ - deriv (S.decode f m) θ) θ :=
    (he.sub hf).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))
  exact (congrArg (fun g : ℝ → ℝ => deriv g θ) hfield).trans hd.deriv

/-- All lifts satisfying the same positive lower bound lie in the
interior of the set with half that bound. -/
theorem circleAffineLift_mem_interior_half_lower
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (e₀ : S.Space)
    (hlower : ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e₀) 1 m) θ) :
    e₀ ∈ interior {e : S.Space |
      ∀ m θ, a / 2 ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ} := by
  obtain ⟨A, hA, hHA⟩ := material_circle_power_upper hT hD hγ
  let L : ℝ := 1 + 2 * circleSobolevConstant * A
  have hL : 0 < L := add_pos_of_pos_of_nonneg zero_lt_one
    (mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) hA)
  let δ : ℝ := (a / 2) / L
  have hδ : 0 < δ := div_pos (half_pos ha) hL
  have hc : Continuous (fun e : S.Space => S.grading 2 (e - e₀)) :=
    ((withSeminorms_graded (fun j => S.level j) S.bond).continuous_seminorm 2).comp
      (continuous_id.sub continuous_const)
  have hball : {e : S.Space | S.grading 2 (e - e₀) < δ} ∈ 𝓝 e₀ :=
    (isOpen_lt hc continuous_const).mem_nhds
      (seminorm_self_sub_lt (S.grading 2) e₀ hδ)
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset hball
  intro e he m θ
  have hb := circleModel_jet_abs_le_material_upper hS
    (material_circle_sample_weights_pos hT hD).2 hA hHA (e - e₀) m 1 θ
  simp only [iteratedDeriv_one, circleInverseUniform_deriv_sub hS] at hb
  have hd : |deriv (S.decode e m) θ - deriv (S.decode e₀ m) θ| ≤
      L * S.grading 2 (e - e₀) := hb.trans
    (mul_le_mul_of_nonneg_right (by dsimp only [L]; linarith) (apply_nonneg _ _))
  have hsmall : L * S.grading 2 (e - e₀) < a / 2 := by
    simpa only [mul_comm L] using (lt_div_iff₀ hL).mp he
  have hdiff := (abs_lt.mp (hd.trans_lt hsmall)).1
  have hbase := hlower m θ
  rw [circleAffineLift_deriv hS] at hbase ⊢
  linarith only [hdiff, hbase]

end ContinuousFlexibility.Statements
