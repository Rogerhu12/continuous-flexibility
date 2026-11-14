module

public import ContinuousFlexibility.Analysis.N04NegativeChartRootTimeJets
public import ContinuousFlexibility.Analysis.N04NegativeChartRootForcingPrefix
public import ContinuousFlexibility.Analysis.N04NegativeChartVariationInduction
public import ContinuousFlexibility.Analysis.N04NegativeChartFiberComposition

/-! Uniform finite state prefixes of the supplied inverse root flow.
The index type contains every admissible coefficient representative and
flow. Thus the variation constants precede every actual input. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- All quantitative assumptions concern the original field on one
physical radial fiber. No state-variation bound on the flow is an input. -/
structure NegativeChartRootInverseInput (P : Type) [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] (N K shift : ℕ) (RH : ℝ) where
  d : P × PolarPoint → ℝ
  c : P × PolarPoint → ℝ
  hd : ContDiff ℝ ∞ d
  hc : ContDiff ℝ ∞ c
  dp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi
  cp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi
  δ : ℝ
  flow : NegativeChartRootFlowData d c δ
  q : N04FlowPoint
  p₀ : Seminorm ℝ P
  p₁ : Seminorm ℝ P
  R : ℝ
  H : ℝ
  M : ℝ
  ρ : ℝ
  hR : 1 ≤ R
  hH : 0 ≤ H
  hHR : H ≤ RH
  hM : 1 ≤ M
  hρ : 1 ≤ ρ
  angle : ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ,
    |deriv (fun η => rootRescaledField (fun p => d (0, p)) (fun p => c (0, p)) δ
      (t, (q.1, η))) θ| ≤ 1
  raw : ∀ k, k ≤ N → ∀ v : Fin k → P,
    (∀ a, p₀ (v a) ≤ 1) → (∀ a, p₁ (v a) ≤ R) →
    ∀ j, j ≤ K + N + 1 → ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ,
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        flowParameterField (negativeChartRootPlotField d c δ) k (0, y.1)
          (fun a => (v a, (0 : PolarPoint))) (t, y.2)) (q.1, θ)‖ ≤
        M * parameterHeightWeight H k * ρ ^ (j - 1 + shift * k)

namespace NegativeChartRootInverseInput

variable {N K shift : ℕ} {RH : ℝ} (i : NegativeChartRootInverseInput P N K shift RH)

def original : ℝ × N04FlowPoint → ℝ :=
  rootRescaledField (fun p => i.d (0, p)) (fun p => i.c (0, p)) i.δ

def field : (P × PolarPoint) × PolarPoint → ℝ :=
  scalarFieldTimeChange (negativeChartRootPlotReverseField i.d i.c i.δ) 0 1

def trajectory : (P × PolarPoint) × PolarPoint → ℝ :=
  negativeChartRootPlotTimeChange i.flow.inverse

theorem original_smooth : ContDiff ℝ ∞ i.original :=
  contDiff_rootRescaledField (i.hd.comp (contDiff_const.prodMk contDiff_id))
    (i.hc.comp (contDiff_const.prodMk contDiff_id)) i.δ

theorem original_periodic : ∀ t v,
    Function.Periodic (fun θ => i.original (t, (v, θ))) Real.pi :=
  rootRescaledField_periodic (i.dp 0) (i.cp 0) i.δ

theorem field_smooth : ContDiff ℝ ∞ i.field :=
  contDiff_scalarFieldTimeChange
    (negativeChartRootPlotReverseField_contDiff i.hd i.hc i.δ) 0 1

theorem trajectory_smooth : ContDiff ℝ ∞ i.trajectory := i.flow.inverse_smooth

theorem original_raw (j : ℕ) (hj : j ≤ K + N + 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y => i.original (t, y)) (i.q.1, θ)‖ ≤
      i.M * i.ρ ^ (j - 1) := by
  have hb := i.raw 0 (Nat.zero_le _) Fin.elim0 (fun a => a.elim0)
    (fun a => a.elim0) j hj t ht θ
  simpa only [flowParameterField, iteratedFDeriv_zero_apply, parameterHeightWeight,
    ↓reduceIte, mul_one, Nat.mul_zero, Nat.add_zero, original, negativeChartRootPlotField] using hb

theorem field_raw {T : ℝ} (hT : 0 ≤ T)
    (hτ : ∀ t ∈ Icc (0 : ℝ) 1, |deriv (compactScalarFlowTime 0 1) t| ≤ T)
    (k : ℕ) (hk : k ≤ N) (v : Fin k → P)
    (hv₀ : ∀ a, i.p₀ (v a) ≤ 1) (hv₁ : ∀ a, i.p₁ (v a) ≤ i.R)
    (j : ℕ) (hj : j ≤ K + N + 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
      flowParameterField i.field k (0, y.1) (fun a => (v a, (0 : PolarPoint)))
        (t, y.2)) (i.q.1, θ)‖ ≤
      (T * i.M) * parameterHeightWeight i.H k * i.ρ ^ (j - 1 + shift * k) := by
  have hr := n04Flow_compactTime_mem t
  have hrev : 1 - compactScalarFlowTime 0 1 t ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith only [hr.2], by linarith only [hr.1]⟩
  change ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
    flowParameterField (scalarFieldTimeChange
      (negativeChartRootPlotReverseField i.d i.c i.δ) 0 1) k (0, y.1)
        (fun a => (v a, (0 : PolarPoint))) (t, y.2)) (i.q.1, θ)‖ ≤ _
  rw [n04NegativeChart_scalarTimeChange_spatialJet_norm
    (negativeChartRootPlotReverseField_contDiff i.hd i.hc i.δ),
    negativeChartRootPlotReverseField_spatialJet_norm]
  exact (mul_le_mul (hτ t ht) (i.raw k hk v hv₀ hv₁ j hj _ hrev θ)
    (norm_nonneg _) hT).trans_eq (by ring)

theorem coefficient_primitive {T : ℝ} (hT : 0 ≤ T)
    (hτ : ∀ t ∈ Icc (0 : ℝ) 1, |deriv (compactScalarFlowTime 0 1) t| ≤ T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |∫ r in (0 : ℝ)..t,
      flowVariationCoefficient i.field i.trajectory (0, i.q.1) (r, i.q.2)| ≤ T := by
  have hk (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      |flowVariationCoefficient i.field i.trajectory (0, i.q.1) (r, i.q.2)| ≤ T := by
    have hu := n04Flow_compactTime_mem r
    have hv : 1 - compactScalarFlowTime 0 1 r ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith only [hu.2], by linarith only [hu.1]⟩
    rw [flowVariationCoefficient_eq_deriv i.field_smooth]
    change |deriv (fun θ => deriv (compactScalarFlowTime 0 1) r *
      -i.original (1 - compactScalarFlowTime 0 1 r, (i.q.1, θ)))
        (i.trajectory ((0, i.q.1), (r, i.q.2)))| ≤ T
    rw [deriv_const_mul_field, deriv.fun_neg, abs_mul, abs_neg]
    exact (mul_le_mul (hτ r hr) (i.angle _ hv _) (abs_nonneg _) hT).trans_eq
      (mul_one T)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (C := T)
    (f := fun r => flowVariationCoefficient i.field i.trajectory (0, i.q.1) (r, i.q.2))
    (fun r hr => by
      have hr' : r ∈ Icc (0 : ℝ) t := by
        simpa only [uIcc_of_le ht.1] using uIoc_subset_uIcc hr
      simpa only [Real.norm_eq_abs] using hk r ⟨hr'.1, hr'.2.trans ht.2⟩)
  have hb' : |∫ r in (0 : ℝ)..t,
      flowVariationCoefficient i.field i.trajectory (0, i.q.1) (r, i.q.2)| ≤ T * t := by
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] using hb
  exact hb'.trans (mul_le_of_le_one_right hT ht.2)

/-- The zeroth spatial jet is the actual displacement of the same
inverse. It requires no estimate on the angular lift itself. -/
theorem displacement : |i.flow.inverse 0 i.q.1 1 i.q.2 - i.q.2| ≤ i.M := by
  apply n04Flow_displacement_abs_le (n04FlowReverseField_contDiff i.original_smooth)
    (i.flow.inverse_equations 0) i.q.1 i.q.2 (zero_le_one.trans i.hM) ?_
    ⟨zero_le_one, le_rfl⟩
  intro r hr θ
  have hrev : 1 - r ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith only [hr.2], by linarith only [hr.1]⟩
  simpa only [n04FlowReverseField, abs_neg, norm_iteratedFDeriv_zero,
    Real.norm_eq_abs, Nat.zero_sub, pow_zero, mul_one] using
      i.original_raw 0 (Nat.zero_le _) (1 - r) hrev θ

end NegativeChartRootInverseInput

/-- Positive spatial orders of the supplied inverse retain degree j-1.
The estimate is at every compactified time and on the original fiber. -/
theorem n04NegativeChart_rootInverse_stateFree_prefix (N K shift : ℕ) (RH : ℝ) :
    ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧
      ∀ i : NegativeChartRootInverseInput P N K shift RH,
      ∀ j, 1 ≤ j → j ≤ K → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
          i.trajectory ((0, y.1), (t, y.2))) i.q‖ ≤ C * i.M ^ e * i.ρ ^ (j - 1) := by
  obtain ⟨C, e, hC, hb⟩ := n04NegativeChart_flow_point_prefix K
  refine ⟨C, e, hC, fun i j hj hjK t ht => ?_⟩
  have ha (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
      |deriv (fun η => n04FlowReverseField i.original (r, (i.q.1, η))) θ| ≤ 1 := by
    change |deriv (fun η => -i.original (1 - r, (i.q.1, η))) θ| ≤ 1
    rw [deriv.fun_neg, abs_neg]
    exact i.angle _ ⟨by linarith only [hr.2], by linarith only [hr.1]⟩ θ
  have hraw (a : ℕ) (haK : a ≤ K) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
      ‖iteratedFDeriv ℝ (a + 1) (fun y : N04FlowPoint =>
        n04FlowReverseField i.original (r, y)) (i.q.1, θ)‖ ≤ i.M * i.ρ ^ a := by
    have he : (fun y : N04FlowPoint => n04FlowReverseField i.original (r, y)) =
        -(fun y => i.original (1 - r, y)) := rfl
    rw [he, iteratedFDeriv_neg_apply, norm_neg]
    simpa only [Nat.add_sub_cancel] using i.original_raw (a + 1) (by omega)
      (1 - r) ⟨by linarith only [hr.2], by linarith only [hr.1]⟩ θ
  have hh := hb i.hM i.hρ (n04FlowReverseField i.original)
    (n04FlowReverseField_contDiff i.original_smooth)
    (n04FlowReverseField_periodic i.original_periodic)
    (i.flow.inverse 0) (i.flow.inverse_equations 0) i.q ha hraw
    (j - 1) (by omega) (compactScalarFlowTime 0 1 t) (n04Flow_compactTime_mem t)
  rw [Nat.sub_add_cancel hj] at hh
  simpa only [NegativeChartRootInverseInput.trajectory, negativeChartRootPlotTimeChange] using hh

private theorem rootTime_derivative_bound :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      |deriv (compactScalarFlowTime 0 1) t| ≤ T := by
  have hτ := (contDiff_infty_iff_deriv.mp (contDiff_compactScalarFlowTime 0 1)).2.continuous
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hτ.continuousOn
  refine ⟨max 1 B, le_max_left _ _, fun t ht => ?_⟩
  exact (show |deriv (compactScalarFlowTime 0 1) t| ≤ B from
    by simpa only [Real.norm_eq_abs] using hB t ht).trans (le_max_right _ _)

namespace NegativeChartRootInverseInput

variable {N K shift : ℕ} {RH : ℝ} (i : NegativeChartRootInverseInput P N K shift RH)

theorem coefficient_prefix {T B : ℝ} (hT : 0 ≤ T) (hB : 1 ≤ B)
    (hτ : ∀ t ∈ Icc (0 : ℝ) 1, |deriv (compactScalarFlowTime 0 1) t| ≤ T)
    (hflow : ∀ j, 1 ≤ j → j ≤ K → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        i.trajectory ((0, y.1), (t, y.2))) i.q‖ ≤ B * i.ρ ^ (j - 1))
    (j : ℕ) (hj : j ≤ K) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
      flowVariationCoefficient i.field i.trajectory (0, y.1) (t, y.2)) i.q‖ ≤
        ((K.factorial : ℝ) * (T * i.M) * B ^ K) * i.ρ ^ j := by
  let F : ℝ × N04FlowPoint → ℝ := fun z => i.field ((0, z.2.1), (z.1, z.2.2))
  have hF : ContDiff ℝ ∞ F := i.field_smooth.comp
    ((contDiff_const.prodMk contDiff_snd.fst).prodMk
      (contDiff_fst.prodMk contDiff_snd.snd))
  have hΘ : ContDiff ℝ ∞ (fun y : N04FlowPoint => i.trajectory ((0, y.1), (t, y.2))) :=
    i.trajectory_smooth.comp
      ((contDiff_const.prodMk contDiff_fst).prodMk (contDiff_const.prodMk contDiff_snd))
  have hraw (a : ℕ) (ha : a ≤ K) (θ : ℝ) :
      ‖iteratedFDeriv ℝ (a + 1) (fun y => F (t, y)) (i.q.1, θ)‖ ≤
        (T * i.M) * i.ρ ^ a := by
    have hh := i.field_raw hT hτ 0 (Nat.zero_le _) Fin.elim0 (fun a => a.elim0)
      (fun a => a.elim0) (a + 1) (by omega) t ht θ
    simpa only [flowParameterField, iteratedFDeriv_zero_apply, parameterHeightWeight,
      ↓reduceIte, mul_one, Nat.mul_zero, Nat.add_zero, Nat.add_sub_cancel, F] using hh
  have he : (fun y : N04FlowPoint =>
      flowVariationCoefficient i.field i.trajectory (0, y.1) (t, y.2)) =
      fun y : N04FlowPoint => deriv (fun θ => F (t, (y.1, θ)))
        (i.trajectory ((0, y.1), (t, y.2))) :=
    funext (fun y => flowVariationCoefficient_eq_deriv i.field_smooth (0, y.1) (t, y.2))
  rw [he]
  exact n04NegativeChart_angleComposition_point_prefix hF hΘ K t i.q
    (mul_nonneg hT (zero_le_one.trans i.hM)) hB i.hρ hraw
    (fun a ha haK => hflow a ha haK t ht) j hj

end NegativeChartRootInverseInput

/-- One state degree is selected before the spatial prefix. The universal
index contains all coefficient representatives, sampled envelopes and
supplied inverse flows, so the final constant is uniform over them. -/
theorem n04NegativeChart_rootInverse_positive_prefix (N shift : ℕ)
    (RH : ℝ) (hRH : 1 ≤ RH) :
    ∃ D : ℕ, shift + 2 ≤ D ∧ ∀ K : ℕ,
      ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧
      ∀ i : NegativeChartRootInverseInput P N K shift RH,
      ∀ k, 0 < k → k ≤ N → ∀ v : Fin k → P,
        (∀ a, i.p₀ (v a) ≤ 1) → (∀ a, i.p₁ (v a) ≤ i.R) →
      ∀ j, j ≤ K →
        ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
          flowParameterField (fun z : (P × PolarPoint) × PolarPoint =>
            i.flow.inverse z.1.1 z.1.2 z.2.1 z.2.2) k (0, y.1)
              (fun a => (v a, (0 : PolarPoint))) (1, y.2)) i.q‖ ≤
          C * i.H * i.M ^ e * i.ρ ^ (j - 1 + D * k) := by
  classical
  let head : ℕ → ℕ := fun k => (shift + 1) * k
  let degree : ℕ → ℕ := negativeChartVariationDegree head
  let D : ℕ := shift + 3 + ∑ k : Fin (N + 1), degree k.val
  refine ⟨D, by dsimp only [D]; omega, fun K => ?_⟩
  let I := NegativeChartRootInverseInput P N K shift RH
  obtain ⟨T, hT, hτ⟩ := rootTime_derivative_bound
  obtain ⟨Cf, ef, hCf, hfree⟩ := n04NegativeChart_rootInverse_stateFree_prefix
    (P := P) N K shift RH
  let B : I → ℝ := fun i => Cf * i.M ^ ef
  have hB (i : I) : 1 ≤ B i :=
    one_le_mul_of_one_le_of_one_le hCf (one_le_pow₀ i.hM)
  let Chead : ℝ := (K.factorial : ℝ) * T * Cf ^ K
  let ehead : ℕ := ef * K + 1
  have hChead : 1 ≤ Chead := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos K)) hT)
    (one_le_pow₀ hCf)
  have hpoly (i : I) : (K.factorial : ℝ) * (T * i.M) * B i ^ K =
      Chead * i.M ^ ehead := by
    dsimp only [B, Chead, ehead]
    rw [mul_pow, ← pow_mul, pow_succ]
    ring
  let J (i : I) : ContinuousTimeSpeedTower (univ : Set (P × PolarPoint)) i.field :=
    continuousTimeSpeedTowerOfContDiff i.field_smooth
  let admissible (n : ℕ) (i : I) (v : Fin n → P × PolarPoint) : Prop :=
    ∀ a, (v a).2 = 0 ∧ i.p₀ (v a).1 ≤ 1 ∧ i.p₁ (v a).1 ≤ i.R
  have hrestrict : ∀ n i v, admissible n i v → ∀ a (f : Fin a → Fin n),
      admissible a i (v ∘ f) := fun _ _ _ hv _ f a => hv (f a)
  have hcoefficient : ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧ ∀ (i : I) j,
      1 ≤ j → j ≤ K → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        flowVariationCoefficient i.field i.trajectory (0, y.1) (t, y.2)) i.q‖ ≤
          C * i.M ^ e * i.ρ ^ j := by
    refine ⟨Chead, ehead, hChead, fun i j _ hj t ht => ?_⟩
    exact (i.coefficient_prefix (zero_le_one.trans hT) (hB i) hτ
      (hfree i) j hj t ht).trans_eq (congrArg (fun a : ℝ => a * i.ρ ^ j) (hpoly i))
  have hhead : ∀ n, n ≤ N → 0 < n → ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧
      ∀ (i : I) (v : Fin n → P × PolarPoint), admissible n i v →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ d : FlowForcingChoice n, ∀ j, j ≤ K →
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        canonicalFlowForcingFactors (J i) i.trajectory_smooth (0, y.1) v t d 0 y.2) i.q‖ ≤
          parameterHeightWeight i.H d.2.card * (C * i.M ^ e) * i.ρ ^ (head n + j) := by
    intro n hnN hn
    refine ⟨Chead, ehead, hChead, fun i v hv t ht d j hj => ?_⟩
    let u : Fin n → P := fun a => (v a).1
    have he : v = fun a => (u a, (0 : PolarPoint)) := by
      funext a
      exact Prod.ext rfl (hv a).1
    rw [he]
    have hh := negativeChart_actual_forcing_head_prefix i.field_smooth (J i)
      i.trajectory_smooth n K shift u i.p₀ i.p₁ i.hR
      (mul_nonneg (zero_le_one.trans hT) (zero_le_one.trans i.hM))
      (hB i) i.hH i.hρ (fun a => (hv a).2.1) (fun a => (hv a).2.2) t i.q
      (fun k hk w hw₀ hw₁ l hl θ => i.field_raw (zero_le_one.trans hT) hτ
        k (hk.trans hnN) w hw₀ hw₁ l (by omega) t ht θ)
      (fun a ha haK => hfree i a ha haK t ht) d j hj
    exact hh.trans_eq (congrArg (fun a : ℝ =>
      parameterHeightWeight i.H d.2.card * a * i.ρ ^ ((shift + 1) * n + j)) (hpoly i))
  have hvar := n04NegativeChart_actualVariation_prescribed_prefix N K
    (fun i : I => i.field) (fun i : I => i.trajectory)
    (fun i => i.field_smooth) J (fun i => i.trajectory_smooth)
    (fun i => i.flow.inverse_initial) (fun i => i.flow.inverse_time)
    (fun (_ : I) (y : N04FlowPoint) => ((0 : P), y.1))
    (fun (_ : I) (y : N04FlowPoint) => y.2)
    (fun _ => contDiff_const.prodMk contDiff_fst) (fun _ => contDiff_snd)
    (fun i => i.q) (fun i => i.H) (fun i => i.M) (fun i => i.ρ)
    admissible hrestrict hRH (zero_le_one.trans hT)
    (fun i => i.hH) (fun i => i.hHR) (fun i => i.hM) (fun i => i.hρ)
    (fun i => i.coefficient_primitive (zero_le_one.trans hT) hτ)
    hcoefficient head hhead
  choose C e hC hb using (fun k : Fin (N + 1) => hvar k.val (by omega))
  let Ctotal : ℝ := 1 + ∑ k : Fin (N + 1), C k
  let etotal : ℕ := ∑ k : Fin (N + 1), e k
  have hCtotal : 1 ≤ Ctotal := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun k _ => zero_le_one.trans (hC k)))
  refine ⟨Ctotal, etotal, hCtotal, fun i k hk hkN v hv₀ hv₁ j hj => ?_⟩
  let a : Fin (N + 1) := ⟨k, by omega⟩
  have hCa : C a ≤ Ctotal := (Finset.single_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset (Fin (N + 1)))) => zero_le_one.trans (hC b))
    (Finset.mem_univ a)).trans (le_add_of_nonneg_left zero_le_one)
  have hea : e a ≤ etotal := Finset.single_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset (Fin (N + 1)))) => Nat.zero_le (e b))
    (Finset.mem_univ a)
  have hda : degree k + 1 ≤ D := by
    have hs : degree k ≤ ∑ b : Fin (N + 1), degree b.val :=
      Finset.single_le_sum (fun b _ => Nat.zero_le (degree b.val)) (Finset.mem_univ a)
    dsimp only [D]
    omega
  have hdegree : degree k + j ≤ j - 1 + D * k := by
    have hm : D * 1 ≤ D * k := Nat.mul_le_mul_left D hk
    simp only [Nat.mul_one] at hm
    omega
  have hamp : C a * i.H * i.M ^ e a ≤ Ctotal * i.H * i.M ^ etotal :=
    mul_le_mul (mul_le_mul_of_nonneg_right hCa i.hH)
      (pow_le_pow_right₀ i.hM hea) (pow_nonneg (zero_le_one.trans i.hM) _)
      (mul_nonneg (zero_le_one.trans hCtotal) i.hH)
  have hh := hb a hk i (fun b => (v b, (0 : PolarPoint)))
    (fun b => ⟨rfl, hv₀ b, hv₁ b⟩) j hj 1 ⟨zero_le_one, le_rfl⟩
  have hbound := hh.trans (mul_le_mul hamp (pow_le_pow_right₀ i.hρ hdegree)
    (pow_nonneg (zero_le_one.trans i.hρ) _)
    (mul_nonneg (mul_nonneg (zero_le_one.trans hCtotal) i.hH)
      (pow_nonneg (zero_le_one.trans i.hM) _)))
  rw [← i.flow.inverse_endpoint_spatialJet k j v i.q]
  exact hbound

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_rootInverse_positive_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_rootInverse_positive_prefix
