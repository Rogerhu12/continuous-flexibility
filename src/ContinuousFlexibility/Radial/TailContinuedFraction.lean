module

public import ContinuousFlexibility.Statements.Radial
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# The natural-line continued fraction on a deep tail

The exact backward elimination map on each node preserves [1, 2] and
contracts uniformly. Finite walls give its unique bounded limit with an
explicit uniform error bound and continuous dependence on the coefficients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology

/-- One backward elimination step for the normalized node ratios. -/
def tailFractionStep (ε : ℕ → ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 - ε (n + 1) * v (n + 1))⁻¹

/-- Finite outer wall with terminal normalized ratio one. -/
def tailFractionTrunc (ε : ℕ → ℝ) (k n : ℕ) : ℝ :=
  (tailFractionStep ε)^[k] (fun _ => 1) n

private theorem tailFraction_den_bounds {e x : ℝ} (he : e ∈ Icc 0 (1 / 8))
    (hx : x ∈ Icc 1 2) : 3 / 4 ≤ 1 - e * x ∧ 1 - e * x ≤ 1 := by
  have h₀ := mul_nonneg he.1 (zero_le_one.trans hx.1)
  have h₁ := mul_le_mul he.2 hx.2 (zero_le_one.trans hx.1) (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

private theorem tailFraction_scalar_mem {e x : ℝ} (he : e ∈ Icc 0 (1 / 8))
    (hx : x ∈ Icc 1 2) : (1 - e * x)⁻¹ ∈ Icc 1 2 := by
  have h := tailFraction_den_bounds he hx
  have hp : 0 < 1 - e * x := (by norm_num : (0 : ℝ) < 3 / 4).trans_le h.1
  rw [← one_div]
  exact ⟨(le_div_iff₀ hp).mpr (by linarith only [h.2]),
    (div_le_iff₀ hp).mpr (by linarith only [h.1])⟩

private theorem tailFraction_scalar_contracts {e x y : ℝ} (he : e ∈ Icc 0 (1 / 8))
    (hx : x ∈ Icc 1 2) (hy : y ∈ Icc 1 2) :
    |(1 - e * x)⁻¹ - (1 - e * y)⁻¹| ≤ (1 / 2 : ℝ) * |x - y| := by
  let a := 1 - e * x
  let b := 1 - e * y
  have ha : 3 / 4 ≤ a := (tailFraction_den_bounds he hx).1
  have hb : 3 / 4 ≤ b := (tailFraction_den_bounds he hy).1
  have ha₀ : 0 < a := (by norm_num : (0 : ℝ) < 3 / 4).trans_le ha
  have hb₀ : 0 < b := (by norm_num : (0 : ℝ) < 3 / 4).trans_le hb
  have hprod : (3 / 4 : ℝ) * (3 / 4) ≤ a * b :=
    mul_le_mul ha hb (by norm_num) ha₀.le
  have heq : a⁻¹ - b⁻¹ = e * (x - y) / (a * b) := by
    field_simp [ha₀.ne', hb₀.ne']
    dsimp only [a, b]
    ring
  change |a⁻¹ - b⁻¹| ≤ _
  rw [heq, abs_div, abs_mul, abs_of_nonneg he.1, abs_of_pos (mul_pos ha₀ hb₀)]
  apply (div_le_iff₀ (mul_pos ha₀ hb₀)).mpr
  have hcoeff : e ≤ (1 / 2 : ℝ) * (a * b) := by linarith only [he.2, hprod]
  calc
    _ ≤ ((1 / 2 : ℝ) * (a * b)) * |x - y| :=
      mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
    _ = _ := by ring

private theorem tailFraction_iterate_mem {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Icc 0 (1 / 8))
    {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Icc 1 2) (k n : ℕ) :
    (tailFractionStep ε)^[k] v n ∈ Icc 1 2 := by
  induction k generalizing n with
  | zero => exact hv n
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact tailFraction_scalar_mem (hε (n + 1)) (ih (n + 1))

private theorem tailFraction_iterate_compare {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Icc 0 (1 / 8))
    {v w : ℕ → ℝ} (hv : ∀ n, v n ∈ Icc 1 2) (hw : ∀ n, w n ∈ Icc 1 2) (k n : ℕ) :
    |(tailFractionStep ε)^[k] v n - (tailFractionStep ε)^[k] w n| ≤ (1 / 2 : ℝ) ^ k := by
  induction k generalizing n with
  | zero =>
    simp only [Function.iterate_zero_apply, pow_zero]
    exact abs_le.mpr ⟨by linarith only [(hv n).1, (hw n).2],
      by linarith only [(hv n).2, (hw n).1]⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ']
    exact (tailFraction_scalar_contracts (hε (n + 1))
      (tailFraction_iterate_mem hε hv k (n + 1))
      (tailFraction_iterate_mem hε hw k (n + 1))).trans
      (mul_le_mul_of_nonneg_left (ih (n + 1)) (by norm_num))

private theorem tailFractionTrunc_compare {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Icc 0 (1 / 8))
    {k l : ℕ} (hkl : k ≤ l) (n : ℕ) :
    |tailFractionTrunc ε l n - tailFractionTrunc ε k n| ≤ (1 / 2 : ℝ) ^ k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkl
  have hOne : ∀ _ : ℕ, (1 : ℝ) ∈ Icc 1 2 := fun _ => ⟨le_rfl, by norm_num⟩
  unfold tailFractionTrunc
  rw [Function.iterate_add_apply]
  exact tailFraction_iterate_compare hε (tailFraction_iterate_mem hε hOne r) hOne k n

private theorem tailFractionTrunc_limit {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Icc 0 (1 / 8))
    (n : ℕ) : ∃ t : ℝ, Tendsto (fun k => tailFractionTrunc ε k n) atTop (𝓝 t) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff'.mpr
  intro δ hδ
  have hp : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hp.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq]
  exact (tailFractionTrunc_compare hε hk n).trans_lt (hN N le_rfl)

/-- The unique bounded limit of the finite-wall ratios. -/
def tailFractionLimit (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Icc 0 (1 / 8)) (n : ℕ) : ℝ :=
  (tailFractionTrunc_limit hε n).choose

theorem tendsto_tailFractionTrunc (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Icc 0 (1 / 8)) (n : ℕ) :
    Tendsto (fun k => tailFractionTrunc ε k n) atTop (𝓝 (tailFractionLimit ε hε n)) :=
  (tailFractionTrunc_limit hε n).choose_spec

theorem tailFractionLimit_mem (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Icc 0 (1 / 8)) (n : ℕ) :
    tailFractionLimit ε hε n ∈ Icc 1 2 :=
  isClosed_Icc.mem_of_tendsto (tendsto_tailFractionTrunc ε hε n)
    (Eventually.of_forall fun k => tailFraction_iterate_mem hε
      (fun _ => ⟨le_rfl, by norm_num⟩) k n)

theorem tailFractionLimit_error (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Icc 0 (1 / 8)) (k n : ℕ) :
    |tailFractionLimit ε hε n - tailFractionTrunc ε k n| ≤ (1 / 2 : ℝ) ^ k := by
  apply le_of_tendsto ((tendsto_tailFractionTrunc ε hε n).sub tendsto_const_nhds).abs
  filter_upwards [eventually_ge_atTop k] with l hl
  exact tailFractionTrunc_compare hε hl n

/-- Exact backward equation for the limit selected by finite walls. -/
theorem tailFractionLimit_eq_step (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Icc 0 (1 / 8)) (n : ℕ) :
    tailFractionLimit ε hε n = tailFractionStep ε (tailFractionLimit ε hε) n := by
  have h := tailFraction_den_bounds (hε (n + 1)) (tailFractionLimit_mem ε hε (n + 1))
  have hpos : 0 < 1 - ε (n + 1) * tailFractionLimit ε hε (n + 1) :=
    (by norm_num : (0 : ℝ) < 3 / 4).trans_le h.1
  have hright := (tendsto_const_nhds.sub
    (tendsto_const_nhds.mul (tendsto_tailFractionTrunc ε hε (n + 1)))).inv₀ hpos.ne'
  have hleft := (tendsto_tailFractionTrunc ε hε n).comp (tendsto_add_atTop_nat 1)
  have heq (k : ℕ) : tailFractionTrunc ε (k + 1) n =
      (1 - ε (n + 1) * tailFractionTrunc ε k (n + 1))⁻¹ := by
    unfold tailFractionTrunc
    rw [Function.iterate_succ_apply']
    rfl
  exact tendsto_nhds_unique hleft (hright.congr (fun k => (heq k).symm))

theorem tailFractionLimit_unique (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Icc 0 (1 / 8))
    {t : ℕ → ℝ} (ht : ∀ n, t n ∈ Icc 1 2) (he : ∀ n, t n = tailFractionStep ε t n) :
    t = tailFractionLimit ε hε := by
  funext n
  have htFix (k : ℕ) : (tailFractionStep ε)^[k] t = t := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      exact (funext he).symm
  have hdist (k : ℕ) : |t n - tailFractionTrunc ε k n| ≤ (1 / 2 : ℝ) ^ k := by
    have h := tailFraction_iterate_compare hε ht (fun _ => ⟨le_rfl, by norm_num⟩) k n
    rw [htFix] at h
    exact h
  have hp : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := le_of_tendsto_of_tendsto'
    (tendsto_const_nhds.sub (tendsto_tailFractionTrunc ε hε n)).abs hp hdist
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- Uniform contraction gives continuous dependence on each coordinate of
any coefficient family with the same smallness bound. -/
theorem continuous_tailFractionLimit {P : Type*} [TopologicalSpace P]
    (ε : P → ℕ → ℝ) (hε : ∀ p n, ε p n ∈ Icc 0 (1 / 8))
    (hcont : ∀ n, Continuous (fun p => ε p n)) (n : ℕ) :
    Continuous (fun p => tailFractionLimit (ε p) (hε p) n) := by
  have hFinite (k : ℕ) (n : ℕ) : Continuous (fun p => tailFractionTrunc (ε p) k n) := by
    induction k generalizing n with
    | zero => exact continuous_const
    | succ k ih =>
      change Continuous (fun p => (tailFractionStep (ε p))^[k + 1] (fun _ => 1) n)
      simp only [Function.iterate_succ_apply', tailFractionStep]
      apply (continuous_const.sub ((hcont (n + 1)).mul (ih (n + 1)))).inv₀
      intro p
      have h := tailFraction_den_bounds (hε p (n + 1))
        (tailFraction_iterate_mem (hε p) (fun _ => ⟨le_rfl, by norm_num⟩) k (n + 1))
      exact ((by norm_num : (0 : ℝ) < 3 / 4).trans_le h.1).ne'
  have hunif : TendstoUniformly (fun k p => tailFractionTrunc (ε p) k n)
      (fun p => tailFractionLimit (ε p) (hε p) n) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro δ hδ
    have hp : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    filter_upwards [hp.eventually (gt_mem_nhds hδ)] with k hk p
    rw [Real.dist_eq]
    exact (tailFractionLimit_error (ε p) (hε p) k n).trans_lt hk
  exact hunif.continuous (Eventually.of_forall (fun k => hFinite k n)).frequently

end ContinuousFlexibility.Radial
