module

public import ContinuousFlexibility.Analysis.ProjectiveNewtonRecurrence

/-!
# A fixed smoothing scale and the scalar Newton budget

The discrete smoothing indices grow by a factor of three halves up to the
rounding error. A single induction propagates the low residual decay and
the allowed growth of the high state.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology BigOperators

/-- The ceiling of three halves of the preceding smoothing index. -/
def newtonSmoothingIndex (N₀ : ℕ) : ℕ → ℕ
  | 0 => N₀
  | n + 1 => (3 * newtonSmoothingIndex N₀ n + 1) / 2

theorem newtonSmoothingIndex_succ_bounds (N₀ n : ℕ) :
    (3 / 2 : ℝ) * newtonSmoothingIndex N₀ n ≤ newtonSmoothingIndex N₀ (n + 1) ∧
      (newtonSmoothingIndex N₀ (n + 1) : ℝ) ≤
        (3 / 2 : ℝ) * newtonSmoothingIndex N₀ n + 1 := by
  let N := newtonSmoothingIndex N₀ n
  let M := newtonSmoothingIndex N₀ (n + 1)
  have he : M = (3 * N + 1) / 2 := rfl
  have hlo : 3 * N ≤ 2 * M := by omega
  have hhi : 2 * M ≤ 3 * N + 1 := by omega
  have hlo' : 3 * (N : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hlo
  have hhi' : 2 * (M : ℝ) ≤ 3 * (N : ℝ) + 1 := by exact_mod_cast hhi
  change (3 / 2 : ℝ) * N ≤ M ∧ (M : ℝ) ≤ (3 / 2 : ℝ) * N + 1
  constructor
  · linarith only [hlo']
  · linarith only [hhi']

theorem newtonSmoothingIndex_ge_add {N₀ : ℕ} (hN₀ : 0 < N₀) (n : ℕ) :
    N₀ + n ≤ newtonSmoothingIndex N₀ n := by
  induction n with
  | zero => simp [newtonSmoothingIndex]
  | succ n ih =>
      change N₀ + (n + 1) ≤ (3 * newtonSmoothingIndex N₀ n + 1) / 2
      omega

/-- The chosen high grade leaves one full unit of decay after rounding. -/
theorem newton_budget_rate_identities (l σ : ℕ) :
    let h := 20 * l + 15 * σ + 8
    let α : ℝ := 4 * (l : ℝ) + 4 * (σ : ℝ) + 2
    let γ : ℝ := 12 * (l : ℝ) + 8 * (σ : ℝ) + 4
    let β : ℝ := (h : ℝ) - 2 * (l : ℝ) - σ
    let A : ℝ := 2 * (l : ℝ) + 2 * (σ : ℝ)
    let G : ℝ := (h : ℝ) + 2 * (l : ℝ) + σ
    G - α = (3 / 2 : ℝ) * γ ∧
      2 * α - A = (3 / 2 : ℝ) * α + 1 ∧
      β - γ = (3 / 2 : ℝ) * α + 1 := by
  dsimp only
  push_cast
  exact ⟨by ring, by ring, by ring⟩

private theorem newton_high_budget_step
    {N Nnext : ℕ} {x xnext r α γ G K M ρ : ℝ}
    (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hG : G - α = (3 / 2 : ℝ) * γ)
    (hscale : (3 / 2 : ℝ) * N ≤ Nnext)
    (hspace : Real.exp (-(γ / 2) * N) ≤ 1 / 2)
    (hcoef : K * ρ ≤ M / 2)
    (hx : x ≤ M * Real.exp (γ * N))
    (hr : r ≤ ρ * Real.exp (-α * N))
    (hstep : xnext ≤ x + K * Real.exp (G * N) * r) :
    xnext ≤ M * Real.exp (γ * Nnext) := by
  have he₁ : Real.exp (γ * N) = Real.exp (-(γ / 2) * N) *
      Real.exp ((3 / 2 : ℝ) * γ * N) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he₂ : Real.exp (G * N) * Real.exp (-α * N) =
      Real.exp ((3 / 2 : ℝ) * γ * N) := by
    rw [← Real.exp_add, show G * N + -α * N = (G - α) * N by ring, hG]
  have hcorr : K * Real.exp (G * N) * (ρ * Real.exp (-α * N)) =
      K * ρ * Real.exp ((3 / 2 : ℝ) * γ * N) := by
    calc
      _ = K * ρ * (Real.exp (G * N) * Real.exp (-α * N)) := by ring
      _ = _ := by rw [he₂]
  have hsize : M * Real.exp (-(γ / 2) * N) + K * ρ ≤ M := by
    have hM' := mul_le_mul_of_nonneg_left hspace hM
    linarith only [hcoef, hM']
  have hexp : Real.exp ((3 / 2 : ℝ) * γ * N) ≤ Real.exp (γ * Nnext) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = γ * ((3 / 2 : ℝ) * N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale hγ
  calc
    xnext ≤ M * Real.exp (γ * N) + K * Real.exp (G * N) * (ρ * Real.exp (-α * N)) :=
      hstep.trans (add_le_add hx
        (mul_le_mul_of_nonneg_left hr (mul_nonneg hK (Real.exp_pos _).le)))
    _ = (M * Real.exp (-(γ / 2) * N) + K * ρ) * Real.exp ((3 / 2 : ℝ) * γ * N) := by
      rw [he₁, hcorr]
      ring
    _ ≤ M * Real.exp ((3 / 2 : ℝ) * γ * N) :=
      mul_le_mul_of_nonneg_right hsize (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hM

private theorem newton_residual_bound_at_rate
    {N : ℕ} {x r rnext α γ A β C M ρ δ : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hr₀ : 0 ≤ r)
    (hA : δ ≤ 2 * α - A) (hβ : δ ≤ β - γ)
    (hx : x ≤ M * Real.exp (γ * N))
    (hr : r ≤ ρ * Real.exp (-α * N))
    (hstep : rnext ≤ C * (Real.exp (A * N) * r ^ 2 + Real.exp (-β * N) * x)) :
    rnext ≤ C * (ρ ^ 2 + M) * Real.exp (-δ * N) := by
  have he₁ : Real.exp (A * N) * Real.exp (-α * N) * Real.exp (-α * N) ≤
      Real.exp (-δ * N) := by
    rw [← Real.exp_add, ← Real.exp_add,
      show A * N + -α * N + -α * N = -(2 * α - A) * N by ring]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hA) (Nat.cast_nonneg N))
  have he₂ : Real.exp (-β * N) * Real.exp (γ * N) ≤ Real.exp (-δ * N) := by
    rw [← Real.exp_add, show -β * N + γ * N = -(β - γ) * N by ring]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hβ) (Nat.cast_nonneg N))
  have hquad : Real.exp (A * N) * r ^ 2 ≤ ρ ^ 2 * Real.exp (-δ * N) := by
    calc
      _ ≤ Real.exp (A * N) * (ρ * Real.exp (-α * N)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr₀ hr 2) (Real.exp_pos _).le
      _ = ρ ^ 2 * (Real.exp (A * N) * Real.exp (-α * N) * Real.exp (-α * N)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he₁ (sq_nonneg _)
  have htail : Real.exp (-β * N) * x ≤ M * Real.exp (-δ * N) := by
    calc
      _ ≤ Real.exp (-β * N) * (M * Real.exp (γ * N)) :=
        mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
      _ = M * (Real.exp (-β * N) * Real.exp (γ * N)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he₂ hM
  calc
    _ ≤ C * (ρ ^ 2 * Real.exp (-δ * N) + M * Real.exp (-δ * N)) :=
      hstep.trans (mul_le_mul_of_nonneg_left (add_le_add hquad htail) hC)
    _ = _ := by ring

private theorem newton_residual_budget_step
    {N Nnext : ℕ} {x r rnext α γ A β C M ρ : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ C) (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hr₀ : 0 ≤ r)
    (hA : 2 * α - A = (3 / 2 : ℝ) * α + 1)
    (hβ : β - γ = (3 / 2 : ℝ) * α + 1)
    (hscale : (Nnext : ℝ) ≤ (3 / 2 : ℝ) * N + 1)
    (hspace : C * (ρ ^ 2 + M) * Real.exp (α - N) ≤ ρ)
    (hx : x ≤ M * Real.exp (γ * N))
    (hr : r ≤ ρ * Real.exp (-α * N))
    (hstep : rnext ≤ C * (Real.exp (A * N) * r ^ 2 + Real.exp (-β * N) * x)) :
    rnext ≤ ρ * Real.exp (-α * Nnext) := by
  let δ : ℝ := (3 / 2 : ℝ) * α + 1
  have hres : rnext ≤ C * (ρ ^ 2 + M) * Real.exp (-δ * N) :=
    newton_residual_bound_at_rate hC hM hr₀ hA.ge hβ.ge hx hr hstep
  have he₃ : Real.exp (-δ * N) =
      Real.exp (α - N) * Real.exp (-α * ((3 / 2 : ℝ) * N + 1)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [δ]
    ring
  have hexp : Real.exp (-α * ((3 / 2 : ℝ) * N + 1)) ≤ Real.exp (-α * Nnext) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hscale (neg_nonpos.mpr hα))
  calc
    _ ≤ C * (ρ ^ 2 + M) * Real.exp (-δ * N) := hres
    _ = (C * (ρ ^ 2 + M) * Real.exp (α - N)) *
        Real.exp (-α * ((3 / 2 : ℝ) * N + 1)) := by
      rw [he₃]
      ring
    _ ≤ ρ * Real.exp (-α * ((3 / 2 : ℝ) * N + 1)) :=
      mul_le_mul_of_nonneg_right hspace (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hρ

private theorem exp_neg_le_half {t : ℝ} (ht : 1 ≤ t) : Real.exp (-t) ≤ 1 / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by norm_num
      _ ≤ _ := Real.add_one_le_exp 1
  have hcancel : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hhalf := mul_le_mul_of_nonneg_left htwo (Real.exp_pos (-1)).le
  rw [hcancel] at hhalf
  exact (Real.exp_le_exp.mpr (neg_le_neg ht)).trans (by linarith only [hhalf])

/-- Propagate both scalar budgets using the finite prefix of already controlled
steps. The recurrence can use that prefix to justify its domain conditions. -/
theorem newton_budget_induction
    (l σ N₀ : ℕ) (hN₀ : 0 < N₀) (r x : ℕ → ℝ)
    (C K M ρ : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hcoef : K * ρ ≤ M / 2) (hr₀ : ∀ n, 0 ≤ r n) :
    let N := newtonSmoothingIndex N₀
    let h := 20 * l + 15 * σ + 8
    let α : ℝ := 4 * (l : ℝ) + 4 * (σ : ℝ) + 2
    let γ : ℝ := 12 * (l : ℝ) + 8 * (σ : ℝ) + 4
    let β : ℝ := (h : ℝ) - 2 * (l : ℝ) - σ
    let A : ℝ := 2 * (l : ℝ) + 2 * (σ : ℝ)
    let G : ℝ := (h : ℝ) + 2 * (l : ℝ) + σ
    C * (ρ ^ 2 + M) * Real.exp (α - N₀) ≤ ρ →
    r 0 ≤ ρ * Real.exp (-α * N₀) → x 0 ≤ M * Real.exp (γ * N₀) →
    (∀ n, (∀ k ≤ n, r k ≤ ρ * Real.exp (-α * N k) ∧ x k ≤ M * Real.exp (γ * N k)) →
      r (n + 1) ≤ C * (Real.exp (A * N n) * (r n) ^ 2 + Real.exp (-β * N n) * x n) ∧
      x (n + 1) ≤ x n + K * Real.exp (G * N n) * r n) →
    ∀ n, r n ≤ ρ * Real.exp (-α * N n) ∧ x n ≤ M * Real.exp (γ * N n) := by
  dsimp only
  intro hthreshold hrinit hxinit hstep n
  let N := newtonSmoothingIndex N₀
  let α : ℝ := 4 * (l : ℝ) + 4 * (σ : ℝ) + 2
  let γ : ℝ := 12 * (l : ℝ) + 8 * (σ : ℝ) + 4
  obtain ⟨hG, hA, hβ⟩ := newton_budget_rate_identities l σ
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hγhalf : 1 ≤ γ / 2 := by
    dsimp only [γ]
    linarith only [show (0 : ℝ) ≤ l from Nat.cast_nonneg l,
      show (0 : ℝ) ≤ σ from Nat.cast_nonneg σ]
  have hγ : 0 ≤ γ := by linarith only [hγhalf]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨hrinit, hxinit⟩
    | succ n =>
      have hpref (k : ℕ) (hk : k ≤ n) := ih k (Nat.lt_succ_of_le hk)
      obtain ⟨hr, hx⟩ := hpref n le_rfl
      obtain ⟨hrstep, hxstep⟩ := hstep n hpref
      obtain ⟨hscale₁, hscale₂⟩ := newtonSmoothingIndex_succ_bounds N₀ n
      have hN₀N : N₀ ≤ N n := (Nat.le_add_right N₀ n).trans (newtonSmoothingIndex_ge_add hN₀ n)
      have hN₁ : 1 ≤ N n := Nat.succ_le_iff.mpr (hN₀.trans_le hN₀N)
      have hN : (1 : ℝ) ≤ N n := by exact_mod_cast hN₁
      have hthreshold' : C * (ρ ^ 2 + M) * Real.exp (α - N n) ≤ ρ := by
        apply le_trans _ hthreshold
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (add_nonneg (sq_nonneg _) hM))
        apply Real.exp_le_exp.mpr
        linarith only [show (N₀ : ℝ) ≤ N n by exact_mod_cast hN₀N]
      have hspace : Real.exp (-(γ / 2) * N n) ≤ 1 / 2 := by
        rw [show -(γ / 2) * N n = -((γ / 2) * N n) by ring]
        exact exp_neg_le_half (by
          simpa only [one_mul] using mul_le_mul hγhalf hN zero_le_one (by linarith only [hγhalf]))
      exact ⟨newton_residual_budget_step hα hC hM hρ (hr₀ n) hA hβ hscale₂ hthreshold' hx hr hrstep,
        newton_high_budget_step hγ hK hM hG hscale₁ hspace hcoef hx hr hxstep⟩

/-- The low-grade corrections can be budgeted uniformly on every finite
prefix, including the correction used by the current step. -/
theorem newton_exponential_prefix_le
    {N₀ : ℕ} (hN₀ : 0 < N₀) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (∑ k ∈ Finset.range n, Real.exp (-δ * (newtonSmoothingIndex N₀ k : ℝ))) ≤
      Real.exp (-δ * (N₀ : ℝ)) * (1 - Real.exp (-δ))⁻¹ := by
  have h₀ : 0 ≤ Real.exp (-δ) := (Real.exp_pos _).le
  have h₁ : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hδ)
  have hsum := (summable_geometric_of_lt_one h₀ h₁).sum_le_tsum (Finset.range n)
    (fun k _ => pow_nonneg h₀ k)
  rw [tsum_geometric_of_lt_one h₀ h₁] at hsum
  have hterm (k : ℕ) : Real.exp (-δ * (newtonSmoothingIndex N₀ k : ℝ)) ≤
      Real.exp (-δ * (N₀ : ℝ)) * Real.exp (-δ) ^ k := by
    have hN : (N₀ : ℝ) + k ≤ newtonSmoothingIndex N₀ k := by
      exact_mod_cast newtonSmoothingIndex_ge_add hN₀ k
    calc
      _ ≤ Real.exp (-δ * ((N₀ : ℝ) + k)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hN (neg_nonpos.mpr hδ.le))
      _ = _ := by rw [mul_add, Real.exp_add, mul_comm (-δ) (k : ℝ), Real.exp_nat_mul]
  calc
    _ ≤ ∑ k ∈ Finset.range n, Real.exp (-δ * (N₀ : ℝ)) * Real.exp (-δ) ^ k :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ = Real.exp (-δ * (N₀ : ℝ)) * ∑ k ∈ Finset.range n, Real.exp (-δ) ^ k := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le

private theorem exp_neg_nat_tendsto_zero {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => Real.exp (-δ * (n : ℝ))) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (-δ) * (n : ℝ)) atTop atBot :=
    (Filter.tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hδ)).2
      tendsto_natCast_atTop_atTop
  exact Real.tendsto_exp_atBot.comp h

/-- One initial index gives both the residual threshold and the strict
finite-prefix correction budget. -/
theorem exists_newton_starting_index
    (C K M α ρ δ ε : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ C * (ρ ^ 2 + M) * Real.exp (α - N₀) ≤ ρ ∧
      K * ρ * Real.exp (-δ * (N₀ : ℝ)) * (1 - Real.exp (-δ))⁻¹ < ε := by
  have h₁ : Tendsto (fun n : ℕ => C * (ρ ^ 2 + M) * Real.exp (α - n)) atTop (𝓝 0) := by
    have he : (fun n : ℕ => C * (ρ ^ 2 + M) * Real.exp (α - n)) =
        (fun n : ℕ => (C * (ρ ^ 2 + M) * Real.exp α) * Real.exp (-(1 : ℝ) * (n : ℝ))) := by
      funext n
      rw [sub_eq_add_neg, Real.exp_add, neg_one_mul]
      ring
    rw [he]
    simpa only [mul_zero] using
      (exp_neg_nat_tendsto_zero (by norm_num : (0 : ℝ) < 1)).const_mul
        (C * (ρ ^ 2 + M) * Real.exp α)
  have h₂ : Tendsto (fun n : ℕ =>
      K * ρ * Real.exp (-δ * (n : ℝ)) * (1 - Real.exp (-δ))⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (((exp_neg_nat_tendsto_zero hδ).const_mul (K * ρ)).mul_const (1 - Real.exp (-δ))⁻¹)
  obtain ⟨N₀, hN₀, hres, hprefix⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and
      ((h₁.eventually_lt_const hρ).and (h₂.eventually_lt_const hε))).exists
  exact ⟨N₀, hN₀, hres.le, hprefix⟩

/-- A higher finite grade can supply the tail rate needed for the next
decay improvement while the smoothing indices stay fixed. -/
theorem exists_newton_high_grade_for_rate (l σ : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    ∃ h : ℕ, 2 * l ≤ h ∧
      let γ : ℝ := ((h : ℝ) + 2 * (l : ℝ) + σ - α) / (3 / 2)
      2 ≤ γ ∧ (h : ℝ) + 2 * (l : ℝ) + σ - α = (3 / 2 : ℝ) * γ ∧
        2 * α - (2 * (l : ℝ) + 2 * (σ : ℝ)) + 1 ≤ (h : ℝ) - 2 * (l : ℝ) - σ - γ := by
  obtain ⟨h, hh⟩ := exists_nat_ge (4 * α + 4 * (l : ℝ) + 3)
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hσ : (0 : ℝ) ≤ σ := Nat.cast_nonneg σ
  have hgrade' : 2 * (l : ℝ) ≤ h := by linarith only [hh, hα, hl]
  have hgrade : 2 * l ≤ h := by exact_mod_cast hgrade'
  refine ⟨h, hgrade, ?_⟩
  dsimp only
  exact ⟨by linarith only [hh, hα, hl, hσ], by ring, by linarith only [hh, hσ]⟩

/-- One recurrence step improves the decay exponent. Its numerical
constant may grow, including the contribution from the rounding error. -/
theorem newton_residual_rate_improvement
    {N Nnext : ℕ} {x r rnext α γ A β C M ρ : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hr₀ : 0 ≤ r)
    (hA : 0 ≤ 2 * α - A) (hβ : 2 * α - A ≤ β - γ)
    (hscale : (Nnext : ℝ) ≤ (3 / 2 : ℝ) * N + 1)
    (hx : x ≤ M * Real.exp (γ * N))
    (hr : r ≤ ρ * Real.exp (-α * N))
    (hstep : rnext ≤ C * (Real.exp (A * N) * r ^ 2 + Real.exp (-β * N) * x)) :
    let α' := (2 * α - A) / (3 / 2)
    rnext ≤ C * (ρ ^ 2 + M) * Real.exp α' * Real.exp (-α' * Nnext) := by
  let α' := (2 * α - A) / (3 / 2)
  have hα' : 0 ≤ α' := div_nonneg hA (by norm_num)
  have he : (3 / 2 : ℝ) * α' = 2 * α - A := by dsimp only [α']; ring
  have hexp : Real.exp (-(2 * α - A) * N) ≤ Real.exp α' * Real.exp (-α' * Nnext) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hprod := mul_le_mul_of_nonneg_left hscale hα'
    calc
      _ = -α' * ((3 / 2 : ℝ) * N) := by rw [← he]; ring
      _ ≤ _ := by linarith only [hprod]
  calc
    _ ≤ C * (ρ ^ 2 + M) * Real.exp (-(2 * α - A) * N) :=
      newton_residual_bound_at_rate hC hM hr₀ le_rfl hβ hx hr hstep
    _ ≤ C * (ρ ^ 2 + M) * (Real.exp α' * Real.exp (-α' * Nnext)) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hC (add_nonneg (sq_nonneg _) hM))
    _ = _ := by ring

/-- The closed form of the successive improvements from the first rate. -/
def newtonImprovedRate (A α : ℝ) (m : ℕ) : ℝ :=
  2 * A + (4 / 3 : ℝ) ^ m * (α - 2 * A)

theorem newtonImprovedRate_zero (A α : ℝ) : newtonImprovedRate A α 0 = α := by
  simp only [newtonImprovedRate, pow_zero, one_mul]
  ring

theorem newtonImprovedRate_succ (A α : ℝ) (m : ℕ) :
    newtonImprovedRate A α (m + 1) = (2 * newtonImprovedRate A α m - A) / (3 / 2) := by
  simp only [newtonImprovedRate, pow_succ]
  ring

theorem tendsto_newtonImprovedRate_atTop {A α : ℝ} (hα : 2 * A < α) :
    Tendsto (newtonImprovedRate A α) atTop atTop := by
  exact tendsto_atTop_add_const_left _ _ <|
    Tendsto.atTop_mul_const (sub_pos.mpr hα) (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

end ContinuousFlexibility.Analysis
