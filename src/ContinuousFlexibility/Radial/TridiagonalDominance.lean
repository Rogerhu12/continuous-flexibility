import Mathlib.Analysis.Normed.Lp.lpSpace
import ContinuousFlexibility.Analysis.NeumannPackage

/-!
# Tridiagonal diagonal-dominance inverse on `ℓ²(ℕ)`

Abstract form of the deep-radial inverse estimate (paper §5, proof of
`lem:radial-deep-inverse`, `05-flat-end-chain.tex` lines 383-393): in the coordinates
`√μ_n a_n` the radial operator is a Jacobi (tridiagonal) matrix whose diagonal entries are `≥ Λ`
while the neighbouring entries are `≤ θ Λ` in absolute value with `2 θ < 1`.  Then the operator
is invertible on `ℓ²(ℕ)` with inverse of norm `≤ 1 / (Λ (1 - 2 θ))`, independently of the size of
the sequences (hence "independently of the number of edges").

* `Ell2` is `ℓ²(ℕ)` over `ℝ`.
* `diagOp β`, `upOp γ`, `downOp γ` are the diagonal and the two weighted shifts
  (junk value `0` for unbounded weights).
* `jacobiOp β γ = diagOp β + upOp γ + downOp γ`.
* `jacobiOp_exists_inverse` is the dominance theorem, and `jacobiOp_neg_exists_inverse` its
  version for the sign pattern `-(∑ b_n a_n² + 2 ∑ c_n a_n a_{n+1})` of the paper.
-/

noncomputable section

open scoped ENNReal

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Analysis

/-- The real Hilbert space `ℓ²(ℕ)`. -/
abbrev Ell2 : Type := lp (fun _ : ℕ => ℝ) 2

theorem sq_summable (x : Ell2) : Summable fun n => ‖x n‖ ^ 2 := by
  have h := (lp.memℓp x).summable (by simp : 0 < (2 : ℝ≥0∞).toReal)
  simpa [Real.rpow_two] using h

theorem tsum_sq_eq (x : Ell2) : ∑' n, ‖x n‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by simp : 0 < (2 : ℝ≥0∞).toReal) x
  simpa [Real.rpow_two] using h.symm

theorem mem_of_sq_summable (f : ℕ → ℝ) (h : Summable fun n => ‖f n‖ ^ 2) : Memℓp f 2 :=
  memℓp_gen (by simpa [Real.rpow_two] using h)

theorem lp_norm_le (g : Ell2) {C : ℝ} (hC : 0 ≤ C) (h : ∑' n, ‖g n‖ ^ 2 ≤ C ^ 2) :
    ‖g‖ ≤ C := by
  have h2 : ‖g‖ ^ 2 ≤ C ^ 2 := by rw [← tsum_sq_eq g]; exact h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC two_ne_zero).mp h2

theorem weighted_sq (c u : ℕ → ℝ) {M : ℝ} (hc : ∀ n, |c n| ≤ M)
    (hu : Summable fun n => ‖u n‖ ^ 2) :
    Summable (fun n => ‖c n * u n‖ ^ 2) ∧
      ∑' n, ‖c n * u n‖ ^ 2 ≤ M ^ 2 * ∑' n, ‖u n‖ ^ 2 := by
  have hle : ∀ n, ‖c n * u n‖ ^ 2 ≤ M ^ 2 * ‖u n‖ ^ 2 := by
    intro n
    have h' : |c n| ≤ M := hc n
    have h : ‖c n‖ ≤ M := by rwa [Real.norm_eq_abs]
    rw [norm_mul, mul_pow]
    gcongr
  have hs : Summable fun n => ‖c n * u n‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle (hu.mul_left _)
  refine ⟨hs, ?_⟩
  calc ∑' n, ‖c n * u n‖ ^ 2 ≤ ∑' n, M ^ 2 * ‖u n‖ ^ 2 :=
        hs.tsum_le_tsum hle (hu.mul_left _)
    _ = M ^ 2 * ∑' n, ‖u n‖ ^ 2 := tsum_mul_left

theorem shift_summable (x : Ell2) : Summable fun n => ‖x (n + 1)‖ ^ 2 :=
  (summable_nat_add_iff 1).mpr (sq_summable x)

theorem shift_tsum_le (x : Ell2) : ∑' n, ‖x (n + 1)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := (sq_summable x).sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one, tsum_sq_eq] at h
  have h0 := sq_nonneg ‖x 0‖
  linarith

theorem norm_le_of_coord (T : Ell2 →L[ℝ] Ell2) (f : Ell2 → ℕ → ℝ)
    (hT : ∀ x n, T x n = f x n) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ∑' n, ‖f x n‖ ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2) : ‖T‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
  refine lp_norm_le _ (by positivity) ?_
  have h : ∑' n, ‖T x n‖ ^ 2 = ∑' n, ‖f x n‖ ^ 2 := tsum_congr fun n => by rw [hT]
  rw [h]
  exact (hb x).trans_eq (by ring)

/-- Build a bounded operator on `ℓ²` from a coordinatewise linear formula with a square-sum
bound. -/
def mkOp (f : Ell2 → ℕ → ℝ) (hf : ∀ x, Memℓp (f x) 2)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (c : ℝ) x, f (c • x) = c • f x)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ∑' n, ‖f x n‖ ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2) :
    Ell2 →L[ℝ] Ell2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨f x, hf x⟩
      map_add' := fun x y => Subtype.ext (hadd x y)
      map_smul' := fun c x => Subtype.ext (hsmul c x) }
    M (fun x => lp_norm_le ⟨f x, hf x⟩ (by positivity) ((hb x).trans_eq (by ring)))

/-! ### The diagonal operator -/

/-- Coordinates of the diagonal operator. -/
def diagFun (β : ℕ → ℝ) (x : Ell2) : ℕ → ℝ := fun n => β n * x n

theorem diagFun_bound {β : ℕ → ℝ} {M : ℝ} (hβ : ∀ n, |β n| ≤ M) (x : Ell2) :
    Summable (fun n => ‖diagFun β x n‖ ^ 2) ∧
      ∑' n, ‖diagFun β x n‖ ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2 := by
  have h := weighted_sq β (⇑x) hβ (sq_summable x)
  exact ⟨h.1, h.2.trans_eq (congrArg (fun t => M ^ 2 * t) (tsum_sq_eq x))⟩

theorem diagFun_add (β : ℕ → ℝ) (x y : Ell2) :
    diagFun β (x + y) = diagFun β x + diagFun β y := by
  funext n
  simp [diagFun, mul_add]

theorem diagFun_smul (β : ℕ → ℝ) (c : ℝ) (x : Ell2) :
    diagFun β (c • x) = c • diagFun β x := by
  funext n
  simp [diagFun, lp.coeFn_smul]
  ring

open Classical in
/-- The diagonal operator `x ↦ (β n * x n)`; the junk value `0` is used for unbounded `β`. -/
def diagOp (β : ℕ → ℝ) : Ell2 →L[ℝ] Ell2 :=
  if h : ∃ M, ∀ n, |β n| ≤ M then
    mkOp (diagFun β) (fun x => mem_of_sq_summable _ (diagFun_bound h.choose_spec x).1)
      (diagFun_add β) (diagFun_smul β) h.choose (le_trans (abs_nonneg _) (h.choose_spec 0))
      (fun x => (diagFun_bound h.choose_spec x).2)
  else 0

theorem diagOp_apply {β : ℕ → ℝ} {M : ℝ} (hβ : ∀ n, |β n| ≤ M) (x : Ell2) (n : ℕ) :
    diagOp β x n = β n * x n := by
  have h : ∃ M, ∀ n, |β n| ≤ M := ⟨M, hβ⟩
  unfold diagOp
  split
  · rfl
  · rename_i h'
    exact absurd h h'

theorem norm_diagOp_le {β : ℕ → ℝ} {M : ℝ} (hβ : ∀ n, |β n| ≤ M) : ‖diagOp β‖ ≤ M :=
  norm_le_of_coord (diagOp β) (diagFun β) (fun x n => diagOp_apply hβ x n)
    (le_trans (abs_nonneg _) (hβ 0)) (fun x => (diagFun_bound hβ x).2)

/-! ### The shifts -/

/-- Coordinates of the upper shift `x ↦ (γ n * x (n+1))`. -/
def upFun (γ : ℕ → ℝ) (x : Ell2) : ℕ → ℝ := fun n => γ n * x (n + 1)

theorem upFun_bound {γ : ℕ → ℝ} {M : ℝ} (hγ : ∀ n, |γ n| ≤ M) (x : Ell2) :
    Summable (fun n => ‖upFun γ x n‖ ^ 2) ∧
      ∑' n, ‖upFun γ x n‖ ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2 := by
  have h := weighted_sq γ (fun n => x (n + 1)) hγ (shift_summable x)
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left (shift_tsum_le x) (sq_nonneg M))⟩

theorem upFun_add (γ : ℕ → ℝ) (x y : Ell2) :
    upFun γ (x + y) = upFun γ x + upFun γ y := by
  funext n
  simp [upFun, mul_add]

theorem upFun_smul (γ : ℕ → ℝ) (c : ℝ) (x : Ell2) :
    upFun γ (c • x) = c • upFun γ x := by
  funext n
  simp [upFun, lp.coeFn_smul]
  ring

/-- Coordinates of the lower shift `x ↦ (0, γ 0 * x 0, γ 1 * x 1, …)`. -/
def downFun (γ : ℕ → ℝ) (x : Ell2) : ℕ → ℝ
  | 0 => 0
  | n + 1 => γ n * x n

theorem downFun_bound {γ : ℕ → ℝ} {M : ℝ} (hγ : ∀ n, |γ n| ≤ M) (x : Ell2) :
    Summable (fun n => ‖downFun γ x n‖ ^ 2) ∧
      ∑' n, ‖downFun γ x n‖ ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2 := by
  have h := weighted_sq γ (⇑x) hγ (sq_summable x)
  have hs : Summable fun n => ‖downFun γ x n‖ ^ 2 := (summable_nat_add_iff 1).mp h.1
  refine ⟨hs, ?_⟩
  have h2 := hs.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at h2
  have h0 : ‖downFun γ x 0‖ ^ 2 = 0 := by simp [downFun]
  have h3 : ∑' n, ‖downFun γ x (n + 1)‖ ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2 :=
    h.2.trans_eq (congrArg (fun t => M ^ 2 * t) (tsum_sq_eq x))
  linarith

theorem downFun_add (γ : ℕ → ℝ) (x y : Ell2) :
    downFun γ (x + y) = downFun γ x + downFun γ y := by
  funext n
  cases n <;> simp [downFun, mul_add]

theorem downFun_smul (γ : ℕ → ℝ) (c : ℝ) (x : Ell2) :
    downFun γ (c • x) = c • downFun γ x := by
  funext n
  cases n <;> simp [downFun, lp.coeFn_smul]
  ring

open Classical in
/-- The weighted shift `x ↦ (γ n * x (n+1))`; junk value `0` for unbounded `γ`. -/
def upOp (γ : ℕ → ℝ) : Ell2 →L[ℝ] Ell2 :=
  if h : ∃ M, ∀ n, |γ n| ≤ M then
    mkOp (upFun γ) (fun x => mem_of_sq_summable _ (upFun_bound h.choose_spec x).1)
      (upFun_add γ) (upFun_smul γ) h.choose (le_trans (abs_nonneg _) (h.choose_spec 0))
      (fun x => (upFun_bound h.choose_spec x).2)
  else 0

open Classical in
/-- The weighted shift `x ↦ (0, γ 0 * x 0, γ 1 * x 1, …)`; junk value `0` for unbounded `γ`. -/
def downOp (γ : ℕ → ℝ) : Ell2 →L[ℝ] Ell2 :=
  if h : ∃ M, ∀ n, |γ n| ≤ M then
    mkOp (downFun γ) (fun x => mem_of_sq_summable _ (downFun_bound h.choose_spec x).1)
      (downFun_add γ) (downFun_smul γ) h.choose (le_trans (abs_nonneg _) (h.choose_spec 0))
      (fun x => (downFun_bound h.choose_spec x).2)
  else 0

theorem upOp_apply {γ : ℕ → ℝ} {M : ℝ} (hγ : ∀ n, |γ n| ≤ M) (x : Ell2) (n : ℕ) :
    upOp γ x n = γ n * x (n + 1) := by
  have h : ∃ M, ∀ n, |γ n| ≤ M := ⟨M, hγ⟩
  unfold upOp
  split
  · rfl
  · rename_i h'
    exact absurd h h'

theorem downOp_apply_zero {γ : ℕ → ℝ} {M : ℝ} (hγ : ∀ n, |γ n| ≤ M) (x : Ell2) :
    downOp γ x 0 = 0 := by
  have h : ∃ M, ∀ n, |γ n| ≤ M := ⟨M, hγ⟩
  unfold downOp
  split
  · rfl
  · rename_i h'
    exact absurd h h'

theorem downOp_apply_succ {γ : ℕ → ℝ} {M : ℝ} (hγ : ∀ n, |γ n| ≤ M) (x : Ell2) (n : ℕ) :
    downOp γ x (n + 1) = γ n * x n := by
  have h : ∃ M, ∀ n, |γ n| ≤ M := ⟨M, hγ⟩
  unfold downOp
  split
  · rfl
  · rename_i h'
    exact absurd h h'

theorem norm_upOp_le {γ : ℕ → ℝ} {M : ℝ} (hγ : ∀ n, |γ n| ≤ M) : ‖upOp γ‖ ≤ M :=
  norm_le_of_coord (upOp γ) (upFun γ) (fun x n => upOp_apply hγ x n)
    (le_trans (abs_nonneg _) (hγ 0)) (fun x => (upFun_bound hγ x).2)

theorem norm_downOp_le {γ : ℕ → ℝ} {M : ℝ} (hγ : ∀ n, |γ n| ≤ M) : ‖downOp γ‖ ≤ M := by
  refine norm_le_of_coord (downOp γ) (downFun γ) (fun x n => ?_)
    (le_trans (abs_nonneg _) (hγ 0)) (fun x => (downFun_bound hγ x).2)
  cases n with
  | zero => exact downOp_apply_zero hγ x
  | succ n => exact downOp_apply_succ hγ x n

/-! ### The Jacobi operator -/

/-- The tridiagonal (Jacobi) operator with diagonal `β` and symmetric off-diagonal entries `γ n`
between `n` and `n + 1`. -/
def jacobiOp (β γ : ℕ → ℝ) : Ell2 →L[ℝ] Ell2 := diagOp β + upOp γ + downOp γ

/-- **Diagonal dominance.**  If the diagonal entries lie in `[Λ, M]` and the neighbouring entries
are bounded by `θ Λ` with `2 θ < 1`, the Jacobi operator is invertible on `ℓ²(ℕ)` with a two-sided
inverse of norm at most `1 / (Λ (1 - 2 θ))`. -/
theorem jacobiOp_exists_inverse {β γ : ℕ → ℝ} {Λ M θ : ℝ} (hΛ : 0 < Λ) (_hθ0 : 0 ≤ θ)
    (hθ : 2 * θ < 1) (hβ : ∀ n, Λ ≤ β n) (hβM : ∀ n, β n ≤ M)
    (hγ : ∀ n, |γ n| ≤ θ * Λ) :
    ∃ G : Ell2 →L[ℝ] Ell2, (∀ x, G (jacobiOp β γ x) = x) ∧ (∀ x, jacobiOp β γ (G x) = x) ∧
      ‖G‖ ≤ 1 / (Λ * (1 - 2 * θ)) := by
  have hpos : ∀ n, 0 < β n := fun n => lt_of_lt_of_le hΛ (hβ n)
  have hbβ : ∀ n, |β n| ≤ M := fun n => by rw [abs_of_pos (hpos n)]; exact hβM n
  have hbinv : ∀ n, |(β n)⁻¹| ≤ Λ⁻¹ := fun n => by
    rw [abs_of_pos (inv_pos.mpr (hpos n))]; exact inv_anti₀ hΛ (hβ n)
  have h12 : 0 < 1 - 2 * θ := by linarith
  set D := diagOp β with hDdef
  set Di := diagOp (fun n => (β n)⁻¹) with hDidef
  set U := upOp γ with hUdef
  set L := downOp γ with hLdef
  have hD : ∀ x n, D x n = β n * x n := fun x n => diagOp_apply hbβ x n
  have hDi : ∀ x n, Di x n = (β n)⁻¹ * x n :=
    fun x n => diagOp_apply (β := fun n => (β n)⁻¹) hbinv x n
  have hDDi : ∀ x, D (Di x) = x := fun x => lp.ext (funext fun n => by
    rw [hD, hDi]; exact mul_inv_cancel_left₀ (hpos n).ne' (x n))
  have hDiD : ∀ x, Di (D x) = x := fun x => lp.ext (funext fun n => by
    rw [hDi, hD]; exact inv_mul_cancel_left₀ (hpos n).ne' (x n))
  set R : Ell2 →L[ℝ] Ell2 := Di * (U + L) with hRdef
  have hRx : ∀ x, R x = Di (U x + L x) := fun x => rfl
  have hDi_norm : ‖Di‖ ≤ Λ⁻¹ := norm_diagOp_le (β := fun n => (β n)⁻¹) hbinv
  have hU : ‖U‖ ≤ θ * Λ := norm_upOp_le hγ
  have hL : ‖L‖ ≤ θ * Λ := norm_downOp_le hγ
  have hUL : ‖U + L‖ ≤ θ * Λ + θ * Λ := (norm_add_le _ _).trans (add_le_add hU hL)
  have hRle : ‖R‖ ≤ 2 * θ := by
    calc ‖R‖ ≤ ‖Di‖ * ‖U + L‖ := norm_mul_le Di (U + L)
      _ ≤ Λ⁻¹ * (θ * Λ + θ * Λ) :=
          mul_le_mul hDi_norm hUL (norm_nonneg _) (inv_nonneg.mpr hΛ.le)
      _ = 2 * θ := by field_simp; ring
  have hR : ‖R‖ < 1 := by linarith
  have hJ : ∀ x, jacobiOp β γ x = D (x + R x) := fun x => by
    show D x + U x + L x = D (x + R x)
    rw [hRx, map_add, hDDi]
    abel
  have hN : ‖neumannInverse R hR‖ ≤ 1 / (1 - 2 * θ) :=
    (norm_neumannInverse_le R hR).trans (one_div_le_one_div_of_le h12 (by linarith))
  refine ⟨(neumannInverse R hR).comp Di, ?_, ?_, ?_⟩
  · intro x
    show neumannInverse R hR (Di (jacobiOp β γ x)) = x
    rw [hJ, hDiD]
    exact neumannInverse_apply_add R hR x
  · intro x
    rw [hJ]
    have h := neumannInverse_add_apply R hR (Di x)
    show D (neumannInverse R hR (Di x) + R (neumannInverse R hR (Di x))) = x
    rw [h]
    exact hDDi x
  · calc ‖(neumannInverse R hR).comp Di‖ ≤ ‖neumannInverse R hR‖ * ‖Di‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 / (1 - 2 * θ) * Λ⁻¹ :=
          mul_le_mul hN hDi_norm (norm_nonneg _) (one_div_pos.mpr h12).le
      _ = 1 / (Λ * (1 - 2 * θ)) := by rw [one_div, one_div, mul_inv]; ring

/-! ### The sign pattern of the paper -/

theorem diagOp_neg {β : ℕ → ℝ} {M : ℝ} (hβ : ∀ n, |β n| ≤ M) :
    diagOp (fun n => -β n) = -diagOp β := by
  have hn : ∀ n, |-β n| ≤ M := fun n => by rw [abs_neg]; exact hβ n
  have e1 : ∀ x n, diagOp (fun n => -β n) x n = -β n * x n :=
    fun x n => diagOp_apply (β := fun n => -β n) hn x n
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun n => ?_)
  rw [e1, neg_apply, lp.coeFn_neg, Pi.neg_apply, diagOp_apply hβ]
  ring

theorem upOp_neg {γ : ℕ → ℝ} {M : ℝ} (hγ : ∀ n, |γ n| ≤ M) :
    upOp (fun n => -γ n) = -upOp γ := by
  have hn : ∀ n, |-γ n| ≤ M := fun n => by rw [abs_neg]; exact hγ n
  have e1 : ∀ x n, upOp (fun n => -γ n) x n = -γ n * x (n + 1) :=
    fun x n => upOp_apply (γ := fun n => -γ n) hn x n
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun n => ?_)
  rw [e1, neg_apply, lp.coeFn_neg, Pi.neg_apply, upOp_apply hγ]
  ring

theorem downOp_neg {γ : ℕ → ℝ} {M : ℝ} (hγ : ∀ n, |γ n| ≤ M) :
    downOp (fun n => -γ n) = -downOp γ := by
  have hn : ∀ n, |-γ n| ≤ M := fun n => by rw [abs_neg]; exact hγ n
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun n => ?_)
  rw [neg_apply, lp.coeFn_neg, Pi.neg_apply]
  cases n with
  | zero =>
    rw [downOp_apply_zero (γ := fun n => -γ n) hn, downOp_apply_zero hγ]
    all_goals ring
  | succ n =>
    rw [downOp_apply_succ (γ := fun n => -γ n) hn, downOp_apply_succ hγ]
    all_goals ring

theorem jacobiOp_neg {β γ : ℕ → ℝ} {M N : ℝ} (hβ : ∀ n, |β n| ≤ M) (hγ : ∀ n, |γ n| ≤ N) :
    jacobiOp (fun n => -β n) (fun n => -γ n) = -jacobiOp β γ := by
  unfold jacobiOp
  rw [diagOp_neg hβ, upOp_neg hγ, downOp_neg hγ]
  abel

/-- The dominance theorem for the sign pattern `-(∑ b_n a_n² + 2 ∑ c_n a_n a_{n+1})`: under the
same hypotheses, `jacobiOp (-β) (-γ)` is invertible with the same norm bound. -/
theorem jacobiOp_neg_exists_inverse {β γ : ℕ → ℝ} {Λ M θ : ℝ} (hΛ : 0 < Λ) (_hθ0 : 0 ≤ θ)
    (hθ : 2 * θ < 1) (hβ : ∀ n, Λ ≤ β n) (hβM : ∀ n, β n ≤ M)
    (hγ : ∀ n, |γ n| ≤ θ * Λ) :
    ∃ G : Ell2 →L[ℝ] Ell2,
      (∀ x, G (jacobiOp (fun n => -β n) (fun n => -γ n) x) = x) ∧
      (∀ x, jacobiOp (fun n => -β n) (fun n => -γ n) (G x) = x) ∧
      ‖G‖ ≤ 1 / (Λ * (1 - 2 * θ)) := by
  obtain ⟨G, h1, h2, h3⟩ := jacobiOp_exists_inverse hΛ _hθ0 hθ hβ hβM hγ
  have hbβ : ∀ n, |β n| ≤ M := fun n => by
    rw [abs_of_pos (lt_of_lt_of_le hΛ (hβ n))]; exact hβM n
  refine ⟨-G, fun x => ?_, fun x => ?_, by rwa [norm_neg]⟩
  · rw [jacobiOp_neg hbβ hγ]
    simp [h1]
  · rw [jacobiOp_neg hbβ hγ]
    simp [h2]

end ContinuousFlexibility.Radial
