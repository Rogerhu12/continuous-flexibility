import ContinuousFlexibility.Radial.TridiagonalDominance
import ContinuousFlexibility.Radial.TailNodeUniqueness
import ContinuousFlexibility.Radial.TailNodeProducts
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Coordinate Green kernels of the tail Jacobi inverse

The inverse on the mass-normalized `ℓ²` space has an actual coordinate kernel.
Symmetry follows from the symmetric tridiagonal operator, and the operator norm
controls every kernel entry. Away from the source, each column satisfies the
homogeneous three-term recurrence. These are the operator facts needed to
identify a Green column with the natural node line.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped InnerProductSpace

/-- The upper and lower weighted shifts are adjoint to one another. -/
theorem tail_inner_upOp {γ : ℕ → ℝ} {M : ℝ} (hγ : ∀ n, |γ n| ≤ M)
    (x y : Ell2) : ⟪upOp γ x, y⟫_ℝ = ⟪x, downOp γ y⟫_ℝ := by
  have hs : Summable (fun n => ⟪x n, downOp γ y n⟫_ℝ) :=
    lp.summable_inner x (downOp γ y)
  have hsplit := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, downOp_apply_zero hγ, inner_zero_right,
    zero_add] at hsplit
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  calc
    (∑' n, ⟪upOp γ x n, y n⟫_ℝ) =
        ∑' n, ⟪x (n + 1), downOp γ y (n + 1)⟫_ℝ := by
      apply tsum_congr
      intro n
      rw [upOp_apply hγ, downOp_apply_succ hγ]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = _ := hsplit

theorem tail_inner_downOp {γ : ℕ → ℝ} {M : ℝ} (hγ : ∀ n, |γ n| ≤ M)
    (x y : Ell2) : ⟪downOp γ x, y⟫_ℝ = ⟪x, upOp γ y⟫_ℝ := by
  calc
    ⟪downOp γ x, y⟫_ℝ = ⟪y, downOp γ x⟫_ℝ := real_inner_comm _ _
    _ = ⟪upOp γ y, x⟫_ℝ := (tail_inner_upOp hγ y x).symm
    _ = ⟪x, upOp γ y⟫_ℝ := real_inner_comm _ _

theorem tail_diagOp_isSymmetric {β : ℕ → ℝ} {M : ℝ}
    (hβ : ∀ n, |β n| ≤ M) : (diagOp β).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪diagOp β x, y⟫_ℝ = ⟪x, diagOp β y⟫_ℝ
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [diagOp_apply hβ, diagOp_apply hβ]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- Bounded real Jacobi coefficients define a symmetric operator. -/
theorem tail_jacobiOp_isSymmetric {β γ : ℕ → ℝ} {M N : ℝ}
    (hβ : ∀ n, |β n| ≤ M) (hγ : ∀ n, |γ n| ≤ N) :
    (jacobiOp β γ).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪diagOp β x + upOp γ x + downOp γ x, y⟫_ℝ =
    ⟪x, diagOp β y + upOp γ y + downOp γ y⟫_ℝ
  simp only [inner_add_left, inner_add_right]
  rw [(tail_diagOp_isSymmetric hβ) x y, tail_inner_upOp hγ, tail_inner_downOp hγ]
  ring

/-- A right inverse of a symmetric Jacobi operator is symmetric. -/
theorem tail_jacobiInverse_isSymmetric {β γ : ℕ → ℝ} {M N : ℝ}
    (hβ : ∀ n, |β n| ≤ M) (hγ : ∀ n, |γ n| ≤ N)
    (G : Ell2 →L[ℝ] Ell2) (hG : ∀ x, jacobiOp β γ (G x) = x) :
    G.toLinearMap.IsSymmetric := by
  intro x y
  have h := (tail_jacobiOp_isSymmetric hβ hγ) (G x) (G y)
  change ⟪jacobiOp β γ (G x), G y⟫_ℝ = ⟪G x, jacobiOp β γ (G y)⟫_ℝ at h
  rw [hG, hG] at h
  exact h.symm

/-- The first index is the source and the second is the evaluation node. -/
def tailNodeGreen (G : Ell2 →L[ℝ] Ell2) (m n : ℕ) : ℝ :=
  G (lp.single 2 m 1) n

theorem tailNodeGreen_symm (G : Ell2 →L[ℝ] Ell2)
    (hG : G.toLinearMap.IsSymmetric) (m n : ℕ) :
    tailNodeGreen G m n = tailNodeGreen G n m := by
  have h := hG (lp.single 2 m 1) (lp.single 2 n 1)
  change ⟪G (lp.single 2 m 1), lp.single 2 n 1⟫_ℝ =
    ⟪lp.single 2 m 1, G (lp.single 2 n 1)⟫_ℝ at h
  simpa only [lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply,
    conj_trivial, mul_one, one_mul, tailNodeGreen] using h

/-- Every coordinate of a Green column is bounded by the inverse norm. -/
theorem abs_tailNodeGreen_le (G : Ell2 →L[ℝ] Ell2) (m n : ℕ) :
    |tailNodeGreen G m n| ≤ ‖G‖ := by
  calc
    |tailNodeGreen G m n| = ‖G (lp.single 2 m 1) n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖G (lp.single 2 m 1)‖ := lp.norm_apply_le_norm (by norm_num) _ n
    _ ≤ ‖G‖ * ‖(lp.single 2 m 1 : Ell2)‖ := G.le_opNorm _
    _ = ‖G‖ := by rw [lp.norm_single (by norm_num), norm_one, mul_one]

theorem tailNodeGreen_sq_summable (G : Ell2 →L[ℝ] Ell2) (m : ℕ) :
    Summable (fun n => ‖tailNodeGreen G m n‖ ^ 2) :=
  sq_summable (G (lp.single 2 m 1))

/-- The coordinate kernel represents the actual bounded operator, with
convergence of the series for every square-summable source. -/
theorem hasSum_tailNodeGreen (G : Ell2 →L[ℝ] Ell2) (x : Ell2) (n : ℕ) :
    HasSum (fun m => tailNodeGreen G m n * x m) (G x n) := by
  have h := (lp.hasSum_single (by norm_num) x).mapL
    ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).comp G)
  change HasSum (fun m => G (lp.single 2 m (x m)) n) (G x n) at h
  convert h using 1
  funext m
  have hs : (lp.single 2 m (x m) : Ell2) = x m • lp.single 2 m 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : ℕ => ℝ) 2 m (x m) (1 : ℝ))
  rw [hs, map_smul]
  change tailNodeGreen G m n * x m = x m * tailNodeGreen G m n
  ring

theorem tailNodeGreen_apply_eq_tsum (G : Ell2 →L[ℝ] Ell2) (x : Ell2) (n : ℕ) :
    G x n = ∑' m, tailNodeGreen G m n * x m :=
  (hasSum_tailNodeGreen G x n).tsum_eq.symm

theorem tail_jacobiOp_apply_zero {β γ : ℕ → ℝ} {M N : ℝ}
    (hβ : ∀ n, |β n| ≤ M) (hγ : ∀ n, |γ n| ≤ N) (x : Ell2) :
    jacobiOp β γ x 0 = β 0 * x 0 + γ 0 * x 1 := by
  change diagOp β x 0 + upOp γ x 0 + downOp γ x 0 = _
  rw [diagOp_apply hβ, upOp_apply hγ, downOp_apply_zero hγ, add_zero]

theorem tail_jacobiOp_apply_succ {β γ : ℕ → ℝ} {M N : ℝ}
    (hβ : ∀ n, |β n| ≤ M) (hγ : ∀ n, |γ n| ≤ N) (x : Ell2) (n : ℕ) :
    jacobiOp β γ x (n + 1) = β (n + 1) * x (n + 1) +
      γ (n + 1) * x (n + 2) + γ n * x n := by
  change diagOp β x (n + 1) + upOp γ x (n + 1) + downOp γ x (n + 1) = _
  rw [diagOp_apply hβ, upOp_apply hγ, downOp_apply_succ hγ]

/-- The column equation includes the Kronecker source at every node. -/
theorem tailNodeGreen_equation {β γ : ℕ → ℝ} {M N : ℝ}
    (hβ : ∀ n, |β n| ≤ M) (hγ : ∀ n, |γ n| ≤ N)
    (G : Ell2 →L[ℝ] Ell2) (hG : ∀ x, jacobiOp β γ (G x) = x) (m n : ℕ) :
    β (n + 1) * tailNodeGreen G m (n + 1) +
      γ (n + 1) * tailNodeGreen G m (n + 2) +
      γ n * tailNodeGreen G m n = if n + 1 = m then 1 else 0 := by
  have h := congrArg (fun x : Ell2 => x (n + 1)) (hG (lp.single 2 m 1))
  rw [tail_jacobiOp_apply_succ hβ hγ] at h
  by_cases hnm : n + 1 = m
  · subst m
    simpa only [tailNodeGreen, lp.single_apply_self, if_pos rfl] using h
  · rw [lp.single_apply_ne 2 m 1 hnm] at h
    simpa only [tailNodeGreen, if_neg hnm] using h

theorem tailNodeGreen_equation_zero {β γ : ℕ → ℝ} {M N : ℝ}
    (hβ : ∀ n, |β n| ≤ M) (hγ : ∀ n, |γ n| ≤ N)
    (G : Ell2 →L[ℝ] Ell2) (hG : ∀ x, jacobiOp β γ (G x) = x) (m : ℕ) :
    β 0 * tailNodeGreen G m 0 + γ 0 * tailNodeGreen G m 1 =
      if 0 = m then 1 else 0 := by
  have h := congrArg (fun x : Ell2 => x 0) (hG (lp.single 2 m 1))
  rw [tail_jacobiOp_apply_zero hβ hγ] at h
  by_cases hm : 0 = m
  · subst m
    simpa only [tailNodeGreen, lp.single_apply_self, if_pos rfl] using h
  · rw [lp.single_apply_ne 2 m 1 hm] at h
    simpa only [tailNodeGreen, if_neg hm] using h

/-- Off the source, a Green column is a homogeneous node solution with
positive-coupling sign convention `c = -γ`. -/
theorem tailNodeGreen_recurrence {β γ : ℕ → ℝ} {M N : ℝ}
    (hβ : ∀ n, |β n| ≤ M) (hγ : ∀ n, |γ n| ≤ N)
    (G : Ell2 →L[ℝ] Ell2) (hG : ∀ x, jacobiOp β γ (G x) = x)
    {m n : ℕ} (hn : n + 1 ≠ m) :
    β (n + 1) * tailNodeGreen G m (n + 1) =
      (-γ n) * tailNodeGreen G m n +
        (-γ (n + 1)) * tailNodeGreen G m (n + 2) := by
  have h := tailNodeGreen_equation hβ hγ G hG m n
  rw [if_neg hn] at h
  linarith

/-- A square-summable nonvanishing natural line determines every inverse
column to the right of its source. No positivity assertion about the inverse
is needed for this factorization. -/
theorem tailNodeGreen_factorization {β γ y : ℕ → ℝ} {M N : ℝ}
    (hβ : ∀ n, |β n| ≤ M) (hγ : ∀ n, |γ n| ≤ N)
    (G : Ell2 →L[ℝ] Ell2) (hG : ∀ x, jacobiOp β γ (G x) = x) (m : ℕ)
    (hγne : ∀ n, m ≤ n → γ n ≠ 0)
    (hyrec : ∀ n, m ≤ n → β (n + 1) * y (n + 1) =
      (-γ n) * y n + (-γ (n + 1)) * y (n + 2))
    (hyne : ∀ n, m ≤ n → y n ≠ 0)
    (hy : Summable (fun n => y n ^ 2)) {n : ℕ} (hmn : m ≤ n) :
    tailNodeGreen G m n = tailNodeGreen G m m * (y n / y m) := by
  have hz : Summable (fun k => (1 : ℝ) * tailNodeGreen G m k ^ 2) := by
    simpa only [one_mul, Real.norm_eq_abs, sq_abs] using tailNodeGreen_sq_summable G m
  have hy' : Summable (fun k => (1 : ℝ) * y k ^ 2) := by
    simpa only [one_mul] using hy
  have h := tailNodeLine_eq_mul_from_of_summable
    (b := β) (c := fun k => -γ k) (μ := fun _ => 1)
    (y := y) (z := tailNodeGreen G m) m (fun _ => zero_lt_one)
    (fun k hk => neg_ne_zero.mpr (hγne k hk))
    ⟨N, fun k _ => by simpa only [abs_neg, Real.sqrt_one, one_mul, mul_one] using hγ k⟩
    hyrec (fun k hk => tailNodeGreen_recurrence hβ hγ G hG (by omega)) hyne hy' hz n hmn
  calc
    tailNodeGreen G m n = (tailNodeGreen G m m / y m) * y n := h
    _ = tailNodeGreen G m m * (y n / y m) := by ring

/-- Undo the mass-square-root normalization in both kernel variables. -/
def tailMassNodeGreen (μ : ℕ → ℝ) (G : Ell2 →L[ℝ] Ell2) (m n : ℕ) : ℝ :=
  tailNodeGreen G m n / (Real.sqrt (μ m) * Real.sqrt (μ n))

theorem tailMassNodeGreen_symm (μ : ℕ → ℝ) (G : Ell2 →L[ℝ] Ell2)
    (hG : G.toLinearMap.IsSymmetric) (m n : ℕ) :
    tailMassNodeGreen μ G m n = tailMassNodeGreen μ G n m := by
  rw [tailMassNodeGreen, tailMassNodeGreen, tailNodeGreen_symm G hG m n,
    mul_comm (Real.sqrt (μ m))]

/-- The diagonal Green bound has the physical factor `μ m` in its denominator. -/
theorem abs_tailMassNodeGreen_diag_le {μ : ℕ → ℝ} (hμ : ∀ n, 0 < μ n)
    (G : Ell2 →L[ℝ] Ell2) {B : ℝ} (hG : ‖G‖ ≤ B) (m : ℕ) :
    |tailMassNodeGreen μ G m m| ≤ B / μ m := by
  rw [tailMassNodeGreen, Real.mul_self_sqrt (hμ m).le, abs_div, abs_of_pos (hμ m)]
  exact (div_le_div_iff_of_pos_right (hμ m)).mpr ((abs_tailNodeGreen_le G m m).trans hG)

/-- In physical node coordinates the normalization cancels, leaving the
ratio of the actual natural line. -/
theorem tailMassNodeGreen_factorization {β γ μ y : ℕ → ℝ} {M N : ℝ}
    (hβ : ∀ n, |β n| ≤ M) (hγ : ∀ n, |γ n| ≤ N) (hμ : ∀ n, 0 < μ n)
    (G : Ell2 →L[ℝ] Ell2) (hG : ∀ x, jacobiOp β γ (G x) = x) (m : ℕ)
    (hγne : ∀ n, m ≤ n → γ n ≠ 0)
    (hyrec : ∀ n, m ≤ n →
      β (n + 1) * (Real.sqrt (μ (n + 1)) * y (n + 1)) =
        (-γ n) * (Real.sqrt (μ n) * y n) +
        (-γ (n + 1)) * (Real.sqrt (μ (n + 2)) * y (n + 2)))
    (hyne : ∀ n, m ≤ n → y n ≠ 0)
    (hy : Summable (fun n => μ n * y n ^ 2)) {n : ℕ} (hmn : m ≤ n) :
    tailMassNodeGreen μ G m n = tailMassNodeGreen μ G m m * (y n / y m) := by
  have hY : Summable (fun k => (Real.sqrt (μ k) * y k) ^ 2) := by
    convert hy using 1
    funext k
    rw [mul_pow, Real.sq_sqrt (hμ k).le]
  have hfactor := tailNodeGreen_factorization hβ hγ G hG m hγne hyrec
    (fun k hk => mul_ne_zero (Real.sqrt_pos.mpr (hμ k)).ne' (hyne k hk)) hY hmn
  rw [tailMassNodeGreen, tailMassNodeGreen, hfactor]
  field_simp [(Real.sqrt_pos.mpr (hμ m)).ne', (Real.sqrt_pos.mpr (hμ n)).ne',
    hyne m le_rfl] <;> ring

/-- The mass-normalized inverse norm and one-step natural-line decay imply
the full right-column product estimate. -/
theorem abs_tailMassNodeGreen_le_prod {β γ μ y r : ℕ → ℝ} {M N B : ℝ}
    (hβ : ∀ n, |β n| ≤ M) (hγ : ∀ n, |γ n| ≤ N) (hμ : ∀ n, 0 < μ n)
    (G : Ell2 →L[ℝ] Ell2) (hG : ∀ x, jacobiOp β γ (G x) = x)
    (hGb : ‖G‖ ≤ B) (hγne : ∀ n, γ n ≠ 0)
    (hyrec : ∀ n, β (n + 1) * (Real.sqrt (μ (n + 1)) * y (n + 1)) =
      (-γ n) * (Real.sqrt (μ n) * y n) +
        (-γ (n + 1)) * (Real.sqrt (μ (n + 2)) * y (n + 2)))
    (hypos : ∀ n, 0 < y n) (hy : Summable (fun n => μ n * y n ^ 2))
    (hr : ∀ n, 0 ≤ r n) (hstep : ∀ n, y (n + 1) ≤ r n * y n)
    {m n : ℕ} (hmn : m ≤ n) :
    |tailMassNodeGreen μ G m n| ≤ B / μ m * ∏ k ∈ Finset.Ico m n, r k := by
  rw [tailMassNodeGreen_factorization hβ hγ hμ G hG m
    (fun k _ => hγne k) (fun k _ => hyrec k) (fun k _ => (hypos k).ne') hy hmn,
    abs_mul, abs_div, abs_of_pos (hypos n), abs_of_pos (hypos m)]
  exact mul_le_mul (abs_tailMassNodeGreen_diag_le hμ G hGb m)
    (tailNode_ratio_le_prod hypos hr hstep hmn)
    (div_nonneg (hypos n).le (hypos m).le)
    (div_nonneg ((norm_nonneg G).trans hGb) (hμ m).le)

/-- Diagonal dominance supplies the symmetric inverse used by the coordinate
kernel, with the original quantitative inverse bound. -/
theorem exists_tailNodeGreen_inverse {β γ : ℕ → ℝ} {Λ M θ : ℝ}
    (hΛ : 0 < Λ) (hθ₀ : 0 ≤ θ) (hθ : 2 * θ < 1)
    (hβ : ∀ n, Λ ≤ β n) (hβM : ∀ n, β n ≤ M)
    (hγ : ∀ n, |γ n| ≤ θ * Λ) :
    ∃ G : Ell2 →L[ℝ] Ell2,
      (∀ x, G (jacobiOp β γ x) = x) ∧
      (∀ x, jacobiOp β γ (G x) = x) ∧
      ‖G‖ ≤ 1 / (Λ * (1 - 2 * θ)) ∧ G.toLinearMap.IsSymmetric := by
  obtain ⟨G, hGl, hGr, hGb⟩ := jacobiOp_exists_inverse hΛ hθ₀ hθ hβ hβM hγ
  have hβabs : ∀ n, |β n| ≤ M := fun n => by
    rw [abs_of_pos (hΛ.trans_le (hβ n))]
    exact hβM n
  exact ⟨G, hGl, hGr, hGb, tail_jacobiInverse_isSymmetric hβabs hγ G hGr⟩

end ContinuousFlexibility.Radial
