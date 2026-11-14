module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Three-lines interpolation for diagonal Hilbert scales

The analytic interpolation argument is carried out in `lp E 2` itself.
The fibers may have arbitrary dimension; in fact, the finite projection
argument only needs complex normed spaces.  The input and output spectral
projections are independent.  This permits passage to an infinite Hilbert
sum without assuming that an operator preserves a finite spectral cutoff.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ENNReal Topology
open Complex.HadamardThreeLines

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, NormedSpace ℂ (E n)]

/-- A finite spectral multiplier.  The fibers themselves need not be finite dimensional. -/
def finiteDiagonal (s : Finset ℕ) (c : ℕ → ℂ) (v : lp E 2) : lp E 2 :=
  ∑ n ∈ s, lp.single 2 n (c n • v n)

@[simp] theorem finiteDiagonal_apply (s : Finset ℕ) (c : ℕ → ℂ)
    (v : lp E 2) (n : ℕ) :
    finiteDiagonal s c v n = if n ∈ s then c n • v n else 0 := by
  classical
  simp only [finiteDiagonal, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single]

theorem finiteDiagonal_comp (s : Finset ℕ) (c d : ℕ → ℂ) (v : lp E 2) :
    finiteDiagonal s c (finiteDiagonal s d v) =
      finiteDiagonal s (fun n => c n * d n) v := by
  ext n
  by_cases hn : n ∈ s <;> simp only [finiteDiagonal_apply, hn, if_true, if_false,
    smul_smul, smul_zero]

@[simp] theorem finiteDiagonal_project (s : Finset ℕ) (c : ℕ → ℂ) (v : lp E 2) :
    finiteDiagonal s (fun _ => 1) (finiteDiagonal s c v) = finiteDiagonal s c v := by
  rw [finiteDiagonal_comp]
  simp only [one_mul]

theorem finiteDiagonal_const (s : Finset ℕ) (c : ℂ) (v : lp E 2) :
    finiteDiagonal s (fun _ => c) v = c • finiteDiagonal s (fun _ => 1) v := by
  ext n
  by_cases hn : n ∈ s <;> simp only [finiteDiagonal_apply, lp.coeFn_smul,
    Pi.smul_apply, hn, if_true, if_false, one_smul, smul_zero]

theorem finiteDiagonal_norm_mono (s : Finset ℕ) (c d : ℕ → ℂ) (v : lp E 2)
    (hcd : ∀ n ∈ s, ‖c n‖ ≤ ‖d n‖) :
    ‖finiteDiagonal s c v‖ ≤ ‖finiteDiagonal s d v‖ := by
  apply lp.norm_mono (by norm_num)
  intro n
  by_cases hn : n ∈ s
  · simp only [finiteDiagonal_apply, if_pos hn, norm_smul]
    exact mul_le_mul_of_nonneg_right (hcd n hn) (norm_nonneg _)
  · simp only [finiteDiagonal_apply, if_neg hn, le_refl]

theorem finiteDiagonal_norm_congr (s : Finset ℕ) (c d : ℕ → ℂ) (v : lp E 2)
    (hcd : ∀ n ∈ s, ‖c n‖ = ‖d n‖) :
    ‖finiteDiagonal s c v‖ = ‖finiteDiagonal s d v‖ :=
  le_antisymm (finiteDiagonal_norm_mono s c d v (fun n hn => (hcd n hn).le))
    (finiteDiagonal_norm_mono s d c v (fun n hn => (hcd n hn).ge))

theorem finiteDiagonal_projection_norm_le (s : Finset ℕ) (v : lp E 2) :
    ‖finiteDiagonal s (fun _ => 1) v‖ ≤ ‖v‖ := by
  apply lp.norm_mono (by norm_num)
  intro n
  by_cases hn : n ∈ s
  · simp only [finiteDiagonal_apply, if_pos hn, one_smul, le_refl]
  · simp only [finiteDiagonal_apply, if_neg hn, norm_zero, norm_nonneg]

theorem finiteDiagonal_norm_le (s : Finset ℕ) (c : ℕ → ℂ) (v : lp E 2)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ n ∈ s, ‖c n‖ ≤ C) :
    ‖finiteDiagonal s c v‖ ≤ C * ‖finiteDiagonal s (fun _ => 1) v‖ := by
  calc
    _ ≤ ‖finiteDiagonal s (fun _ => (C : ℂ)) v‖ :=
      finiteDiagonal_norm_mono s c _ v (fun n hn => by
        simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using hc n hn)
    _ = C * ‖finiteDiagonal s (fun _ => 1) v‖ := by
      rw [finiteDiagonal_const, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC]

theorem finiteDiagonal_norm_le_mul (s : Finset ℕ) (c : ℕ → ℂ) (v : lp E 2)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ n ∈ s, ‖c n‖ ≤ C) :
    ‖finiteDiagonal s c v‖ ≤ C * ‖v‖ :=
  (finiteDiagonal_norm_le s c v hC hc).trans
    (mul_le_mul_of_nonneg_left (finiteDiagonal_projection_norm_le s v) hC)

/-- Finite spectral multipliers preserve holomorphic parameter dependence. -/
theorem differentiable_finiteDiagonal (s : Finset ℕ) {c : ℂ → ℕ → ℂ}
    {v : ℂ → lp E 2} (hc : ∀ n ∈ s, Differentiable ℂ (fun z => c z n))
    (hv : Differentiable ℂ v) :
    Differentiable ℂ (fun z => finiteDiagonal s (c z) (v z)) := by
  unfold finiteDiagonal
  apply Differentiable.fun_sum
  intro n hn
  have he : Differentiable ℂ (fun z => v z n) :=
    (lp.evalCLM ℂ E 2 n).differentiable.comp hv
  simpa only [Function.comp_def, lp.singleContinuousLinearMap_apply] using
    (lp.singleContinuousLinearMap ℂ E 2 n).differentiable.comp ((hc n hn).fun_smul he)

private theorem angular_rpow_strip_bound {a t : ℝ} (ha : 0 < a)
    (ht : 0 ≤ t) (ht' : t ≤ 1) : a ^ t ≤ max 1 a := by
  by_cases ha' : 1 ≤ a
  · calc
      a ^ t ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha' ht'
      _ ≤ max 1 a := by rw [Real.rpow_one]; exact le_max_right _ _
  · exact (Real.rpow_le_one ha.le (le_of_lt (lt_of_not_ge ha')) ht).trans
      (le_max_left _ _)

/-- The finite analytic family used in the three-lines argument. -/
def angularInterpolationFamily (K : lp E 2 →L[ℂ] lp E 2)
    (a b : ℕ → ℝ) (s t : Finset ℕ) (v : lp E 2) (z : ℂ) : lp E 2 :=
  finiteDiagonal s (fun n => (a n : ℂ) ^ z)
    (K (finiteDiagonal t (fun n => (b n : ℂ) ^ (-z)) v))

theorem differentiable_angularInterpolationFamily (K : lp E 2 →L[ℂ] lp E 2)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (s t : Finset ℕ) (v : lp E 2) :
    Differentiable ℂ (angularInterpolationFamily K a b s t v) := by
  unfold angularInterpolationFamily
  apply differentiable_finiteDiagonal
  · intro n _
    exact differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (ha n).ne'))
  · apply K.differentiable.comp
    apply differentiable_finiteDiagonal
    · intro n _
      exact differentiable_id.neg.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (hb n).ne'))
    · exact differentiable_const v

theorem bounded_angularInterpolationFamily (K : lp E 2 →L[ℂ] lp E 2)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (s t : Finset ℕ) (v : lp E 2) :
    BddAbove ((norm ∘ angularInterpolationFamily K a b s t v) ''
      verticalClosedStrip 0 1) := by
  let A : ℝ := ∑ n ∈ s, max 1 (a n)
  let B : ℝ := ∑ n ∈ t, max 1 ((b n)⁻¹)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => (zero_le_one.trans (le_max_left _ _)))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => (zero_le_one.trans (le_max_left _ _)))
  refine ⟨A * (‖K‖ * (B * ‖v‖)), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz0 : 0 ≤ z.re := hz.1
  have hz1 : z.re ≤ 1 := hz.2
  have hout : ∀ n ∈ s, ‖(a n : ℂ) ^ z‖ ≤ A := by
    intro n hn
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (ha n)]
    exact (angular_rpow_strip_bound (ha n) hz0 hz1).trans
      (Finset.single_le_sum (f := fun n => max 1 (a n))
        (fun _ _ => zero_le_one.trans (le_max_left _ _)) hn)
  have hin : ∀ n ∈ t, ‖(b n : ℂ) ^ (-z)‖ ≤ B := by
    intro n hn
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hb n), Complex.neg_re,
      Real.rpow_neg_eq_inv_rpow]
    exact (angular_rpow_strip_bound (inv_pos.mpr (hb n)) hz0 hz1).trans
      (Finset.single_le_sum (f := fun n => max 1 ((b n)⁻¹))
        (fun _ _ => zero_le_one.trans (le_max_left _ _)) hn)
  change ‖angularInterpolationFamily K a b s t v z‖ ≤ A * (‖K‖ * (B * ‖v‖))
  unfold angularInterpolationFamily
  calc
    _ ≤ A * ‖K (finiteDiagonal t (fun n => (b n : ℂ) ^ (-z)) v)‖ :=
      finiteDiagonal_norm_le_mul s _ _ hA hout
    _ ≤ A * (‖K‖ * ‖finiteDiagonal t (fun n => (b n : ℂ) ^ (-z)) v‖) :=
      mul_le_mul_of_nonneg_left (K.le_opNorm _) hA
    _ ≤ A * (‖K‖ * (B * ‖v‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (finiteDiagonal_norm_le_mul t _ v hB hin)
          (norm_nonneg K)) hA

/-- Weighted three-lines interpolation on two independent finite spectral
projections.  Only the two endpoint operator estimates are hypotheses.
The interior estimate is a consequence of Hadamard's theorem. -/
theorem angular_three_lines_finite (K : lp E 2 →L[ℂ] lp E 2)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    {C : ℝ} (hC : 0 ≤ C) (hzero : ‖K‖ ≤ C)
    (hone : ∀ (s t : Finset ℕ) (v : lp E 2),
      ‖finiteDiagonal s (fun n => (a n : ℂ))
        (K (finiteDiagonal t (fun _ => 1) v))‖ ≤
      C * ‖finiteDiagonal t (fun n => (b n : ℂ)) v‖)
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta' : theta ≤ 1)
    (s t : Finset ℕ) (v : lp E 2) :
    ‖angularInterpolationFamily K a b s t v (theta : ℂ)‖ ≤
      C * ‖finiteDiagonal t (fun _ => 1) v‖ := by
  let F := angularInterpolationFamily K a b s t v
  let D : ℝ := C * ‖finiteDiagonal t (fun _ => 1) v‖
  have hD : 0 ≤ D := mul_nonneg hC (norm_nonneg _)
  have hleft : ∀ z ∈ Complex.re ⁻¹' {0}, ‖F z‖ ≤ D := by
    intro z hz
    have hz' : z.re = 0 := hz
    have hin : ‖finiteDiagonal t (fun n => (b n : ℂ) ^ (-z)) v‖ =
        ‖finiteDiagonal t (fun _ => 1) v‖ := by
      apply finiteDiagonal_norm_congr
      intro n _
      simp only [Complex.norm_cpow_eq_rpow_re_of_pos (hb n), Complex.neg_re,
        hz', neg_zero, Real.rpow_zero, norm_one]
    calc
      ‖F z‖ = ‖finiteDiagonal s (fun _ => 1)
          (K (finiteDiagonal t (fun n => (b n : ℂ) ^ (-z)) v))‖ := by
        dsimp only [F, angularInterpolationFamily]
        apply finiteDiagonal_norm_congr
        intro n _
        simp only [Complex.norm_cpow_eq_rpow_re_of_pos (ha n), hz',
          Real.rpow_zero, norm_one]
      _ ≤ ‖K (finiteDiagonal t (fun n => (b n : ℂ) ^ (-z)) v)‖ :=
        finiteDiagonal_projection_norm_le _ _
      _ ≤ C * ‖finiteDiagonal t (fun n => (b n : ℂ) ^ (-z)) v‖ :=
        (K.le_opNorm _).trans (mul_le_mul_of_nonneg_right hzero (norm_nonneg _))
      _ = D := by rw [hin]
  have hright : ∀ z ∈ Complex.re ⁻¹' {1}, ‖F z‖ ≤ D := by
    intro z hz
    have hz' : z.re = 1 := hz
    have hin : ‖finiteDiagonal t (fun n => (b n : ℂ))
        (finiteDiagonal t (fun n => (b n : ℂ) ^ (-z)) v)‖ =
        ‖finiteDiagonal t (fun _ => 1) v‖ := by
      rw [finiteDiagonal_comp]
      apply finiteDiagonal_norm_congr
      intro n _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hb n),
        Complex.norm_cpow_eq_rpow_re_of_pos (hb n), Complex.neg_re, hz',
        Real.rpow_neg_one, mul_inv_cancel₀ (hb n).ne', norm_one]
    calc
      ‖F z‖ = ‖finiteDiagonal s (fun n => (a n : ℂ))
          (K (finiteDiagonal t (fun n => (b n : ℂ) ^ (-z)) v))‖ := by
        dsimp only [F, angularInterpolationFamily]
        apply finiteDiagonal_norm_congr
        intro n _
        simp only [Complex.norm_cpow_eq_rpow_re_of_pos (ha n), hz', Real.rpow_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha n)]
      _ ≤ C * ‖finiteDiagonal t (fun n => (b n : ℂ))
          (finiteDiagonal t (fun n => (b n : ℂ) ^ (-z)) v)‖ := by
        simpa only [finiteDiagonal_project] using
          hone s t (finiteDiagonal t (fun n => (b n : ℂ) ^ (-z)) v)
      _ = D := by rw [hin]
  have h := norm_le_interp_of_mem_verticalClosedStrip₀₁' F
    (z := (theta : ℂ)) (a := D) (b := D) ⟨htheta, htheta'⟩
    (differentiable_angularInterpolationFamily K a b ha hb s t v).diffContOnCl
    (bounded_angularInterpolationFamily K a b ha hb s t v) hleft hright
  have hexp : (1 - theta) + theta = 1 := by ring
  have hcollapse : D ^ (1 - theta) * D ^ theta = D := by
    rw [← Real.rpow_add' hD (by linarith : (1 - theta) + theta ≠ 0),
      hexp, Real.rpow_one]
  change ‖F (theta : ℂ)‖ ≤ D
  simpa only [Complex.ofReal_re, hcollapse] using h

end ContinuousFlexibility.Analysis
