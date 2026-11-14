module

public import ContinuousFlexibility.Radial.PositiveBufferComparison
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# A universal inner cutoff and its commutator

The same fixed smooth transition is translated to the inner layer of
every normalized buffer.  It equals one up to `σ + 2` and zero from
`σ + 4` onwards.  Its derivative bounds are independent of `σ`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

/-- A smooth transition from one to zero over a layer of width two. -/
def positiveBufferCutoffProfile (x : ℝ) : ℝ := 1 - smoothTransition (x / 2)

theorem positiveBufferCutoffProfile_contDiff :
    ContDiff ℝ ∞ positiveBufferCutoffProfile :=
  contDiff_const.sub (smoothTransition.contDiff.comp (contDiff_id.div_const 2))

theorem positiveBufferCutoffProfile_one {x : ℝ} (hx : x ≤ 0) :
    positiveBufferCutoffProfile x = 1 := by
  unfold positiveBufferCutoffProfile
  rw [smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx (by norm_num)), sub_zero]

theorem positiveBufferCutoffProfile_zero {x : ℝ} (hx : 2 ≤ x) :
    positiveBufferCutoffProfile x = 0 := by
  unfold positiveBufferCutoffProfile
  rw [smoothTransition.one_of_one_le (by linarith : 1 ≤ x / 2), sub_self]

theorem positiveBufferCutoffProfile_bounds (x : ℝ) :
    0 ≤ positiveBufferCutoffProfile x ∧ positiveBufferCutoffProfile x ≤ 1 := by
  unfold positiveBufferCutoffProfile
  constructor
  · exact sub_nonneg.mpr (smoothTransition.le_one _)
  · linarith [smoothTransition.nonneg (x / 2)]

/-- Both differentiated cutoffs vanish away from the transition layer. -/
theorem positiveBufferCutoffProfile_derivatives_zero {x : ℝ}
    (hx : x ∉ Icc (0 : ℝ) 2) :
    deriv positiveBufferCutoffProfile x = 0 ∧
      deriv (deriv positiveBufferCutoffProfile) x = 0 := by
  have hconst : ∃ c : ℝ, positiveBufferCutoffProfile =ᶠ[𝓝 x] fun _ => c := by
    by_cases hx0 : x < 0
    · refine ⟨1, ?_⟩
      filter_upwards [eventually_lt_nhds hx0] with y hy
      exact positiveBufferCutoffProfile_one hy.le
    · have hx2 : 2 < x := lt_of_not_ge (fun h => hx ⟨le_of_not_gt hx0, h⟩)
      refine ⟨0, ?_⟩
      filter_upwards [eventually_gt_nhds hx2] with y hy
      exact positiveBufferCutoffProfile_zero hy.le
  obtain ⟨c, hc⟩ := hconst
  constructor
  · simpa using hc.deriv_eq
  · simpa using hc.deriv.deriv_eq

theorem positiveBufferCutoffProfile_derivative_compactSupport :
    HasCompactSupport (deriv positiveBufferCutoffProfile) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (0 : ℝ) 2))
  intro x hx
  exact (positiveBufferCutoffProfile_derivatives_zero hx).1

/-- One constant bounds both derivatives of the fixed transition. -/
theorem positiveBufferCutoffProfile_derivative_bounds :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x, |deriv positiveBufferCutoffProfile x| ≤ C) ∧
      ∀ x, |deriv (deriv positiveBufferCutoffProfile) x| ≤ C := by
  have h1 : ContDiff ℝ ∞ (deriv positiveBufferCutoffProfile) :=
    (contDiff_infty_iff_deriv.mp positiveBufferCutoffProfile_contDiff).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv positiveBufferCutoffProfile)) :=
    (contDiff_infty_iff_deriv.mp h1).2
  obtain ⟨C₁, hC₁⟩ := h1.continuous.bounded_above_of_compact_support
    positiveBufferCutoffProfile_derivative_compactSupport
  obtain ⟨C₂, hC₂⟩ := h2.continuous.bounded_above_of_compact_support
    positiveBufferCutoffProfile_derivative_compactSupport.deriv
  refine ⟨max 0 (max C₁ C₂), le_max_left _ _, ?_, ?_⟩
  · intro x
    exact (hC₁ x).trans ((le_max_left C₁ C₂).trans (le_max_right 0 _))
  · intro x
    exact (hC₂ x).trans ((le_max_right C₁ C₂).trans (le_max_right 0 _))

/-- The translated inner cutoff for a normalized buffer of action `σ`. -/
def positiveBufferCutoff (σ x : ℝ) : ℝ :=
  positiveBufferCutoffProfile (x - (σ + 2))

theorem positiveBufferCutoff_contDiff (σ : ℝ) : ContDiff ℝ ∞ (positiveBufferCutoff σ) :=
  positiveBufferCutoffProfile_contDiff.comp (contDiff_id.sub contDiff_const)

theorem positiveBufferCutoff_one {σ x : ℝ} (hx : x ≤ σ + 2) :
    positiveBufferCutoff σ x = 1 :=
  positiveBufferCutoffProfile_one (sub_nonpos.mpr hx)

theorem positiveBufferCutoff_zero {σ x : ℝ} (hx : σ + 4 ≤ x) :
    positiveBufferCutoff σ x = 0 :=
  positiveBufferCutoffProfile_zero (by linarith)

theorem positiveBufferCutoff_bounds (σ x : ℝ) :
    0 ≤ positiveBufferCutoff σ x ∧ positiveBufferCutoff σ x ≤ 1 :=
  positiveBufferCutoffProfile_bounds _

theorem positiveBufferCutoff_deriv (σ x : ℝ) :
    deriv (positiveBufferCutoff σ) x =
      deriv positiveBufferCutoffProfile (x - (σ + 2)) := by
  have hd : Differentiable ℝ positiveBufferCutoffProfile :=
    positiveBufferCutoffProfile_contDiff.differentiable (by simp)
  have h := (hd (x - (σ + 2))).hasDerivAt.comp x
    ((hasDerivAt_id x).sub_const (σ + 2))
  change deriv (fun y => positiveBufferCutoffProfile (y - (σ + 2))) x = _
  simpa only [Function.comp_def, id_eq, mul_one] using h.deriv

theorem positiveBufferCutoff_deriv_deriv (σ x : ℝ) :
    deriv (deriv (positiveBufferCutoff σ)) x =
      deriv (deriv positiveBufferCutoffProfile) (x - (σ + 2)) := by
  have hd : Differentiable ℝ (deriv positiveBufferCutoffProfile) :=
    (contDiff_infty_iff_deriv.mp positiveBufferCutoffProfile_contDiff).2.differentiable (by simp)
  have heq : deriv (positiveBufferCutoff σ) =
      fun y => deriv positiveBufferCutoffProfile (y - (σ + 2)) :=
    funext (positiveBufferCutoff_deriv σ)
  rw [heq]
  have h := (hd (x - (σ + 2))).hasDerivAt.comp x
    ((hasDerivAt_id x).sub_const (σ + 2))
  simpa only [Function.comp_def, id_eq, mul_one] using h.deriv

theorem positiveBufferCutoff_derivatives_zero {σ x : ℝ}
    (hx : x ∉ Icc (σ + 2) (σ + 4)) :
    deriv (positiveBufferCutoff σ) x = 0 ∧
      deriv (deriv (positiveBufferCutoff σ)) x = 0 := by
  rw [positiveBufferCutoff_deriv, positiveBufferCutoff_deriv_deriv]
  apply positiveBufferCutoffProfile_derivatives_zero
  intro h
  exact hx ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The derivative bounds have one constant before all translations. -/
theorem positiveBufferCutoff_derivative_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ x : ℝ,
      |deriv (positiveBufferCutoff σ) x| ≤ C ∧
      |deriv (deriv (positiveBufferCutoff σ)) x| ≤ C := by
  obtain ⟨C, hC, h1, h2⟩ := positiveBufferCutoffProfile_derivative_bounds
  refine ⟨C, hC, fun σ x => ?_⟩
  rw [positiveBufferCutoff_deriv, positiveBufferCutoff_deriv_deriv]
  exact ⟨h1 _, h2 _⟩

/-- The ordinary function produced by the cutoff commutator. -/
def positiveBufferCutoffError (σ : ℝ) (u du : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv (positiveBufferCutoff σ)) x * u x -
    2 * deriv (positiveBufferCutoff σ) x * du x

theorem positiveBufferCutoffError_support (σ : ℝ) (u du : ℝ → ℝ) :
    Function.support (positiveBufferCutoffError σ u du) ⊆ Icc (σ + 2) (σ + 4) := by
  intro x hx
  by_contra hn
  have hd := positiveBufferCutoff_derivatives_zero hn
  apply hx
  simp only [positiveBufferCutoffError, hd.1, hd.2, neg_zero, zero_mul, mul_zero, sub_self]

/-- Exact classical commutator for the Schrödinger expression. -/
theorem positiveBufferCutoff_commutator {J : Set ℝ} (hJ : IsOpen J)
    {u du q : ℝ → ℝ} (hu : ∀ x ∈ J, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ J, HasDerivAt du (q x * u x) x)
    (σ : ℝ) {x : ℝ} (hx : x ∈ J) :
    -deriv (deriv (fun y => positiveBufferCutoff σ y * u y)) x +
        q x * (positiveBufferCutoff σ x * u x) =
      positiveBufferCutoffError σ u du x := by
  have hχ := (positiveBufferCutoff_contDiff σ).differentiable (by simp)
  have hχ' := (contDiff_infty_iff_deriv.mp (positiveBufferCutoff_contDiff σ)).2
  have hdχ' := hχ'.differentiable (by simp)
  have hfirst : deriv (fun y => positiveBufferCutoff σ y * u y) =ᶠ[𝓝 x]
      fun y => deriv (positiveBufferCutoff σ) y * u y + positiveBufferCutoff σ y * du y := by
    filter_upwards [hJ.mem_nhds hx] with y hy
    exact ((hχ y).hasDerivAt.fun_mul (hu y hy)).deriv
  have hsecond := ((hdχ' x).hasDerivAt.fun_mul (hu x hx)).fun_add
    ((hχ x).hasDerivAt.fun_mul (hdu x hx))
  rw [hfirst.deriv_eq, hsecond.deriv]
  unfold positiveBufferCutoffError
  ring

/-- Quantitative commutator attenuation on a normalized buffer. -/
theorem positiveBufferCutoffError_bound {σ C : ℝ} {u du q : ℝ → ℝ}
    (hσ : 0 < σ) (hC : 0 ≤ C)
    (hcut : ∀ x, |deriv (positiveBufferCutoff σ) x| ≤ C ∧
      |deriv (deriv (positiveBufferCutoff σ)) x| ≤ C)
    (hc : ContinuousOn u (Icc 0 (σ + 6)))
    (hu : ∀ x ∈ Ioo 0 (σ + 6), HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo 0 (σ + 6), HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioo 0 (σ + 6), 1 ≤ q x)
    (h0 : u 0 = 1) (hwall : u (σ + 6) = 0) :
    ∀ x, |positiveBufferCutoffError σ u du x| ≤ 3 * C * exp (-σ) := by
  intro x
  by_cases hx : x ∈ Icc (σ + 2) (σ + 4)
  · have hdecay := positiveBuffer_normalized_inner_decay hσ hc hu hdu hq h0 hwall x hx
    have h1 : |deriv (deriv (positiveBufferCutoff σ)) x| * |u x| ≤ C * exp (-σ) :=
      mul_le_mul (hcut x).2 hdecay.1 (abs_nonneg _) hC
    have h2 : |deriv (positiveBufferCutoff σ) x| * |du x| ≤ C * exp (-σ) :=
      mul_le_mul (hcut x).1 hdecay.2 (abs_nonneg _) hC
    calc
      |positiveBufferCutoffError σ u du x| ≤
          |deriv (deriv (positiveBufferCutoff σ)) x| * |u x| +
            2 * (|deriv (positiveBufferCutoff σ) x| * |du x|) := by
        simpa only [positiveBufferCutoffError, sub_eq_add_neg, abs_mul, abs_neg,
          abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), mul_assoc] using
          abs_add_le (-deriv (deriv (positiveBufferCutoff σ)) x * u x)
            (-(2 * deriv (positiveBufferCutoff σ) x * du x))
      _ ≤ 3 * C * exp (-σ) := by nlinarith
  · have hd := positiveBufferCutoff_derivatives_zero hx
    simp only [positiveBufferCutoffError, hd.1, hd.2, neg_zero, zero_mul, mul_zero, sub_self,
      abs_zero]
    positivity

end ContinuousFlexibility.Radial
