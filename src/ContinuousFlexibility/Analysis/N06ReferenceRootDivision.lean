module

public import ContinuousFlexibility.Analysis.SmoothDivisionBounds
public import ContinuousFlexibility.Analysis.N06RadialGeometryJets
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The actual divided profile on both sides of a reference root

The smooth factor is S05's genuine division of the shifted derivative.
Its Taylor integral bounds its ordinary jets on a symmetric interval.
The resulting Lipschitz estimates retain the actual profile and factor;
they will provide explicit positive collars from the real root curvature.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

set_option backward.isDefEq.respectTransparency false

/-- The original Taylor integral gives the same fixed loss on both
sides of its zero, including all ordinary derivatives at the zero. -/
theorem n06_smoothDivisionFactor_jet_symmetric
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfactor : ∀ x : ℝ, f x = x * g x) (n : ℕ)
    {ρ M x : ℝ} (hx : x ∈ Icc (-ρ) ρ)
    (hbound : ∀ y ∈ Icc (-ρ) ρ, |iteratedDeriv (n + 1) f y| ≤ M) :
    |iteratedDeriv n g x| ≤ M := by
  have hρ : 0 ≤ ρ := by linarith only [hx.1, hx.2]
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound 0 ⟨neg_nonpos.mpr hρ, hρ⟩)
  rw [iteratedDeriv_smoothDivisionFactor hf hg hfactor n]
  have hpoint (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      ‖t ^ n * iteratedDeriv (n + 1) f (t * x)‖ ≤ M := by
    have htx : |t * x| ≤ ρ := by
      rw [abs_mul, abs_of_nonneg ht.1.le]
      exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg x)).trans
        (by simpa only [one_mul] using abs_le.mpr hx)
    have hpow0 : 0 ≤ t ^ n := pow_nonneg ht.1.le n
    have hpow1 : t ^ n ≤ 1 := pow_le_one₀ ht.1.le ht.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow0]
    calc
      _ ≤ t ^ n * M := mul_le_mul_of_nonneg_left (hbound _ (abs_le.mp htx)) hpow0
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right hpow1 hM
      _ = M := one_mul _
  have hint := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall hpoint)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 1)
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const, sub_zero, one_smul] using hint

/-- Unit reflections and translations preserve the absolute values of
the actual profile derivative jets. -/
theorem n06_abs_iteratedDeriv_shifted_profile_deriv
    (w : ℝ → ℝ) (r ι : ℝ) (hι : ι = 1 ∨ ι = -1) (k : ℕ) (x : ℝ) :
    |iteratedDeriv k (fun t => -deriv w (r + ι * t)) x| =
      |iteratedDeriv (k + 1) w (r + ι * x)| := by
  rcases hι with rfl | rfl
  · simp only [one_mul, iteratedDeriv_fun_neg, abs_neg,
      iteratedDeriv_comp_const_add, ← iteratedDeriv_succ']
  · simp only [neg_one_mul, ← sub_eq_add_neg]
    simp only [iteratedDeriv_fun_neg, abs_neg, iteratedDeriv_comp_const_sub,
      smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      ← iteratedDeriv_succ']

/-- Construct the same genuine divided profile and bound its first two
jets and variation from the original profile through order four. -/
theorem n06_exists_reference_root_division
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (r ι : ℝ)
    (hι : ι = 1 ∨ ι = -1) (hz : deriv w r = 0) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      g 0 = -ι * deriv (deriv w) r ∧
      (∀ x : ℝ, -deriv w (r + ι * x) = x * g x) ∧
      ∀ M : ℝ, 1 ≤ M →
        (∀ k : ℕ, k ≤ 4 → ∀ y ∈ Icc (r - 1) (r + 1),
          |iteratedDeriv k w y| ≤ M) →
        ∀ x ∈ Icc (-1 : ℝ) 1,
          N06ScalarJetTwoBound g x M ∧
          |g x - g 0| ≤ M * |x| ∧
          |w (r + ι * x) - w r| ≤ M * |x| := by
  let f : ℝ → ℝ := fun x => -deriv w (r + ι * x)
  have hwd : ContDiff ℝ ∞ (deriv w) := (contDiff_infty_iff_deriv.mp hw).2
  have hshift : ContDiff ℝ ∞ (fun x : ℝ => r + ι * x) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  have hf : ContDiff ℝ ∞ f := (hwd.comp hshift).neg
  have hf0 : f 0 = 0 := by simp only [f, mul_zero, add_zero, hz, neg_zero]
  obtain ⟨g, hg, hg0, hfactor⟩ := Statements.exists_smooth_division_at_zero hf hf0
  have hsh : HasDerivAt (fun x : ℝ => r + ι * x) ι (0 : ℝ) := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id (0 : ℝ)).const_mul ι).const_add r
  have hdf : deriv f 0 = -ι * deriv (deriv w) r := by
    calc
      deriv f 0 = -(deriv (deriv w) (r + ι * 0) * ι) :=
        (((hwd.differentiable (by simp) _).hasDerivAt.comp 0 hsh).neg).deriv
      _ = -ι * deriv (deriv w) r := by simp only [mul_zero, add_zero]; ring
  refine ⟨g, hg, hg0.trans hdf, hfactor, ?_⟩
  intro M hM hbound
  have hιabs : |ι| = 1 := by rcases hι with rfl | rfl <;> norm_num
  have hmem {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
      r + ι * x ∈ Icc (r - 1) (r + 1) := by
    have ha : |ι * x| ≤ 1 := by simpa only [abs_mul, hιabs, one_mul] using abs_le.mpr hx
    have hh := abs_le.mp ha
    exact ⟨by linarith only [hh.1], by linarith only [hh.2]⟩
  have hjet (k : ℕ) (hk : k ≤ 2) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      |iteratedDeriv k g x| ≤ M := by
    apply n06_smoothDivisionFactor_jet_symmetric hf hg hfactor k hx
    intro y hy
    rw [n06_abs_iteratedDeriv_shifted_profile_deriv w r ι hι]
    exact hbound ((k + 1) + 1) (by omega) _ (hmem hy)
  have hgjet (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : N06ScalarJetTwoBound g x M := by
    constructor
    · simpa only [iteratedDeriv_zero] using hjet 0 (by norm_num) x hx
    · simpa only [iteratedDeriv_one] using hjet 1 (by norm_num) x hx
    · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hjet 2 le_rfl x hx
  intro x hx
  refine ⟨hgjet x hx, ?_, ?_⟩
  · have hgd : ∀ y ∈ Icc (-1 : ℝ) 1, DifferentiableAt ℝ g y :=
      fun y _ => hg.differentiable (by simp) y
    have hgn : ∀ y ∈ Icc (-1 : ℝ) 1, ‖deriv g y‖ ≤ M := by
      intro y hy
      simpa only [Real.norm_eq_abs] using (hgjet y hy).first
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le hgd hgn
      (convex_Icc (-1 : ℝ) 1) (show (0 : ℝ) ∈ Icc (-1) 1 by norm_num) hx
    simpa only [Real.norm_eq_abs, sub_zero] using hh
  · have hwdiff : ∀ y ∈ Icc (r - 1) (r + 1), DifferentiableAt ℝ w y :=
      fun y _ => hw.differentiable (by simp) y
    have hwn : ∀ y ∈ Icc (r - 1) (r + 1), ‖deriv w y‖ ≤ M := by
      intro y hy
      simpa only [Real.norm_eq_abs, iteratedDeriv_one] using hbound 1 (by norm_num) y hy
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le hwdiff hwn
      (convex_Icc (r - 1) (r + 1))
      (show r ∈ Icc (r - 1) (r + 1) by constructor <;> linarith) (hmem hx)
    simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_mul, hιabs, one_mul] using hh

end ContinuousFlexibility.Analysis
