module

public import ContinuousFlexibility.Analysis.N06IntervalCubicCutoffJets
public import ContinuousFlexibility.Analysis.N06OpenCubicTestCutoff

/-!
# The cubic cutoff commutator for an actual radial weight

The full symmetric divergence product rule keeps both mixed channels.
A bound for the actual radial weight and its derivative controls the
commutator on any original canonical interval. Only the test germ is
used; no endpoint extension of its coefficients is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem cubic_normal_drift {d : ℝ → ℝ} {A B : PolarPoint → ℝ} {p : PolarPoint}
    (hd : DifferentiableAt ℝ d p.1) (hA : DifferentiableAt ℝ A p)
    (hB : DifferentiableAt ℝ B p) :
    radialPartial (fun q => d q.1 ^ 3 * A q) p +
      angularPartial (fun q => d q.1 ^ 3 * B q) p =
      d p.1 ^ 2 * (3 * deriv d p.1 * A p + d p.1 * radialPartial A p +
        d p.1 * angularPartial B p) := by
  have hd₃ : DifferentiableAt ℝ (fun q : PolarPoint => d q.1 ^ 3) p :=
    (hd.pow 3).comp p differentiableAt_fst
  have hr : radialPartial (fun q : PolarPoint => d q.1 ^ 3) p =
      3 * d p.1 ^ 2 * deriv d p.1 := by
    calc
      _ = deriv (fun y => d y ^ 3) p.1 := radialPartial_radialHeightField (hd.pow 3)
      _ = _ := by
        have hpow := (hd.hasDerivAt.pow 3).deriv
        have heq : (d ^ 3 : ℝ → ℝ) = fun y => d y ^ 3 := by
          funext y
          rfl
        rw [heq] at hpow
        simpa only [Nat.cast_ofNat, Nat.reduceSub, smul_eq_mul] using hpow
  have ht : angularPartial (fun q : PolarPoint => d q.1 ^ 3) p = 0 :=
    angularPartial_radialHeightField (hd.pow 3)
  rw [radialPartial_mul hd₃ hA, angularPartial_mul hd₃ hB, hr, ht]
  ring

theorem n06_radialCubic_cutoff_commutator
    {d χ : ℝ → ℝ} {A B C φ : PolarPoint → ℝ} {p : PolarPoint}
    (hd : DifferentiableAt ℝ d p.1)
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hC : DifferentiableAt ℝ C p) (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ) :
    divergenceOperator (n06CubicCoefficients (fun q => d q.1) A B C)
        (fun q => χ q.1 * φ q) p -
      χ p.1 * divergenceOperator (n06CubicCoefficients (fun q => d q.1) A B C) φ p =
      (d p.1 ^ 3 * deriv (deriv χ) p.1) * A p * φ p +
      (d p.1 ^ 2 * deriv χ p.1) *
        (3 * deriv d p.1 * A p + d p.1 * radialPartial A p +
          d p.1 * angularPartial B p) * φ p +
      2 * (d p.1 ^ 3 * deriv χ p.1) * A p * radialPartial φ p +
      2 * (d p.1 ^ 3 * deriv χ p.1) * B p * angularPartial φ p := by
  have hd₃ : DifferentiableAt ℝ (fun q : PolarPoint => d q.1 ^ 3) p :=
    (hd.pow 3).comp p differentiableAt_fst
  rw [n06_divergence_radialCutoff_commutator (hd₃.mul hA) (hd₃.mul hB) (hd₃.mul hC) hφ hχ]
  change deriv (deriv χ) p.1 * (d p.1 ^ 3 * A p) * φ p +
    deriv χ p.1 * ((radialPartial (fun q => d q.1 ^ 3 * A q) p +
      angularPartial (fun q => d q.1 ^ 3 * B q) p) * φ p +
        2 * (d p.1 ^ 3 * A p) * radialPartial φ p +
        2 * (d p.1 ^ 3 * B p) * angularPartial φ p) = _
  rw [cubic_normal_drift hd hA hB]
  ring

private theorem abs_triple_le {x y z X Y Z : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hx : |x| ≤ X) (hy : |y| ≤ Y) (hz : |z| ≤ Z) :
    |x * y * z| ≤ X * Y * Z := by
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul hx hy (abs_nonneg _) hX) hz
    (abs_nonneg _) (mul_nonneg hX hY)

private theorem abs_four_le (x y z w : ℝ) :
    |x + y + z + w| ≤ |x| + |y| + |z| + |w| :=
  (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)

theorem n06_radialCubic_cutoff_error_bound
    {d χ : ℝ → ℝ} {A B C φ : PolarPoint → ℝ} {p : PolarPoint} {D δ J ε : ℝ}
    (hd : DifferentiableAt ℝ d p.1)
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hC : DifferentiableAt ℝ C p) (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ)
    (hD : 1 ≤ D) (hδ : 0 ≤ δ) (hJ : 0 ≤ J) (hε : 0 ≤ ε)
    (hd₀ : |d p.1| ≤ D) (hd₁ : |deriv d p.1| ≤ D)
    (hA₀ : |A p| ≤ δ) (hB₀ : |B p| ≤ δ)
    (hAr : |radialPartial A p| ≤ δ) (hBt : |angularPartial B p| ≤ δ)
    (hφ₀ : |φ p| ≤ J) (hφr : |radialPartial φ p| ≤ J) (hφt : |angularPartial φ p| ≤ J)
    (hχ₁ : |d p.1 ^ 2 * deriv χ p.1| ≤ ε)
    (hχ₂ : |d p.1 ^ 3 * deriv (deriv χ) p.1| ≤ ε) :
    |divergenceOperator (n06CubicCoefficients (fun q => d q.1) A B C)
        (fun q => χ q.1 * φ q) p -
      χ p.1 * divergenceOperator (n06CubicCoefficients (fun q => d q.1) A B C) φ p| ≤
        10 * D * ε * δ * J := by
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hχ₃ : |d p.1 ^ 3 * deriv χ p.1| ≤ D * ε := by
    calc
      _ = |d p.1 * (d p.1 ^ 2 * deriv χ p.1)| := congrArg abs (by ring)
      _ = |d p.1| * |d p.1 ^ 2 * deriv χ p.1| := abs_mul _ _
      _ ≤ D * ε := mul_le_mul hd₀ hχ₁ (abs_nonneg _) hD₀
  have hfirst : |3 * deriv d p.1 * A p + d p.1 * radialPartial A p +
      d p.1 * angularPartial B p| ≤ 5 * D * δ := by
    have h₁ : |3 * deriv d p.1 * A p| ≤ 3 * D * δ :=
      abs_triple_le (by norm_num) hD₀ (by norm_num) hd₁ hA₀
    have h₂ : |d p.1 * radialPartial A p| ≤ D * δ := by
      rw [abs_mul]
      exact mul_le_mul hd₀ hAr (abs_nonneg _) hD₀
    have h₃ : |d p.1 * angularPartial B p| ≤ D * δ := by
      rw [abs_mul]
      exact mul_le_mul hd₀ hBt (abs_nonneg _) hD₀
    exact ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add h₁ h₂)) h₃)).trans_eq (by ring)
  have h₁ := abs_triple_le hε hδ hχ₂ hA₀ hφ₀
  have h₁' : |(d p.1 ^ 3 * deriv (deriv χ) p.1) * A p * φ p| ≤ D * (ε * δ * J) :=
    h₁.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hD (mul_nonneg (mul_nonneg hε hδ) hJ))
  have h₂ := abs_triple_le hε (show 0 ≤ 5 * D * δ by positivity) hχ₁ hfirst hφ₀
  have h₃ : |2 * (d p.1 ^ 3 * deriv χ p.1) * A p * radialPartial φ p| ≤
      2 * ((D * ε) * δ * J) := by
    rw [show 2 * (d p.1 ^ 3 * deriv χ p.1) * A p * radialPartial φ p =
      2 * ((d p.1 ^ 3 * deriv χ p.1) * A p * radialPartial φ p) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left
      (abs_triple_le (mul_nonneg hD₀ hε) hδ hχ₃ hA₀ hφr) (by norm_num)
  have h₄ : |2 * (d p.1 ^ 3 * deriv χ p.1) * B p * angularPartial φ p| ≤
      2 * ((D * ε) * δ * J) := by
    rw [show 2 * (d p.1 ^ 3 * deriv χ p.1) * B p * angularPartial φ p =
      2 * ((d p.1 ^ 3 * deriv χ p.1) * B p * angularPartial φ p) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left
      (abs_triple_le (mul_nonneg hD₀ hε) hδ hχ₃ hB₀ hφt) (by norm_num)
  rw [n06_radialCubic_cutoff_commutator hd hA hB hC hφ hχ]
  exact (abs_four_le _ _ _ _).trans
    ((add_le_add (add_le_add (add_le_add h₁' h₂) h₃) h₄).trans_eq (by ring))

/-- Open-strip smoothness suffices because the estimate is a germ identity. -/
theorem n06_radialCubic_cutoff_error_bound_on
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {d χ : ℝ → ℝ} {A B C φ : PolarPoint → ℝ} {p : PolarPoint} {D δ J ε : ℝ}
    (hd : DifferentiableAt ℝ d p.1)
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hC : DifferentiableAt ℝ C p)
    (hφ : ContDiffOn ℝ ∞ φ (canonicalOpen S K m)) (hpU : p ∈ canonicalOpen S K m)
    (hχ : ContDiff ℝ ∞ χ)
    (hD : 1 ≤ D) (hδ : 0 ≤ δ) (hJ : 0 ≤ J) (hε : 0 ≤ ε)
    (hd₀ : |d p.1| ≤ D) (hd₁ : |deriv d p.1| ≤ D)
    (hA₀ : |A p| ≤ δ) (hB₀ : |B p| ≤ δ)
    (hAr : |radialPartial A p| ≤ δ) (hBt : |angularPartial B p| ≤ δ)
    (hφ₀ : |φ p| ≤ J) (hφr : |radialPartial φ p| ≤ J) (hφt : |angularPartial φ p| ≤ J)
    (hχ₁ : |d p.1 ^ 2 * deriv χ p.1| ≤ ε)
    (hχ₂ : |d p.1 ^ 3 * deriv (deriv χ) p.1| ≤ ε) :
    |divergenceOperator (n06CubicCoefficients (fun q => d q.1) A B C)
        (fun q => χ q.1 * φ q) p -
      χ p.1 * divergenceOperator (n06CubicCoefficients (fun q => d q.1) A B C) φ p| ≤
        10 * D * ε * δ * J := by
  obtain ⟨g, hg, he⟩ := n06_exists_smooth_strip_germ hφ hpU
  have hr : radialPartial g p = radialPartial φ p :=
    congrArg (fun T : PolarPoint →L[ℝ] ℝ => T (1, 0)) (he.fderiv_eq (𝕜 := ℝ))
  have ht : angularPartial g p = angularPartial φ p :=
    congrArg (fun T : PolarPoint →L[ℝ] ℝ => T (0, 1)) (he.fderiv_eq (𝕜 := ℝ))
  have hcut : (fun q : PolarPoint => χ q.1 * g q) =ᶠ[𝓝 p]
      (fun q => χ q.1 * φ q) := by
    filter_upwards [he] with q hq
    rw [hq]
  have h := n06_radialCubic_cutoff_error_bound hd hA hB hC hg hχ hD hδ hJ hε hd₀ hd₁
    hA₀ hB₀ hAr hBt (by simpa only [he.eq_of_nhds] using hφ₀)
    (by simpa only [hr] using hφr) (by simpa only [ht] using hφt) hχ₁ hχ₂
  simpa only [n06_divergenceOperator_input_congr_germ _ hcut,
    n06_divergenceOperator_input_congr_germ _ he] using h

end ContinuousFlexibility.Analysis
