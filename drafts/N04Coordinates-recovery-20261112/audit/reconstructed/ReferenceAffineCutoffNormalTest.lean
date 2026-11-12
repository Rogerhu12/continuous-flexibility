import ContinuousFlexibility.Analysis.ReferenceCompactCosineNormalTest

/-!
# The complete cutoff cost in a genuine same-inverse root test

The test is the actual compact field `(r-c) * chi(r) * cos(2 theta)`.
Its forcing retains both derivatives of the cutoff.  In particular, a
linear germ at a turning root does not justify discarding the transition
forcing.  The supplied inverse and its first-normal constant are unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Radial ContinuousFlexibility.Analysis
open scoped ContDiff

def referenceAffineCutoff (c : ℝ) (χ : ℝ → ℝ) (r : ℝ) : ℝ :=
  (r - c) * χ r

def referenceAffineCutoffForcing (D : ReferenceData) (c : ℝ)
    (χ : ℝ → ℝ) (r : ℝ) : ℝ :=
  D.w r * (2 * deriv χ r + (r - c) * deriv (deriv χ) r) +
    deriv D.w r * (χ r + (r - c) * deriv χ r - (4 / r) * ((r - c) * χ r))

theorem referenceAffineCutoff_deriv {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (c r : ℝ) :
    deriv (referenceAffineCutoff c χ) r = χ r + (r - c) * deriv χ r := by
  exact (show HasDerivAt (referenceAffineCutoff c χ)
      (χ r + (r - c) * deriv χ r) r from by
    simpa only [referenceAffineCutoff, one_mul] using
      ((hasDerivAt_id r).sub_const c).mul
        ((hχ.differentiable (by simp)) r).hasDerivAt).deriv

theorem referenceAffineCutoff_jacobi {D : ReferenceData}
    (hw : ContDiff ℝ ∞ D.w) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (c r : ℝ) :
    radialJacobi 4 D.w (referenceAffineCutoff c χ) r =
      referenceAffineCutoffForcing D c χ r := by
  have hχd : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hdu : deriv (referenceAffineCutoff c χ) =
      fun x => χ x + (x - c) * deriv χ x :=
    funext (referenceAffineCutoff_deriv hχ c)
  have hinner : HasDerivAt (fun x => χ x + (x - c) * deriv χ x)
      (deriv χ r + (1 * deriv χ r + (r - c) * deriv (deriv χ) r)) r :=
    ((hχ.differentiable (by simp)) r).hasDerivAt.add
      (((hasDerivAt_id r).sub_const c).mul
        ((hχd.differentiable (by simp)) r).hasDerivAt)
  have hflux := ((hw.differentiable (by simp)) r).hasDerivAt.mul hinner
  rw [radialJacobi, hdu, hflux.deriv]
  simp only [referenceAffineCutoffForcing, referenceAffineCutoff, div_eq_mul_inv]
  ring

/-- At a true turning root the forcing value depends on the cutoff slope,
not on an inverse of the second derivative of the profile. -/
theorem referenceAffineCutoff_at_root {D : ReferenceData}
    (hw : ContDiff ℝ ∞ D.w) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {c : ℝ} (hc : deriv D.w c = 0) :
    deriv (referenceAffineCutoff c χ) c = χ c ∧
      radialJacobi 4 D.w (referenceAffineCutoff c χ) c =
        2 * D.w c * deriv χ c := by
  constructor
  · simp only [referenceAffineCutoff_deriv hχ, sub_self, zero_mul, add_zero]
  · rw [referenceAffineCutoff_jacobi hw hχ]
    simp only [referenceAffineCutoffForcing, hc, sub_self, zero_mul, add_zero]
    ring

/-- The genuine pointwise transition cost at scale delta.  No lower bound
on the turning slope is an input or an output of this estimate. -/
theorem referenceAffineCutoffForcing_abs_le {D : ReferenceData}
    {χ : ℝ → ℝ} {c r δ B a : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B) (ha : 0 < a) (har : a ≤ r)
    (hrc : |r - c| ≤ δ) (hχ0 : |χ r| ≤ 1)
    (hχ1 : |deriv χ r| ≤ B / δ)
    (hχ2 : |deriv (deriv χ) r| ≤ B / δ ^ 2) :
    |referenceAffineCutoffForcing D c χ r| ≤
      |D.w r| * (3 * B / δ) +
        |deriv D.w r| * (1 + B + 4 * δ / a) := by
  have hr : 0 < r := ha.trans_le har
  have hfirst : |(r - c) * deriv χ r| ≤ B := by
    calc
      _ = |r - c| * |deriv χ r| := abs_mul _ _
      _ ≤ δ * (B / δ) := mul_le_mul hrc hχ1 (abs_nonneg _) hδ.le
      _ = B := by field_simp [hδ.ne']
  have hsecond : |(r - c) * deriv (deriv χ) r| ≤ B / δ := by
    calc
      _ = |r - c| * |deriv (deriv χ) r| := abs_mul _ _
      _ ≤ δ * (B / δ ^ 2) := mul_le_mul hrc hχ2 (abs_nonneg _) hδ.le
      _ = B / δ := by field_simp [hδ.ne']; ring
  have hlow : |(r - c) * χ r| ≤ δ := by
    calc
      _ = |r - c| * |χ r| := abs_mul _ _
      _ ≤ δ * 1 := mul_le_mul hrc hχ0 (abs_nonneg _) hδ.le
      _ = δ := mul_one _
  have hpotential : |(4 / r) * ((r - c) * χ r)| ≤ 4 * δ / a := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hr)]
    calc
      _ ≤ (4 / r) * δ := mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ (4 / a) * δ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) ha har) hδ.le
      _ = _ := by ring
  have h2 : |2 * deriv χ r + (r - c) * deriv (deriv χ) r| ≤ 3 * B / δ := by
    calc
      _ ≤ |2 * deriv χ r| + |(r - c) * deriv (deriv χ) r| := abs_add_le _ _
      _ = 2 * |deriv χ r| + |(r - c) * deriv (deriv χ) r| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (B / δ) + B / δ := add_le_add
        (mul_le_mul_of_nonneg_left hχ1 (by norm_num)) hsecond
      _ = _ := by ring
  have h1 : |χ r + (r - c) * deriv χ r - (4 / r) * ((r - c) * χ r)| ≤
      1 + B + 4 * δ / a := by
    have ht : |χ r + (r - c) * deriv χ r - (4 / r) * ((r - c) * χ r)| ≤
        |χ r + (r - c) * deriv χ r| + |(4 / r) * ((r - c) * χ r)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (χ r + (r - c) * deriv χ r) (0 : ℝ)
          ((4 / r) * ((r - c) * χ r))
    exact ht.trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add hχ0 hfirst)) hpotential)
  unfold referenceAffineCutoffForcing
  exact (abs_add_le _ _).trans (by
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)))

/-- The original first-normal constant is fixed before the center and
cutoff.  Its actual right-hand side includes the full displayed forcing
and the original border row; neither is silently omitted. -/
theorem FirstNormalInverseEstimate.compactAffineCutoff_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hNormal : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ) (χ : ℝ → ℝ),
      ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ radialCore D →
      let u := referenceAffineCutoff c χ
      let F : RadialSource := (referenceCompactCosine (referenceAffineCutoffForcing D c χ),
        referenceRow D (referenceCompactCosine u))
      RadialRepresentativeEq D (G F) (referenceCompactCosine u, 0) ∧
      OutputRealization D γ M₁ 0
        (referenceCompactCosine (fun r => χ r + (r - c) * deriv χ r), 0) ∧
      outputNormSquare D γ M₁ 0
        (referenceCompactCosine (fun r => χ r + (r - c) * deriv χ r), 0) ≤
        C ^ 2 * (sourceNormSquare D γ M₀ F +
          sourceNormSquare D γ M₀ (angularPartial F.1, 0)) := by
  obtain ⟨C, hC, htest⟩ := FirstNormalInverseEstimate.compactCosine_bound hD hborder hG hNormal
  refine ⟨C, hC, ?_⟩
  intro c χ hχ hc hs
  have hu : ContDiff ℝ ∞ (referenceAffineCutoff c χ) :=
    (contDiff_id.sub contDiff_const).mul hχ
  have hsupport : tsupport (referenceAffineCutoff c χ) ⊆ tsupport χ :=
    tsupport_mul_subset_right
  have huc : HasCompactSupport (referenceAffineCutoff c χ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  have hforcing : radialJacobi 4 D.w (referenceAffineCutoff c χ) =
      referenceAffineCutoffForcing D c χ :=
    funext (referenceAffineCutoff_jacobi hD.choose_spec.1.2.2.1.1 hχ c)
  have hderiv : deriv (referenceAffineCutoff c χ) =
      fun r => χ r + (r - c) * deriv χ r :=
    funext (referenceAffineCutoff_deriv hχ c)
  simpa only [referenceCompactCosineSource, hforcing, hderiv] using
    htest (referenceAffineCutoff c χ) hu huc (hsupport.trans hs)

end ContinuousFlexibility.Statements
