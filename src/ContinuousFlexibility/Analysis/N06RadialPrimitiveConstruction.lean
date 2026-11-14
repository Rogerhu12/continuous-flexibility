module

public import ContinuousFlexibility.Analysis.N06PositivePrimitiveConstruction
public import ContinuousFlexibility.Analysis.N06RadialInverseExtension

/-!
# Primitive reference bounds from physical fields and the true inverse

Ordinary physical jets of the profile and the constructed height and
slope are composed with the genuine inverse. The physical lower bound
in terms of both endpoint distances becomes the canonical quadratic
weight by the actual upper slope estimate. A smooth inverse extension
preserves these bounds through equality of germs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem N06ScalarJetTwoBound.congr_germ
    {f g : ℝ → ℝ} {x B : ℝ} (hg : N06ScalarJetTwoBound g x B)
    (he : f =ᶠ[𝓝 x] g) : N06ScalarJetTwoBound f x B := by
  apply n06_scalarJetTwoBound_iff.mpr
  intro k hk
  rw [he.iteratedDeriv_eq k]
  exact n06_scalarJetTwoBound_iff.mp hg k hk

/-- All primitive jets and pointwise lower bounds are retained by the
actual inverse extension, including at both boundary points. -/
theorem N06RadialPrimitiveJetBounds.congr_inverse
    {w H Y R R0 : ℝ → ℝ} {y B : ℝ}
    (h : N06RadialPrimitiveJetBounds w H Y R0 y B)
    (he : R =ᶠ[𝓝 y] R0) : N06RadialPrimitiveJetBounds w H Y R y B := by
  have hv : R y = R0 y := by
    simpa only [iteratedDeriv_zero] using he.iteratedDeriv_eq 0
  have hcomp (f : ℝ → ℝ) : (fun t => f (R t)) =ᶠ[𝓝 y] (fun t => f (R0 t)) :=
    he.mono fun t ht => congrArg f ht
  refine ⟨h.radius.congr_germ he, h.profile.congr_germ (hcomp w),
    h.profile_derivative.congr_germ (hcomp (deriv w)),
    h.height.congr_germ (hcomp H), h.slope.congr_germ (hcomp (deriv Y)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hv] using h.radius_lower
  · simpa only [hv] using h.profile_lower
  · simpa only [hv] using h.height_lower
  · simpa only [hv] using h.slope_lower
  · simpa only [hv] using h.angular_lower
  · simpa only [hv] using h.height_first
  · simpa only [hv] using h.height_second

/-- An upper bound for the actual coordinate slope converts the physical
two-endpoint lower bound into the canonical quadratic weight. -/
theorem n06_inverse_root_weight_lower
    {w Y R : ℝ → ℝ} {l r A y : ℝ}
    (hY : Differentiable ℝ Y) (hA : 0 < A)
    (hupper : ∀ x, deriv Y x ≤ 2 * A)
    (hYR : ∀ t, Y (R t) = t) (hl : Y l = 0) (hr : Y r = 1)
    (hy : y ∈ Icc (0 : ℝ) 1) (hR : R y ∈ Icc l r)
    (hroot : (R y - l) * (r - R y) / A ≤ deriv w (R y) / R y) :
    cylinderWeight y / (4 * A ^ 3) ≤ deriv w (R y) / R y := by
  have hleft : y ≤ 2 * A * (R y - l) := by
    simpa only [hYR y, hl, sub_zero] using
      image_sub_le_mul_sub_of_deriv_le hY hupper hR.1
  have hright : 1 - y ≤ 2 * A * (r - R y) := by
    simpa only [hYR y, hr] using
      image_sub_le_mul_sub_of_deriv_le hY hupper hR.2
  have hproduct : cylinderWeight y ≤ 4 * A ^ 2 * ((R y - l) * (r - R y)) := by
    calc
      _ ≤ (2 * A * (R y - l)) * (2 * A * (r - R y)) :=
        mul_le_mul hleft hright (sub_nonneg.mpr hy.2)
          (mul_nonneg (by positivity) (sub_nonneg.mpr hR.1))
      _ = _ := by ring
  calc
    _ ≤ (4 * A ^ 2 * ((R y - l) * (r - R y))) / (4 * A ^ 3) :=
      div_le_div_of_nonneg_right hproduct (by positivity)
    _ = (R y - l) * (r - R y) / A := by field_simp [hA.ne']
    _ ≤ _ := hroot

/-- The primitive package follows from ordinary physical jets and actual
forward coordinate bounds. The inverse is exactly `Function.invFun Y`.
The only angular lower input is the physical profile inequality involving
its two root distances. -/
theorem n06_radialPrimitiveJetBounds_of_forward
    {w H Y : ℝ → ℝ} {l r A B y : ℝ}
    (hw : ContDiff ℝ ∞ w) (hH : ContDiff ℝ ∞ H) (hY : ContDiff ℝ ∞ Y)
    (hbij : Function.Bijective Y) (hR : ContDiff ℝ ∞ (Function.invFun Y))
    (hA : 1 ≤ A) (hAB : 2 * A ≤ B)
    (hlower : 1 / A ≤ l) (hlabs : |l| ≤ A) (hrabs : |r| ≤ A)
    (hyL : Y l = 0) (hyR : Y r = 1)
    (hYbounds : ∀ x, 1 / (2 * A) ≤ deriv Y x ∧ deriv Y x ≤ 2 * A)
    (hHlower : ∀ x, 1 / A ≤ H x)
    (hHjets : ∀ x, N06ScalarJetTwoBound H x B)
    (hYjets : ∀ x, N06ScalarJetTwoBound (deriv Y) x B)
    (hwjets : ∀ x ∈ Icc l r, 1 / A ≤ w x ∧
      N06ScalarJetTwoBound w x A ∧ N06ScalarJetTwoBound (deriv w) x A)
    (hroot : ∀ x ∈ Icc l r, (x - l) * (r - x) / A ≤ deriv w x / x)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    N06RadialPrimitiveJetBounds w H Y (Function.invFun Y) y (4 * B ^ 12) := by
  let R0 : ℝ → ℝ := Function.invFun Y
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hBB : A ≤ B := by linarith
  have hB : 1 ≤ B := hA.trans hBB
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hB4 : B ≤ B ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 4)
  have hB4one : 1 ≤ B ^ 4 := one_le_pow₀ hB
  have hB12 : 0 ≤ B ^ 12 := pow_nonneg hBp.le _
  have hB4Q : B ^ 4 ≤ 4 * B ^ 12 :=
    (pow_le_pow_right₀ hB (by norm_num : 4 ≤ 12)).trans (by nlinarith)
  have hBQ : B ≤ 4 * B ^ 12 := hB4.trans hB4Q
  have hAQ : A ≤ 4 * B ^ 12 := hBB.trans hBQ
  have hYR : ∀ t, Y (R0 t) = t := Function.rightInverse_invFun hbij.2
  have hmem : R0 y ∈ Icc l r :=
    n06_inverse_mem_Icc (by positivity : 0 < 1 / (2 * A))
      (fun x => (hYbounds x).1) hYR hyL hyR hy
  have hRvalue : |R0 y| ≤ B := (n06_abs_le_of_mem_Icc hlabs hrabs hmem).trans hBB
  have hYlower : ∀ x, 1 / B ≤ deriv Y x := fun x =>
    (one_div_le_one_div_of_le (by positivity : 0 < 2 * A) hAB).trans (hYbounds x).1
  have hRjets : N06ScalarJetTwoBound R0 y (B ^ 4) :=
    n06_inverse_twoJet_bound hY hB hYlower hYR hRvalue (hYjets (R0 y)).first
  have hcompose (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
      (hfjet : N06ScalarJetTwoBound f (R0 y) B) :
      N06ScalarJetTwoBound (fun t => f (R0 t)) y (4 * B ^ 12) := by
    apply (N06ScalarJetTwoBound.comp hf hR hB4one (hfjet.mono hB4) hRjets).mono
    calc
      2 * (B ^ 4) ^ 3 = 2 * B ^ 12 := by ring
      _ ≤ _ := by nlinarith
  have hlowerQ : 1 / (4 * B ^ 12) ≤ 1 / A := one_div_le_one_div_of_le hAp hAQ
  have hrootQ : 4 * A ^ 3 ≤ 4 * B ^ 12 := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (pow_le_pow_left₀ hAp.le hBB 3).trans (pow_le_pow_right₀ hB (by norm_num))
  have hrootBound := n06_inverse_root_weight_lower (hY.differentiable (by simp)) hAp
    (fun x => (hYbounds x).2) hYR hyL hyR hy hmem (hroot (R0 y) hmem)
  refine ⟨hRjets.mono hB4Q,
    hcompose w hw ((hwjets (R0 y) hmem).2.1.mono hBB),
    hcompose (deriv w) (contDiff_infty_iff_deriv.mp hw).2
      ((hwjets (R0 y) hmem).2.2.mono hBB),
    hcompose H hH (hHjets (R0 y)),
    hcompose (deriv Y) (contDiff_infty_iff_deriv.mp hY).2 (hYjets (R0 y)),
    hlowerQ.trans (hlower.trans hmem.1),
    hlowerQ.trans (hwjets (R0 y) hmem).1,
    hlowerQ.trans (hHlower (R0 y)), ?_, ?_,
    (hHjets (R0 y)).first.trans hBQ, (hHjets (R0 y)).second.trans hBQ⟩
  · exact (one_div_le_one_div_of_le (by positivity : 0 < 2 * A)
      (hAB.trans hBQ)).trans (hYbounds (R0 y)).1
  · exact (div_le_div_of_nonneg_left (cylinderWeight_nonneg hy)
      (by positivity : 0 < 4 * A ^ 3) hrootQ).trans hrootBound

end ContinuousFlexibility.Analysis
