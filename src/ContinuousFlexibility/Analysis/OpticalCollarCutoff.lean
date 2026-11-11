import ContinuousFlexibility.Analysis.ReturnCorrectionCutoff
import ContinuousFlexibility.Analysis.N01ReferenceOpticalCollars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Cutoffs supported on quantitatively positive optical collars

The actual interpolation cutoff is the same fixed smooth transition,
rescaled so that its derivative is supported on the selected optical
collar. All orders have uniform inverse-width bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem smoothTransition_iteratedDeriv_uniform_bound (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, |iteratedDeriv n Real.smoothTransition r| ≤ K := by
  cases n with
  | zero =>
      refine ⟨1, zero_lt_one, fun r => ?_⟩
      simpa only [iteratedDeriv_zero, abs_of_nonneg (Real.smoothTransition.nonneg r)] using
        Real.smoothTransition.le_one r
  | succ n =>
      have hc : Continuous (iteratedDeriv (n + 1) Real.smoothTransition) :=
        (Real.smoothTransition.contDiff (n := ⊤)).continuous_iteratedDeriv (n + 1) (by simp)
      obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (hc.continuousOn (s := Icc (-1 : ℝ) 2))
      refine ⟨max B 1, zero_lt_one.trans_le (le_max_right _ _), fun r => ?_⟩
      by_cases hr : r ∈ Icc (-1 : ℝ) 2
      · have hrB : |iteratedDeriv (n + 1) Real.smoothTransition r| ≤ B := by
          simpa only [Real.norm_eq_abs] using hB r hr
        exact hrB.trans (le_max_left _ _)
      · have he : Real.smoothTransition =ᶠ[𝓝 r] (fun _ => if r < 0 then 0 else 1) := by
          by_cases hleft : r < 0
          · filter_upwards [Iio_mem_nhds hleft] with s hs
            rw [if_pos hleft]
            exact Real.smoothTransition.zero_of_nonpos hs.le
          · have hright : 1 < r := by
              by_contra hn
              apply hr
              constructor <;> linarith
            filter_upwards [Ioi_mem_nhds hright] with s hs
            rw [if_neg hleft]
            exact Real.smoothTransition.one_of_one_le hs.le
        rw [Filter.EventuallyEq.iteratedDeriv_eq (n + 1) he, iteratedDeriv_const]
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, abs_zero]
        exact zero_le_one.trans (le_max_right _ _)

/-- The existing fixed cutoff, translated and scaled to a selected
closed optical collar. -/
def returnOpticalCutoff (x δ : ℝ) : ℝ → ℝ :=
  returnCorrectionCutoff (x - 3 * δ) (x + 3 * δ)

theorem returnOpticalCutoff_contDiff (x δ : ℝ) :
    ContDiff ℝ ∞ (returnOpticalCutoff x δ) :=
  returnCorrectionCutoff_contDiff _ _

theorem returnOpticalCutoff_mem_Icc (x δ r : ℝ) :
    returnOpticalCutoff x δ r ∈ Icc (0 : ℝ) 1 :=
  returnCorrectionCutoff_mem_Icc _ _ _

theorem returnOpticalCutoff_affine (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    returnOpticalCutoff x δ =
      fun r => Real.smoothTransition ((2 * δ)⁻¹ * (r + (δ - x))) := by
  funext r
  unfold returnOpticalCutoff returnCorrectionCutoff
  congr 1
  field_simp [hδ.ne']
  ring

theorem returnOpticalCutoff_deriv_support_subset (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Function.support (deriv (returnOpticalCutoff x δ)) ⊆ Icc (x - δ) (x + δ) := by
  have hlh : x - 3 * δ < x + 3 * δ := by linarith
  have h := returnCorrectionCutoff_deriv_support_subset hlh
  have hl : (2 * (x - 3 * δ) + (x + 3 * δ)) / 3 = x - δ := by ring
  have hr : ((x - 3 * δ) + 2 * (x + 3 * δ)) / 3 = x + δ := by ring
  simpa only [returnOpticalCutoff, hl, hr] using h

theorem returnOpticalCutoff_eventually_zero {x δ r : ℝ} (hδ : 0 < δ)
    (hr : r < x - δ) :
    returnOpticalCutoff x δ =ᶠ[𝓝 r] fun _ => 0 := by
  apply returnCorrectionCutoff_eventually_zero (by linarith)
  linarith

theorem returnOpticalCutoff_eventually_one {x δ r : ℝ} (hδ : 0 < δ)
    (hr : x + δ < r) :
    returnOpticalCutoff x δ =ᶠ[𝓝 r] fun _ => 1 := by
  apply returnCorrectionCutoff_eventually_one (by linarith)
  linarith

/-- The derivative bound is uniform in the center and collar width. -/
theorem returnOpticalCutoff_iteratedDeriv_bound (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x δ : ℝ, 0 < δ → ∀ r : ℝ,
      |iteratedDeriv n (returnOpticalCutoff x δ) r| ≤ K * (δ⁻¹) ^ n := by
  obtain ⟨K, hK, hbound⟩ := smoothTransition_iteratedDeriv_uniform_bound n
  refine ⟨K, hK, fun x δ hδ r => ?_⟩
  have hformula : iteratedDeriv n (returnOpticalCutoff x δ) r =
      ((2 * δ)⁻¹) ^ n * iteratedDeriv n Real.smoothTransition
        ((2 * δ)⁻¹ * (r + (δ - x))) := by
    rw [returnOpticalCutoff_affine x hδ]
    let f : ℝ → ℝ := fun y => Real.smoothTransition ((2 * δ)⁻¹ * y)
    have hshift : iteratedDeriv n (fun y => f (y + (δ - x))) r =
        iteratedDeriv n f (r + (δ - x)) :=
      congrArg (fun g : ℝ → ℝ => g r) (iteratedDeriv_comp_add_const n f (δ - x))
    have hscale : iteratedDeriv n f (r + (δ - x)) =
        ((2 * δ)⁻¹) ^ n * iteratedDeriv n Real.smoothTransition
          ((2 * δ)⁻¹ * (r + (δ - x))) :=
      congrArg (fun g : ℝ → ℝ => g (r + (δ - x)))
        (iteratedDeriv_comp_const_mul
          (Real.smoothTransition.contDiff (n := (n : ℕ∞))) ((2 * δ)⁻¹))
    exact hshift.trans hscale
  have hc0 : 0 ≤ (2 * δ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hcd : (2 * δ)⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ (by linarith : 0 < 2 * δ) hδ).mpr (by linarith)
  rw [hformula, abs_mul, abs_of_nonneg (pow_nonneg hc0 n)]
  calc
    _ ≤ ((2 * δ)⁻¹) ^ n * K :=
      mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg hc0 n)
    _ ≤ (δ⁻¹) ^ n * K :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hcd n) hK.le
    _ = _ := mul_comm _ _

/-- The explicit optical collar loses only a fixed radial coefficient
power, uniformly in the component. -/
theorem opticalCollar_width_inv_bound
    {E K A B L R : ℝ} (hE : 1 ≤ E) (hK : 0 < K) (hA : 0 ≤ A)
    (hL : 0 < L) (hLR : L ≤ R) :
    (((E ^ (-B) / L) ^ 2) / (4 * (K * E ^ A + 1)))⁻¹ ≤
      (4 * (K + 1) * R ^ 2) * E ^ (A + 2 * B) := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hEA : 1 ≤ E ^ A := Real.one_le_rpow hE hA
  have hEB : 0 < E ^ B := Real.rpow_pos_of_pos hE0 _
  have hR : 0 < R := hL.trans_le hLR
  have hE2B : E ^ (2 * B) = (E ^ B) ^ 2 := by
    rw [mul_comm (2 : ℝ) B]
    exact Real.rpow_mul_natCast hE0.le B 2
  have heq : (((E ^ (-B) / L) ^ 2) / (4 * (K * E ^ A + 1)))⁻¹ =
      4 * (K * E ^ A + 1) * L ^ 2 * E ^ (2 * B) := by
    rw [Real.rpow_neg hE0.le, hE2B]
    field_simp [hL.ne', hEB.ne'] <;> ring
  rw [heq, Real.rpow_add hE0]
  have hcoef : K * E ^ A + 1 ≤ (K + 1) * E ^ A := by nlinarith
  have hLsq : L ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hL.le hR.le).mpr hLR
  calc
    _ ≤ 4 * ((K + 1) * E ^ A) * R ^ 2 * E ^ (2 * B) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hLsq
          (sq_nonneg _) (by positivity))
        (Real.rpow_nonneg hE0.le _)
    _ = _ := by ring

end ContinuousFlexibility.Analysis
