import ContinuousFlexibility.Analysis.RootCompositionZeroOrder
import ContinuousFlexibility.Analysis.RootChartSymmetry
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform small travel from a true first-derivative bound

The genuine divided root coefficient is bounded by the first derivative
of its smooth input. Angular periodicity extends the estimate from one
fixed period to every angle. A single radius, selected before the input
function, then bounds the root travel strictly below any positive target.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem abs_rootOddCoefficient_le_of_csBound_one
    {G : ℝ × ℝ × ℝ → ℝ} {M x : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ r ζ θ, G (r, ζ, θ + Real.pi) = G (r, ζ, θ) + Real.pi)
    (hB : CSBound 1
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G M)
    (hx : x ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    |rootOddCoefficient G (x, θ)| ≤ M := by
  obtain ⟨t, ht, he⟩ :=
    (rootOddCoefficient_periodic hperiod x).exists_mem_Ico₀ Real.pi_pos θ
  change rootOddCoefficient G (x, θ) = rootOddCoefficient G (x, t) at he
  rw [he]
  have ht' : t ∈ Icc (-Real.pi) Real.pi :=
    ⟨(neg_nonpos.mpr Real.pi_pos.le).trans ht.1, ht.2.le⟩
  have hb := (csBound_rootOdd_zero hG hB).norm_le ⟨hx, ht'⟩
  simpa only [rootOddCoefficient, abs_neg, Real.norm_eq_abs] using hb

theorem abs_rootTravel_le_linear_of_csBound_one
    {G : ℝ × ℝ × ℝ → ℝ} {M x : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ r ζ θ, G (r, ζ, θ + Real.pi) = G (r, ζ, θ) + Real.pi)
    (hB : CSBound 1
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G M)
    (hx : x ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    |x ^ (3 / 2 : ℝ) * rootOddCoefficient G (x, θ)| ≤ M * x := by
  have hχ := abs_rootOddCoefficient_le_of_csBound_one hG hperiod hB hx θ
  have hM : 0 ≤ M := (abs_nonneg _).trans hχ
  have hpow : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx.1 _
  calc
    |x ^ (3 / 2 : ℝ) * rootOddCoefficient G (x, θ)| =
        x ^ (3 / 2 : ℝ) * |rootOddCoefficient G (x, θ)| := by
      rw [abs_mul, abs_of_nonneg hpow]
    _ ≤ x ^ (3 / 2 : ℝ) * M := mul_le_mul_of_nonneg_left hχ hpow
    _ ≤ x * M := mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_le_one hx.1 hx.2 (by norm_num)) hM
    _ = M * x := mul_comm _ _

/-- The radius is chosen before the entire smooth family. In applications
the same bound M is first obtained for all states in one neighborhood. -/
theorem exists_rootTravel_uniform_small_band
    {η A M : ℝ} (hη : 0 < η) (hηone : η ≤ 1) (hA : 0 < A) (hM : 0 ≤ M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ η ∧
      ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
        (∀ r ζ θ, G (r, ζ, θ + Real.pi) = G (r, ζ, θ) + Real.pi) →
        CSBound 1
          (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G M →
        ∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ,
          x ^ (3 / 2 : ℝ) * rootOddCoefficient G (x, θ) < A := by
  have hMone : 0 < M + 1 := by linarith
  let ρ := min η (A / (2 * (M + 1)))
  have hρ : 0 < ρ := lt_min hη (div_pos hA (mul_pos (by norm_num) hMone))
  have hρη : ρ ≤ η := min_le_left _ _
  have hρA : (M + 1) * ρ ≤ A / 2 := by
    calc
      (M + 1) * ρ ≤ (M + 1) * (A / (2 * (M + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hMone.le
      _ = A / 2 := by field_simp [hMone.ne'] <;> ring
  refine ⟨ρ, hρ, hρη, ?_⟩
  intro G hG hperiod hB x hx θ
  have hlinear := abs_rootTravel_le_linear_of_csBound_one hG hperiod hB
    ⟨hx.1, hx.2.trans (hρη.trans hηone)⟩ θ
  calc
    x ^ (3 / 2 : ℝ) * rootOddCoefficient G (x, θ) ≤
        |x ^ (3 / 2 : ℝ) * rootOddCoefficient G (x, θ)| := le_abs_self _
    _ ≤ M * x := hlinear
    _ ≤ (M + 1) * x := mul_le_mul_of_nonneg_right (by linarith) hx.1
    _ ≤ (M + 1) * ρ := mul_le_mul_of_nonneg_left hx.2 hMone.le
    _ ≤ A / 2 := hρA
    _ < A := by linarith

end ContinuousFlexibility.Analysis
