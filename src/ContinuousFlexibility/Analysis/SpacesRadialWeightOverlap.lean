module

public import ContinuousFlexibility.Analysis.SpacesRadialOverlap
public import ContinuousFlexibility.Analysis.MaterialLocalComparison

/-!
# Weighted localization and gluing estimates

The bounded logarithmic material derivative compares `M` at the center
and throughout a fixed-width cell. Combining this comparison with the
actual support and derivative bounds of the radial cutoffs controls the
square sum of every weighted localization or gluing multiplier.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Function MeasureTheory
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

include hT

/-- A single logarithmic derivative bound works on every material window. -/
theorem spaces_material_M_window_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c → ∀ (R : ℝ), 0 ≤ R →
      ∀ x y : ℝ, |x - y| ≤ R →
        T.M (T.radius x) ^ c ≤ Real.exp (c * C * R) * T.M (T.radius y) ^ c := by
  obtain ⟨C, hC, hdiff, hbound⟩ := material_M_log_derivative_bound hT
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hT
  have hp (x : ℝ) : 0 < T.M (T.radius x) :=
    zero_lt_one.trans_le (hpos _ (hinside x).1).2.2.2
  refine ⟨C, hC, fun c hc R _ x y hxy => ?_⟩
  have hb : |Real.log (T.M (T.radius x)) - Real.log (T.M (T.radius y))| ≤ C * |x - y| := by
    simpa only [Real.norm_eq_abs] using
      (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun z _ => hdiff z) (fun z _ => by simpa only [Real.norm_eq_abs] using hbound z)
        (mem_univ y) (mem_univ x)
  have hlog : Real.log (T.M (T.radius x)) ≤ Real.log (T.M (T.radius y)) + C * R := by
    have hh := (le_abs_self _).trans (hb.trans (mul_le_mul_of_nonneg_left hxy hC))
    linarith only [hh]
  calc
    T.M (T.radius x) ^ c = Real.exp (Real.log (T.M (T.radius x)) * c) := by
      rw [Real.exp_mul, Real.exp_log (hp x)]
    _ ≤ Real.exp ((Real.log (T.M (T.radius y)) + C * R) * c) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlog hc)
    _ = Real.exp (c * C * R) * T.M (T.radius y) ^ c := by
      rw [add_mul, Real.exp_add, Real.exp_mul, Real.exp_log (hp y)]
      rw [show C * R * c = c * C * R by ring, mul_comm]

theorem spaces_material_M_pos (x : ℝ) : 0 < T.M (T.radius x) := by
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hT
  exact zero_lt_one.trans_le (hpos _ (hinside x).1).2.2.2

/-- Natural powers of the material weight have uniformly bounded ratios
on the fixed width-two windows used by both cutoff families. -/
theorem spaces_material_M_pow_ratio_bound (c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : ℝ, |x - y| ≤ 2 →
      T.M (T.radius x) ^ c / T.M (T.radius y) ^ c ≤ K := by
  obtain ⟨C, hC, hb⟩ := spaces_material_M_window_comparison hT
  refine ⟨Real.exp ((c : ℝ) * C * 2), (Real.exp_pos _).le, fun x y hxy => ?_⟩
  apply (div_le_iff₀ (pow_pos (spaces_material_M_pos hT y) c)).mpr
  simpa only [Real.rpow_natCast] using hb c (by positivity) 2 (by norm_num) x y hxy

private theorem spaces_weight_ratio_overlap (c : ℕ) {f : ℤ → ℝ → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ n x, |f n x| ≤ B)
    (hs : ∀ n, support (f n) ⊆ Icc ((n : ℝ) - 2) (n + 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℤ) (x : ℝ),
      ∑ n ∈ s, (f n x * (T.M (T.radius n) ^ c / T.M (T.radius x) ^ c)) ^ 2 ≤ C ^ 2 := by
  obtain ⟨K, hK, hb⟩ := spaces_material_M_pow_ratio_bound hT c
  let g : ℤ → ℝ → ℝ := fun n x => f n x * (T.M (T.radius n) ^ c / T.M (T.radius x) ^ c)
  have hg (n : ℤ) (x : ℝ) : |g n x| ≤ B * K := by
    by_cases hz : f n x = 0
    · simp only [g, hz, zero_mul, abs_zero]
      positivity
    · have hx := hs n hz
      have hd : |(n : ℝ) - x| ≤ 2 := abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
      dsimp only [g]
      rw [abs_mul, abs_of_nonneg (div_nonneg (pow_nonneg (spaces_material_M_pos hT n).le c)
        (pow_nonneg (spaces_material_M_pos hT x).le c))]
      exact mul_le_mul (hf n x) (hb n x hd)
        (div_nonneg (pow_nonneg (spaces_material_M_pos hT n).le c)
          (pow_nonneg (spaces_material_M_pos hT x).le c)) hB
  have hgs (n : ℤ) : support (g n) ⊆ Icc ((n : ℝ) - 2) (n + 2) := by
    intro x hx
    apply hs n
    intro hz
    exact hx (by simp only [g, hz, zero_mul])
  exact ⟨5 * (B * K), by positivity,
    spaces_radial_overlap_square_bound (mul_nonneg hB hK) hg hgs⟩

private theorem spaces_reverse_weight_ratio_overlap (c : ℕ) {f : ℤ → ℝ → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ n x, |f n x| ≤ B)
    (hs : ∀ n, support (f n) ⊆ Icc ((n : ℝ) - 2) (n + 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℤ) (x : ℝ),
      ∑ n ∈ s, (f n x * (T.M (T.radius x) ^ c / T.M (T.radius n) ^ c)) ^ 2 ≤ C ^ 2 := by
  obtain ⟨K, hK, hb⟩ := spaces_material_M_pow_ratio_bound hT c
  let g : ℤ → ℝ → ℝ := fun n x => f n x * (T.M (T.radius x) ^ c / T.M (T.radius n) ^ c)
  have hg (n : ℤ) (x : ℝ) : |g n x| ≤ B * K := by
    by_cases hz : f n x = 0
    · simp only [g, hz, zero_mul, abs_zero]
      positivity
    · have hx := hs n hz
      have hd : |x - n| ≤ 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      dsimp only [g]
      rw [abs_mul, abs_of_nonneg (div_nonneg (pow_nonneg (spaces_material_M_pos hT x).le c)
        (pow_nonneg (spaces_material_M_pos hT n).le c))]
      exact mul_le_mul (hf n x) (hb x n hd)
        (div_nonneg (pow_nonneg (spaces_material_M_pos hT x).le c)
          (pow_nonneg (spaces_material_M_pos hT n).le c)) hB
  have hgs (n : ℤ) : support (g n) ⊆ Icc ((n : ℝ) - 2) (n + 2) := by
    intro x hx
    apply hs n
    intro hz
    exact hx (by simp only [g, hz, zero_mul])
  exact ⟨5 * (B * K), by positivity,
    spaces_radial_overlap_square_bound (mul_nonneg hB hK) hg hgs⟩

/-- Analysis cutoff derivatives, with the center weight divided by the
actual weight, have a uniform square-sum estimate. -/
theorem spacesRadialPartition_weighted_derivative_overlap (a c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℤ) (x : ℝ),
      ∑ n ∈ s, (iteratedDeriv a (spacesRadialPartition n) x *
        (T.M (T.radius n) ^ c / T.M (T.radius x) ^ c)) ^ 2 ≤ C ^ 2 := by
  obtain ⟨B, hB, hb⟩ := spacesRadialPartition_derivative_bound a
  apply spaces_weight_ratio_overlap hT c hB hb
  intro n x hx
  have hs := spacesRadialPartition_derivative_support n a hx
  constructor <;> linarith [hs.1, hs.2]

/-- Synthesis envelope derivatives, with the actual weight divided by the
center weight, have a uniform square-sum estimate. -/
theorem spacesRadialEnvelope_weighted_derivative_overlap (a c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℤ) (x : ℝ),
      ∑ n ∈ s, (iteratedDeriv a (spacesRadialEnvelope n) x *
        (T.M (T.radius x) ^ c / T.M (T.radius n) ^ c)) ^ 2 ≤ C ^ 2 := by
  obtain ⟨B, hB, hb⟩ := spacesRadialEnvelope_derivative_bound a
  exact spaces_reverse_weight_ratio_overlap hT c hB hb
    (fun n => spacesRadialEnvelope_derivative_support n a)

end ContinuousFlexibility.Statements
