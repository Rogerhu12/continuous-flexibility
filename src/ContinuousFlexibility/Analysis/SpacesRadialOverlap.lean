import ContinuousFlexibility.Analysis.SpacesRadialPartition
import ContinuousFlexibility.Analysis.SpacesLpOverlap
import ContinuousFlexibility.Analysis.CylinderTestPairing

/-!
# Uniform localization bounds for all radial cutoff derivatives

Every cutoff derivative is supported in the same fixed-width interval.
At any material radius at most five of these intervals occur. The bounds
therefore give actual localization and gluing operators on the cylinder.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Function MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem spaces_iteratedDeriv_support_subset {f : ℝ → ℝ} {s : Set ℝ}
    (hs : IsClosed s) (hf : support f ⊆ s) (a : ℕ) :
    support (iteratedDeriv a f) ⊆ s := by
  intro x hx
  have hF : x ∈ support (iteratedFDeriv ℝ a f) := by
    intro hzero
    apply hx
    rw [iteratedDeriv_eq_iteratedFDeriv, hzero]
    exact zero_apply _
  exact (closure_minimal hf hs) (support_iteratedFDeriv_subset a hF)

theorem spacesRadialEnvelope_support (n : ℤ) :
    support (spacesRadialEnvelope n) ⊆ Icc ((n : ℝ) - 2) (n + 2) := by
  intro x hx
  have hm : x ∈ Ioo ((n : ℝ) - 2) (n + 2) := by
    by_contra hm
    exact hx (spacesRadialEnvelope_eq_zero n hm)
  exact ⟨hm.1.le, hm.2.le⟩

theorem spacesRadialEnvelope_hasCompactSupport (n : ℤ) :
    HasCompactSupport (spacesRadialEnvelope n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (spacesRadialEnvelope_support n)

theorem spacesRadialEnvelope_derivative_bound (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, ∀ x : ℝ,
      |iteratedDeriv a (spacesRadialEnvelope n) x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := (spacesRadialEnvelope_hasCompactSupport 0).exists_bound_iteratedFDeriv
    (spacesRadialEnvelope_contDiff 0) a
  refine ⟨C, hC, fun n x => ?_⟩
  have he : spacesRadialEnvelope n = fun y => spacesRadialEnvelope 0 (y - n) := by
    funext y
    simp only [spacesRadialEnvelope, Int.cast_zero, sub_zero, zero_add]
    congr 2
    ring
  rw [he, iteratedDeriv_comp_sub_const]
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
    hbound a le_rfl (x - n)

theorem spacesRadialEnvelope_derivative_support (n : ℤ) (a : ℕ) :
    support (iteratedDeriv a (spacesRadialEnvelope n)) ⊆ Icc ((n : ℝ) - 2) (n + 2) :=
  spaces_iteratedDeriv_support_subset isClosed_Icc (spacesRadialEnvelope_support n) a

theorem spacesRadialPartition_derivative_support (n : ℤ) (a : ℕ) :
    support (iteratedDeriv a (spacesRadialPartition n)) ⊆ Icc ((n : ℝ) - 1) (n + 1) :=
  spaces_iteratedDeriv_support_subset isClosed_Icc (spacesRadialPartition_support n) a

/-- Five integer-centered windows cover every possible nonzero cutoff. -/
theorem spaces_radial_overlap_square_bound {f : ℤ → ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ n x, |f n x| ≤ B)
    (hs : ∀ n, support (f n) ⊆ Icc ((n : ℝ) - 2) (n + 2))
    (s : Finset ℤ) (x : ℝ) : ∑ n ∈ s, f n x ^ 2 ≤ (5 * B) ^ 2 := by
  classical
  let w : Finset ℤ := Finset.Icc (⌊x⌋ - 2) (⌊x⌋ + 2)
  have hwcard : w.card = 5 := by
    change (Finset.Icc (⌊x⌋ - 2) (⌊x⌋ + 2)).card = 5
    rw [Int.card_Icc]
    omega
  have hmem (n : ℤ) (hn : f n x ≠ 0) : n ∈ w := by
    have hsx := hs n hn
    have hxlo := Int.floor_le x
    have hxhi := Int.lt_floor_add_one x
    apply Finset.mem_Icc.mpr
    constructor
    · have hcast : (⌊x⌋ : ℝ) - 2 ≤ n := by linarith [hsx.2]
      exact_mod_cast hcast
    · have hcast : (n : ℝ) < ⌊x⌋ + 3 := by linarith [hsx.1]
      have hi : n < ⌊x⌋ + 3 := by exact_mod_cast hcast
      omega
  have he : (∑ n ∈ s ∩ w, f n x ^ 2) = ∑ n ∈ s, f n x ^ 2 := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro n hns hn
    have hnw : n ∉ w := by
      intro hw
      exact hn (Finset.mem_inter.mpr ⟨hns, hw⟩)
    have hz : f n x = 0 := by
      by_contra hz
      exact hnw (hmem n hz)
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  calc
    (∑ n ∈ s, f n x ^ 2) = ∑ n ∈ s ∩ w, f n x ^ 2 := he.symm
    _ ≤ ∑ n ∈ w, f n x ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ _n ∈ w, B ^ 2 := Finset.sum_le_sum (fun n _ => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hf n x))
    _ = 5 * B ^ 2 := by rw [Finset.sum_const, hwcard]; norm_num
    _ ≤ (5 * B) ^ 2 := by nlinarith [sq_nonneg B]

theorem spacesRadialPartition_derivative_overlap (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℤ) (x : ℝ),
      ∑ n ∈ s, iteratedDeriv a (spacesRadialPartition n) x ^ 2 ≤ C ^ 2 := by
  obtain ⟨B, hB, hb⟩ := spacesRadialPartition_derivative_bound a
  refine ⟨5 * B, by positivity, fun s x => ?_⟩
  apply spaces_radial_overlap_square_bound hB hb (fun n y hy => ?_) s x
  have hs := spacesRadialPartition_derivative_support n a hy
  constructor <;> linarith [hs.1, hs.2]

theorem spacesRadialEnvelope_derivative_overlap (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℤ) (x : ℝ),
      ∑ n ∈ s, iteratedDeriv a (spacesRadialEnvelope n) x ^ 2 ≤ C ^ 2 := by
  obtain ⟨B, hB, hb⟩ := spacesRadialEnvelope_derivative_bound a
  exact ⟨5 * B, by positivity,
    spaces_radial_overlap_square_bound hB hb (fun n => spacesRadialEnvelope_derivative_support n a)⟩

end ContinuousFlexibility.Statements
