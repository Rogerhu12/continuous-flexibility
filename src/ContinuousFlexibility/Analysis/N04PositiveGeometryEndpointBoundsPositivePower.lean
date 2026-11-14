import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryKernelBounds
import ContinuousFlexibility.Analysis.PositivePowerPolynomialMaterialJets

/-!
# Positive powers preserve the finite root word budget

The ordinary outer derivatives are bounded explicitly by the value and
its reciprocal. The genuine composition formula then preserves the
original angular reserve and the complete positive-parameter height.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_positivePower_outer_prefix (γ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ, ∀ M : ℝ, 1 ≤ M →
      ∀ x : ℝ, 0 < x → x ≤ M → x⁻¹ ≤ M → ∀ n : ℕ, n ≤ N →
        ‖iteratedFDeriv ℝ n (fun y : ℝ => y ^ γ) x‖ ≤ C * M ^ degree := by
  obtain ⟨C, hC, hcoeff⟩ := exists_rpowJetCoefficient_bound γ N
  let degree : ℕ := ⌈|γ| + (N : ℝ)⌉₊
  refine ⟨C, hC, degree, ?_⟩
  intro M hM x hx hvalue hinv n hn
  have hexp : |γ - (n : ℝ)| ≤ (degree : ℝ) := by
    calc
      _ ≤ |γ| + |(n : ℝ)| := abs_sub _ _
      _ = |γ| + (n : ℝ) := by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
      _ ≤ |γ| + (N : ℝ) :=
        add_le_add le_rfl (show (n : ℝ) ≤ (N : ℝ) by exact_mod_cast hn)
      _ ≤ (degree : ℝ) := Nat.le_ceil _
  have hpower : x ^ (γ - (n : ℝ)) ≤ M ^ degree := by
    calc
      _ ≤ M ^ |γ - (n : ℝ)| :=
        positive_rpow_le_of_value_inverse_bounds hx hvalue hinv _
      _ ≤ M ^ (degree : ℝ) := Real.rpow_le_rpow_of_exponent_le hM hexp
      _ = M ^ degree := Real.rpow_natCast _ _
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_rpow_eq,
    norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  exact mul_le_mul (hcoeff n hn) hpower (Real.rpow_nonneg hx.le _)
    (zero_le_one.trans hC)

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

def n04PositiveGeometry_positivePower_joint
    {U : Set E} {f : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ univ) f) (γ : ℝ)
    (hpos : ∀ y ∈ U ×ˢ (univ : Set ℝ), 0 < f y) :
    SmoothDirections (U ×ˢ univ) (fun y => f y ^ γ) :=
  smoothDirections_contDiff_comp J isOpen_Ioi
    (fun _ hx => (contDiffAt_id.rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt) hpos

theorem n04PositiveGeometry_boundaryWord_positivePower
    (γ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ,
      ∀ {U : Set E} {f : E × ℝ → ℝ},
      ∀ J : SmoothDirections (U ×ˢ univ) f,
      ∀ Q : SmoothDirections (U ×ˢ univ) (fun y => f y ^ γ),
      (∀ y ∈ U ×ˢ (univ : Set ℝ), 0 < f y) →
      ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift,
      N04BoundaryWordBounds J K s d x θ P M H t shift →
      (f (x, θ))⁻¹ ≤ M →
      N04BoundaryWordBounds Q K s d x θ P
        (C * M ^ degree) H t shift := by
  obtain ⟨C₀, hC₀, degree, houter⟩ :=
    n04PositiveGeometry_positivePower_outer_prefix γ N
  obtain ⟨C, hC, hkernel⟩ :=
    n04PositiveGeometry_boundaryKernel_polynomial_bound (E := E) (F := ℝ) (G := ℝ)
      N degree C₀ hC₀
  refine ⟨C, hC, degree + 2 * N, ?_⟩
  intro U f J Q hpos K s d hN x hx θ P M H t hM hH hHM ht shift hJ hinv
  have hvalue : f (x, θ) ≤ M :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hJ.value hx)
  exact hkernel (g := fun y : ℝ => y ^ γ) J Q isOpen_Ioi
    (fun _ hy => (contDiffAt_id.rpow_const_of_ne (ne_of_gt hy)).contDiffWithinAt)
    hpos K s d hN x hx θ P M H t hM hH hHM ht shift hJ
    (fun n hn => houter M hM (f (x, θ)) (hpos _ ⟨hx, mem_univ _⟩) hvalue hinv n hn)

end ContinuousFlexibility.Analysis
