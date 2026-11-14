module

public import ContinuousFlexibility.Analysis.SpacesReciprocal
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# A bounded scalar representative for smooth composition

A fixed scalar cutoff preserves the original function near zero while
making every derivative globally bounded. The one order-two neighborhood
that bounds physical heights therefore works for all derivative orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

theorem spacesScalarCutoff_hasCompactSupport : HasCompactSupport spacesScalarCutoff := by
  apply HasCompactSupport.intro (K := Icc (-1 : ℝ) 1) isCompact_Icc
  intro x hx
  have h : 1 < |x| := lt_of_not_ge (fun h => hx (abs_le.mp h))
  exact spacesScalarCutoff_eq_zero ((by norm_num : (3 : ℝ) / 4 ≤ 1).trans h.le)

def spacesScalarClipped (F : ℝ → ℝ) (x : ℝ) : ℝ := spacesScalarCutoff x * F x

theorem spacesScalarClipped_contDiff {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spacesScalarClipped F) := spacesScalarCutoff_contDiff.mul hF

theorem spacesScalarClipped_zero {F : ℝ → ℝ} (hF : F 0 = 0) : spacesScalarClipped F 0 = 0 := by
  rw [spacesScalarClipped, hF, mul_zero]

theorem spacesScalarClipped_eq {F : ℝ → ℝ} {x : ℝ} (hx : |x| ≤ 1 / 2) :
    spacesScalarClipped F x = F x := by
  rw [spacesScalarClipped, spacesScalarCutoff_eq_one hx, one_mul]

theorem spacesScalarClipped_hasCompactSupport (F : ℝ → ℝ) :
    HasCompactSupport (spacesScalarClipped F) := spacesScalarCutoff_hasCompactSupport.mul_right

theorem spaces_iteratedDeriv_hasCompactSupport {F : ℝ → ℝ} (hF : HasCompactSupport F) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n F) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

theorem spaces_scalar_compact_derivative_bound {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hcompact : HasCompactSupport F) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C := by
  have hc := spaces_iteratedDeriv_hasCompactSupport hcompact n
  have hcont : Continuous (iteratedDeriv n F) := hF.continuous_iteratedDeriv n (by simp)
  obtain ⟨C, hC⟩ := (hc.abs.isCompact_range hcont.abs).bddAbove
  exact ⟨max C 0, le_max_right _ _, fun x => (hC ⟨x, rfl⟩).trans (le_max_left _ _)⟩

theorem spacesScalarClipped_derivative_bound {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n (spacesScalarClipped F) x| ≤ C :=
  spaces_scalar_compact_derivative_bound (spacesScalarClipped_contDiff hF)
    (spacesScalarClipped_hasCompactSupport F) n

theorem spaces_scalar_contDiff_iteratedDeriv {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n F) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

theorem spaces_scalar_lipschitz_of_derivative_bound {F : ℝ → ℝ}
    (hF : Differentiable ℝ F) {C : ℝ} (hbound : ∀ x, |deriv F x| ≤ C) (x y : ℝ) :
    |F x - F y| ≤ C * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => hF z) (fun z _ => by simpa only [Real.norm_eq_abs] using hbound z)
      (mem_univ y) (mem_univ x)

theorem spacesScalarClipped_derivative_lipschitz {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      |iteratedDeriv n (spacesScalarClipped F) x - iteratedDeriv n (spacesScalarClipped F) y| ≤
        C * |x - y| := by
  obtain ⟨C, hC, hbound⟩ := spacesScalarClipped_derivative_bound hF (n + 1)
  have hd := (spaces_scalar_contDiff_iteratedDeriv (spacesScalarClipped_contDiff hF) n).differentiable
    (by simp)
  refine ⟨C, hC, fun x y => spaces_scalar_lipschitz_of_derivative_bound hd ?_ x y⟩
  intro z
  simpa only [iteratedDeriv_succ] using hbound z

theorem spacesScalarClipped_linear_bound {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hzero : F 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |spacesScalarClipped F x| ≤ C * |x| := by
  obtain ⟨C, hC, hbound⟩ := spacesScalarClipped_derivative_lipschitz hF 0
  refine ⟨C, hC, fun x => ?_⟩
  simpa only [iteratedDeriv_zero, spacesScalarClipped_zero hzero, sub_zero] using hbound x 0

/-- Scalar clipping agrees with the original function throughout one fixed
neighborhood in the actual physical grading. -/
theorem spacesScalarClipped_model_neighborhood {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γ : ℝ} (hγ : 0 < γ)
    {H : SobolevModelData} (hH : IsSobolevModel D T γ H) (F : ℝ → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : H.Space, H.grading 2 u < ε → ∀ p,
      spacesScalarClipped F (H.decode u p) = F (H.decode u p) := by
  obtain ⟨ε, hε, hsmall⟩ := spaces_positive_denominator_neighborhood hT hγ hH
  exact ⟨ε, hε, fun u hu p => spacesScalarClipped_eq (hsmall u hu p).1.le⟩

end ContinuousFlexibility.Statements
