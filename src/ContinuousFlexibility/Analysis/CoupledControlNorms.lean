import ContinuousFlexibility.Analysis.CoupledControlAlgebra
import ContinuousFlexibility.Analysis.SolveStateSpaces

/-!
# Base control norms and continuous restriction

The diagonal lower bound controls the stored inverse on the actual control
Banach space.  The continuous weighted restriction has a bound by one
finite circle grading, obtained from the original seminorm topology.
-/

noncomputable section

open scoped NNReal ENNReal

namespace ContinuousFlexibility.Analysis

section BanachTarget

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear map to a Banach norm is bounded by one member of
an increasing defining grading. No norm is imposed on its source. -/
theorem coupled_exists_grading_bound
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (ht : WithSeminorms p)
    (L : E →L[ℝ] F) :
    ∃ b : ℕ, ∃ C : ℝ≥0, ∀ x, ‖L x‖ ≤ C * p b x := by
  classical
  let q : Seminorm ℝ E := (normSeminorm ℝ F).comp L.toLinearMap
  have hq : Continuous q := L.continuous.norm
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous ht q hq
  have hsup : s.sup p ≤ p (s.sup id) :=
    Finset.sup_le (fun i hi => hp (Finset.le_sup (f := id) hi))
  refine ⟨s.sup id, C, fun x => ?_⟩
  have hCx : ‖L x‖ ≤ (C : ℝ) * (s.sup p) x := hC x
  exact hCx.trans (mul_le_mul_of_nonneg_left (hsup x) C.coe_nonneg)

theorem coupled_continuousLinear_to_norm_isTame
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (ht : WithSeminorms p)
    (L : E →L[ℝ] F) :
    ∃ b : ℕ, IsTameLinear p (fun _ => normSeminorm ℝ F) L.toLinearMap 0 b := by
  obtain ⟨b, C, hC⟩ := coupled_exists_grading_bound hp ht L
  refine ⟨b, fun n hn => ⟨C, fun x => ?_⟩⟩
  change ‖L x‖ ≤ (C : ℝ) * p (n + 0) x
  exact (hC x).trans (mul_le_mul_of_nonneg_left (hp (by omega) x) C.coe_nonneg)

end BanachTarget

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

variable {S : PhysicalSpacesData}

/-- The coordinate identities and the frozen lower bound force the actual
stored Banach inverse to have norm at most two. -/
theorem controlJInverse_norm_le_two
    (B : ControlColumnData S) (z : AnnularState S × ℝ)
    (hdiag : ∀ u m, B.J z u m = B.diagonal z m * u m)
    (hJ : ∀ u, B.J z (B.JInverse z u) = u)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|) :
    ‖B.JInverse z‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  have hnorm : ‖B.JInverse z u‖ ≤ ‖(2 : ℝ) • u‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro m
    rw [controlJInverse_apply_of_diagonal B z hdiag hJ hlo u m]
    have hinv : |(B.diagonal z m)⁻¹| ≤ 2 := by
      rw [abs_inv, ← one_div]
      calc
        1 / |B.diagonal z m| ≤ 1 / (1 / 2 : ℝ) :=
          one_div_le_one_div_of_le (by norm_num) (hlo m)
        _ = 2 := by norm_num
    simpa only [Real.norm_eq_abs, abs_mul, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      mul_le_mul_of_nonneg_right hinv (abs_nonneg (u m))
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hnorm

theorem controlRestriction_isTame (B : ControlColumnData S) :
    ∃ b : ℕ, IsTameLinear (S.circle (3 / 4 : ℝ)).grading controlGrading
      B.restriction.toLinearMap 0 b :=
  coupled_continuousLinear_to_norm_isTame (gradedSeminorm_monotone _ _)
    (withSeminorms_graded _ _) B.restriction

theorem controlRestriction_grading_bound (B : ControlColumnData S) :
    ∃ b : ℕ, ∃ C : ℝ≥0, ∀ u,
      ‖B.restriction u‖ ≤ C * (S.circle (3 / 4 : ℝ)).grading b u :=
  coupled_exists_grading_bound (gradedSeminorm_monotone _ _)
    (withSeminorms_graded _ _) B.restriction

end ContinuousFlexibility.Statements
