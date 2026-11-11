import ContinuousFlexibility.Analysis.CoupledConstantCircle
import ContinuousFlexibility.Analysis.CoupledInverseContinuity

/-!
# The diagonal inverse on the closed constant-circle space

The forward operator is the actual mean of the circle control derivative.
Its reciprocal acts on the original closed constant-circle subspace. The
weighted restriction identities prove both inverse identities there, and
the same factor two controls every order. Hamilton's inverse-family theorem
therefore needs no separate assumption of parameter continuity in an
operator-norm topology.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {T : MaterialData} {S : PhysicalSpacesData}

def coupledControlCircleOperator
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : AnnularState S × ℝ) :
    CoupledConstantCircle hS →L[ℝ] CoupledConstantCircle hS :=
  (coupledConstantCircleProjection hS).comp
    ((B.circleColumn z).comp (coupledConstantCircleSubmodule hS).subtypeL)

theorem coupledControlCircleOperator_val
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : AnnularState S × ℝ) (u : CoupledConstantCircle hS) :
    (coupledControlCircleOperator hS B z u).val =
      circleAngularMeanProjection hS (B.circleColumn z u.val) := by
  rw [coupledControlCircleOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    coupledConstantCircleProjection_val]

/-- The same reciprocal diagonal, made total by zero outside its numerical
lower-bound domain. -/
def coupledControlCircleInverse
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : AnnularState S × ℝ) :
    CoupledConstantCircle hS →L[ℝ] CoupledConstantCircle hS := by
  classical
  exact if hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m| then
    (coupledConstantCircleInverse hS (B.diagonal z) hlo).comp
      (coupledConstantCircleSubmodule hS).subtypeL
    else 0

theorem coupledControlCircleInverse_val
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : AnnularState S × ℝ)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|) (u : CoupledConstantCircle hS) :
    (coupledControlCircleInverse hS B z u).val =
      coupledInverseControlLift hS (B.diagonal z) hlo u.val := by
  rw [coupledControlCircleInverse, dif_pos hlo, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, coupledConstantCircleInverse_val]

theorem coupledControlCircleInverse_grading_le
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : AnnularState S × ℝ)
    (n : ℕ) (u : CoupledConstantCircle hS) :
    coupledConstantCircleGrading hS n (coupledControlCircleInverse hS B z u) ≤
      2 * coupledConstantCircleGrading hS n u := by
  classical
  by_cases hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|
  · change (S.circle (3 / 4 : ℝ)).grading n (coupledControlCircleInverse hS B z u).val ≤
      2 * (S.circle (3 / 4 : ℝ)).grading n u.val
    rw [coupledControlCircleInverse_val hS B z hlo]
    exact coupledInverseControlLift_grading_le hS (B.diagonal z) hlo n u.val
  · rw [coupledControlCircleInverse, dif_neg hlo, ContinuousLinearMap.zero_apply, map_zero]
    exact mul_nonneg (by norm_num) (apply_nonneg _ _)

theorem controlRestriction_angularMeanProjection
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m)) (u : CircleSpace S) :
    B.restriction (circleAngularMeanProjection hS u) = B.restriction u := by
  apply lp.ext
  funext m
  rw [hrestriction, hrestriction]
  have hm : (S.circle (3 / 4 : ℝ)).decode (circleAngularMeanProjection hS u) m =
      (fun _ : ℝ => angularMean ((S.circle (3 / 4 : ℝ)).decode u m)) :=
    funext (circleAngularMeanProjection_decode hS u m)
  rw [hm, coupled_angularMean_const]

theorem coupledControlCircleOperator_restriction
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : AnnularState S × ℝ)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hcolumn : ∀ u, B.restriction (B.circleColumn z u) = B.J z (B.restriction u))
    (u : CoupledConstantCircle hS) :
    B.restriction (coupledControlCircleOperator hS B z u).val = B.J z (B.restriction u.val) := by
  rw [coupledControlCircleOperator_val,
    controlRestriction_angularMeanProjection hS B hrestriction]
  exact hcolumn u.val

theorem coupledControlCircleInverse_restriction
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : AnnularState S × ℝ)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hdiag : ∀ u m, B.J z u m = B.diagonal z m * u m)
    (hJ : ∀ u, B.J z (B.JInverse z u) = u)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|) (u : CoupledConstantCircle hS) :
    B.restriction (coupledControlCircleInverse hS B z u).val =
      B.JInverse z (B.restriction u.val) := by
  rw [coupledControlCircleInverse_val hS B z hlo]
  exact coupledInverseControlLift_restriction hS B z hrestriction hdiag hJ hlo u.val

theorem coupledControlCircleInverse_left
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : AnnularState S × ℝ)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    (hcolumn : ∀ u, B.restriction (B.circleColumn z u) = B.J z (B.restriction u))
    (hdiag : ∀ u m, B.J z u m = B.diagonal z m * u m)
    (hJ : ∀ u, B.JInverse z (B.J z u) = u ∧ B.J z (B.JInverse z u) = u)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|) (u : CoupledConstantCircle hS) :
    coupledControlCircleInverse hS B z (coupledControlCircleOperator hS B z u) = u := by
  apply Subtype.ext
  apply controlRestriction_injective_on_constants hS B hrestriction hH
    (coupledConstantCircle_constant hS _) (coupledConstantCircle_constant hS u)
  rw [coupledControlCircleInverse_restriction hS B z hrestriction hdiag
      (fun v => (hJ v).2) hlo,
    coupledControlCircleOperator_restriction hS B z hrestriction hcolumn]
  exact (hJ _).1

theorem coupledControlCircleInverse_right
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : AnnularState S × ℝ)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    (hcolumn : ∀ u, B.restriction (B.circleColumn z u) = B.J z (B.restriction u))
    (hdiag : ∀ u m, B.J z u m = B.diagonal z m * u m)
    (hJ : ∀ u, B.JInverse z (B.J z u) = u ∧ B.J z (B.JInverse z u) = u)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|) (u : CoupledConstantCircle hS) :
    coupledControlCircleOperator hS B z (coupledControlCircleInverse hS B z u) = u := by
  apply Subtype.ext
  apply controlRestriction_injective_on_constants hS B hrestriction hH
    (coupledConstantCircle_constant hS _) (coupledConstantCircle_constant hS u)
  rw [coupledControlCircleOperator_restriction hS B z hrestriction hcolumn,
    coupledControlCircleInverse_restriction hS B z hrestriction hdiag
      (fun v => (hJ v).2) hlo]
  exact (hJ _).2

section ParameterFamily

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-- The inverse has a uniform zero-loss linear-family estimate for any
parameter grading, since its every-order bound is the same factor two. -/
theorem coupledControlCircleInverse_linearFamilyTame
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : X → AnnularState S × ℝ)
    (p : ℕ → Seminorm ℝ X) (U : Set X) :
    LinearFamilyTame p (coupledConstantCircleGrading hS) (coupledConstantCircleGrading hS)
      U (fun x => (coupledControlCircleInverse hS B (z x)).toLinearMap) := by
  refine ⟨0, 0, fun n _ => ⟨2, by norm_num, fun x _ u => ?_⟩⟩
  have hb := coupledControlCircleInverse_grading_le hS B (z x) n u
  have hn : 0 ≤ (1 + p n x) * coupledConstantCircleGrading hS 0 u :=
    mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _)
  simpa only [Nat.add_zero] using hb.trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hn) (by norm_num : (0 : ℝ) ≤ 2))

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Smoothness of the actual forward family and its exact identities
upgrade the constructed inverse to a smooth tame family. -/
theorem coupledControlCircleInverse_smoothTameOn
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : X → AnnularState S × ℝ)
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p) (htp : WithSeminorms p)
    {U : Set X} (hU : IsOpen U)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    (hcolumn : ∀ x ∈ U, ∀ u,
      B.restriction (B.circleColumn (z x) u) = B.J (z x) (B.restriction u))
    (hdiag : ∀ x ∈ U, ∀ u m, B.J (z x) u m = B.diagonal (z x) m * u m)
    (hJ : ∀ x ∈ U, ∀ u,
      B.JInverse (z x) (B.J (z x) u) = u ∧ B.J (z x) (B.JInverse (z x) u) = u)
    (hlo : ∀ x ∈ U, ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal (z x) m|)
    (hforward : SmoothTameOn (pairGrading p (coupledConstantCircleGrading hS))
      (coupledConstantCircleGrading hS) (U ×ˢ univ)
      (fun v : X × CoupledConstantCircle hS => coupledControlCircleOperator hS B (z v.1) v.2)) :
    SmoothTameOn (pairGrading p (coupledConstantCircleGrading hS))
      (coupledConstantCircleGrading hS) (U ×ˢ univ)
      (fun v : X × CoupledConstantCircle hS => coupledControlCircleInverse hS B (z v.1) v.2) := by
  exact coupled_smoothTameOn_inverseFamily_of_tame hp
    (coupledConstantCircleGrading_monotone hS) (coupledConstantCircleGrading_monotone hS)
    htp (coupledConstantCircleGrading_withSeminorms hS)
    (coupledConstantCircleGrading_withSeminorms hS) hU
    (fun x => coupledControlCircleOperator hS B (z x))
    (fun x => (coupledControlCircleInverse hS B (z x)).toLinearMap) hforward
    (fun x hx u => coupledControlCircleInverse_left hS B (z x) hrestriction hH
      (hcolumn x hx) (hdiag x hx) (hJ x hx) (hlo x hx) u)
    (fun x hx u => coupledControlCircleInverse_right hS B (z x) hrestriction hH
      (hcolumn x hx) (hdiag x hx) (hJ x hx) (hlo x hx) u)
    (coupledControlCircleInverse_linearFamilyTame hS B z p U)

end ParameterFamily

end ContinuousFlexibility.Statements
