import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Scalar.SecondProduct
import ContinuousFlexibility.Scalar.Linearization
import Mathlib.Tactic.LinearCombination

/-!
# Principal coefficients from the actual operator identity

Centered quadratic tests have zero value and gradient. Their actual Hessian
therefore removes the potential and all first-order terms from the operator
identity. The resulting three tests recover the symmetric principal density

  h² / |det D F| · D F · A · (D F)ᵀ.

The identity is proved from actual derivatives. It is not an assumed
transformation rule for independent coordinate jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The quadratic form of the actual symmetric coefficient values. -/
def coefficientQuadratic (A : SymmetricCoefficients) (x v : PolarPoint) : ℝ :=
  A.a x * v.1 ^ 2 + 2 * A.b x * v.1 * v.2 + A.c x * v.2 ^ 2

/-- A true critical quadratic test isolates the principal part, including
the height factor in a conjugated test function. -/
theorem divergenceOperator_mul_sq_of_zero
    {A : SymmetricCoefficients} {h f : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x)
    (hh : ContDiffAt ℝ 2 h x) (hf : ContDiffAt ℝ 2 f x)
    (hf0 : f x = 0) :
    divergenceOperator A (fun y => h y * f y ^ 2) x =
      2 * h x * coefficientQuadratic A x
        (radialPartial f x, angularPartial f x) := by
  unfold divergenceOperator
  rw [divergence_expansion_of_coefficients ha hb hc (hh.mul (hf.pow 2))]
  simp only [radialPartial, angularPartial,
    polar_directional_mul_sq_of_zero
      (hh.differentiableAt (by norm_num)) (hf.differentiableAt (by norm_num)) hf0,
    polar_second_directional_mul_sq_of_zero hh hf hf0,
    coefficientQuadratic]
  ring

theorem divergenceOperator_sq_of_zero
    {A : SymmetricCoefficients} {f : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x)
    (hf : ContDiffAt ℝ 2 f x) (hf0 : f x = 0) :
    divergenceOperator A (fun y => f y ^ 2) x =
      2 * coefficientQuadratic A x (radialPartial f x, angularPartial f x) := by
  simpa only [one_mul, mul_one] using
    divergenceOperator_mul_sq_of_zero (h := fun _ => (1 : ℝ))
      ha hb hc contDiffAt_const hf hf0

/-- Any genuine operator identity determines its quadratic principal form.
The scalar potential is eliminated by the zero value of the test function. -/
theorem principalQuadratic_of_operator_identity
    {A B : SymmetricCoefficients} {F : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {x : PolarPoint} {V : ℝ}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x)
    (hF : ContDiffAt ℝ 2 F x) (hh : ContDiffAt ℝ 2 h x)
    (hBa : DifferentiableAt ℝ B.a (F x))
    (hBb : DifferentiableAt ℝ B.b (F x))
    (hBc : DifferentiableAt ℝ B.c (F x))
    (hid : ∀ W : PolarPoint → ℝ, ContDiff ℝ ∞ W →
      h x * divergenceOperator A (fun y => h y * W (F y)) x /
          |planeJacobian F x| =
        divergenceOperator B W (F x) + V * W (F x))
    (ℓ : PolarPoint →L[ℝ] ℝ) :
    coefficientQuadratic B (F x) (ℓ (1, 0), ℓ (0, 1)) =
      h x ^ 2 / |planeJacobian F x| *
        coefficientQuadratic A x
          (ℓ (fderiv ℝ F x (1, 0)), ℓ (fderiv ℝ F x (0, 1))) := by
  have hf : ContDiffAt ℝ 2 (fun y => ℓ (F y) - ℓ (F x)) x :=
    (ℓ.contDiff.contDiffAt.comp x hF).sub contDiffAt_const
  have hf' : HasFDerivAt (fun y => ℓ (F y) - ℓ (F x))
      (ℓ.comp (fderiv ℝ F x)) x :=
    (ℓ.hasFDerivAt.comp x
      (hF.differentiableAt (by norm_num)).hasFDerivAt).sub_const _
  have hg : ContDiffAt ℝ 2 (fun y => ℓ y - ℓ (F x)) (F x) :=
    ℓ.contDiff.contDiffAt.sub contDiffAt_const
  have hg' : HasFDerivAt (fun y => ℓ y - ℓ (F x)) ℓ (F x) :=
    ℓ.hasFDerivAt.sub_const _
  have hs := divergenceOperator_mul_sq_of_zero ha hb hc hh hf (sub_self _)
  have ht := divergenceOperator_sq_of_zero hBa hBb hBc hg (sub_self _)
  simp only [radialPartial, angularPartial, hf'.fderiv,
    ContinuousLinearMap.comp_apply] at hs
  simp only [radialPartial, angularPartial, hg'.fderiv] at ht
  have hW : ContDiff ℝ ∞ (fun y => (ℓ y - ℓ (F x)) ^ 2) :=
    (ℓ.contDiff.sub contDiff_const).pow 2
  have he := hid (fun y => (ℓ y - ℓ (F x)) ^ 2) hW
  rw [hs, ht] at he
  simp only [sub_self, zero_pow two_ne_zero, mul_zero, add_zero] at he
  calc
    _ = (h x * (2 * h x *
        coefficientQuadratic A x
          (ℓ (fderiv ℝ F x (1, 0)), ℓ (fderiv ℝ F x (0, 1)))) /
            |planeJacobian F x|) / 2 := by linarith [he]
    _ = _ := by ring

/-- The physical-point expression of the canonical principal coefficients.
Composition with the inverse chart gives the canonical coefficient fields. -/
def coordinatePrincipalDensity (A : SymmetricCoefficients)
    (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) : SymmetricCoefficients where
  a x := h x ^ 2 / |planeJacobian F x| *
    coefficientQuadratic A x
      ((fderiv ℝ F x (1, 0)).1, (fderiv ℝ F x (0, 1)).1)
  b x := h x ^ 2 / |planeJacobian F x| *
    (A.a x * (fderiv ℝ F x (1, 0)).1 * (fderiv ℝ F x (1, 0)).2 +
      A.b x * ((fderiv ℝ F x (1, 0)).1 * (fderiv ℝ F x (0, 1)).2 +
        (fderiv ℝ F x (0, 1)).1 * (fderiv ℝ F x (1, 0)).2) +
      A.c x * (fderiv ℝ F x (0, 1)).1 * (fderiv ℝ F x (0, 1)).2)
  c x := h x ^ 2 / |planeJacobian F x| *
    coefficientQuadratic A x
      ((fderiv ℝ F x (1, 0)).2, (fderiv ℝ F x (0, 1)).2)

/-- Three actual quadratic probes recover every entry of the principal
matrix, including the mixed entry by polarization. -/
theorem principalCoefficients_of_operator_identity
    {A B : SymmetricCoefficients} {F : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {x : PolarPoint} {V : ℝ}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x)
    (hF : ContDiffAt ℝ 2 F x) (hh : ContDiffAt ℝ 2 h x)
    (hBa : DifferentiableAt ℝ B.a (F x))
    (hBb : DifferentiableAt ℝ B.b (F x))
    (hBc : DifferentiableAt ℝ B.c (F x))
    (hid : ∀ W : PolarPoint → ℝ, ContDiff ℝ ∞ W →
      h x * divergenceOperator A (fun y => h y * W (F y)) x /
          |planeJacobian F x| =
        divergenceOperator B W (F x) + V * W (F x)) :
    B.a (F x) = (coordinatePrincipalDensity A F h).a x ∧
      B.b (F x) = (coordinatePrincipalDensity A F h).b x ∧
      B.c (F x) = (coordinatePrincipalDensity A F h).c x := by
  have hq := principalQuadratic_of_operator_identity ha hb hc hF hh hBa hBb hBc hid
  have hqa : B.a (F x) = (coordinatePrincipalDensity A F h).a x := by
    simpa [coefficientQuadratic, coordinatePrincipalDensity] using
      hq (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hqc : B.c (F x) = (coordinatePrincipalDensity A F h).c x := by
    simpa [coefficientQuadratic, coordinatePrincipalDensity] using
      hq (ContinuousLinearMap.snd ℝ ℝ ℝ)
  refine ⟨hqa, ?_, hqc⟩
  have hsum := hq (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
  simp only [coefficientQuadratic, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.fst_apply, ContinuousLinearMap.snd_apply,
    zero_add, add_zero, one_pow, mul_one] at hsum
  rw [hqa, hqc] at hsum
  dsimp only [coordinatePrincipalDensity, coefficientQuadratic] at hsum ⊢
  linear_combination hsum / 2

end ContinuousFlexibility.Analysis
