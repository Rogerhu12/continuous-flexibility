import ContinuousFlexibility.Analysis.CircleModelRealization

/-!
# Realizing bilinear operators in the supplied circle model

A bilinear family of actual weighted fields lifts through the injective
decoder.  Linearity is proved from the physical decoder identities in both
arguments, so the result lives in the supplied model without a new space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

section BilinearLift

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {T : MaterialData} {γ : ℝ} {S : CircleModelData}

/-- Lift an actual bilinear field through the supplied physical decoder. -/
def liftCircleBilinear (hS : IsCircleModel T γ S)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] (ℕ → ℝ → ℝ))
    (hB : ∀ x y, CircleMember T γ (B x y)) :
    E →ₗ[ℝ] F →ₗ[ℝ] S.Space where
  toFun x := liftCircleLinear hS (B x) (hB x)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    apply hS.2.2.2.2.2.1
    simp only [LinearMap.add_apply, map_add, liftCircleLinear_decode]
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    apply hS.2.2.2.2.2.1
    simp only [LinearMap.smul_apply, map_smul, liftCircleLinear_decode,
      RingHom.id_apply]

theorem liftCircleBilinear_decode (hS : IsCircleModel T γ S)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] (ℕ → ℝ → ℝ))
    (hB : ∀ x y, CircleMember T γ (B x y)) (x : E) (y : F) :
    S.decode (liftCircleBilinear hS B hB x y) = B x y :=
  liftCircleLinear_decode hS (B x) (hB x) y

end BilinearLift

end ContinuousFlexibility.Statements
